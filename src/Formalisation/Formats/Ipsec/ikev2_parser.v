From Formalisation Require Import ikev2_notify ikev2_transforms ikev2 Nom SizeNat .
From Formalisation Require Import bin_combinators combinator multi.

Open Scope N_scope.

Program Definition shift_right {len} (n : natN len) (s : N) : natN len :=
  mk_natN len (N.div (val n) (2 ^ s)) _.
Next Obligation.
  intros. destruct n as [n Pn]. simpl. eapply N.le_lt_trans. 2 : eapply Pn.
  rewrite <- N.div_1_r. apply N.div_le_compat_l. split. lia.
  destruct s; simpl; lia.
Qed.

Notation "n >> s" := (shift_right n s)(at level 20).

Program Definition preserve_s_low {len} (n : natN len) (s : N) : natN len :=
  mk_natN len (N.modulo (val n) (2 ^ s)) _.
Next Obligation.
  intros. destruct n as [n Pn]. simpl. eapply N.le_lt_trans. 2 : eapply Pn.
  apply N.mod_le. destruct s; simpl; lia.
Qed.

Notation "n & s" := (preserve_s_low n s)(at level 20).

Definition parse_ikev2_header : NomG IkeV2Header :=
  let! len := length in
  if len <? 28
  then
    fail
  else
    let! init_spi := be_u64 in
    let! resp_spi := be_u64 in
    let! next_payload := map be_u8 mk_payload_type in
    let! vers := be_u8 in
    let maj_ver : nat8 := vers >> 4 in
    let min_ver := vers & 4 in
    let! exch_type := map be_u8 mk_exc in
    let! flags := be_u8 in
    let! msg_id := be_u32 in
    let! length := be_u32 in
    ret (mk_header
           span
           init_spi
           resp_spi
           next_payload
           maj_ver
           min_ver
           exch_type
           flags
           msg_id
           length).

Definition parse_ikev2_payload_generic : NomG IkeV2GenericPayload :=
  let! next_payload_type := map be_u8 mk_payload_type in
  let! b := be_u8 in
  let b1 := b >> 7 in
  let b2 := b & 7 in
  let! payload_length := verify be_u16 (fun n => 4 <=? val n) in
  let! payload := take (val payload_length - 4) in
  let hdr := mk_payloadheader
               next_payload_type
               (val b1 =? 1)
               b2
               payload_length in
  ret (mk_genericpayload span hdr payload).

Definition parse_ikev2_transform : NomG IkeV2RawTransform :=
  let! last := be_u8 in
  let! reserved1 := be_u8 in
  let! transform_length := be_u16 in
  let! transform_type := be_u8 in
  let! reserved2 := be_u8 in
  let! transform_id := be_u16 in
  let! attributes := cond (8 <? val transform_length) (take (val transform_length - 8)) in
  ret (mk_raw span
              last
              reserved1
              transform_length
              (mk_transform transform_type)
              reserved2
              transform_id
              attributes).

Definition parse_ikev2_proposal : NomG IkeV2Proposal :=
  let! len := length in
  if len <? 8
  then
    fail
  else
    let! last := be_u8 in
    let! reserved := be_u8 in
    let! proposal_length := be_u16 in
    let! proposal_num := be_u8 in
    let! protocol_id := map be_u8 mk_prot in
    let! spi_size := be_u8 in
    let! num_transforms := be_u8 in
    let! spi := cond (0 <? val spi_size) (take (val spi_size)) in
    if val proposal_length <? (8 + val spi_size)
    then
      fail
    else
      let! transforms := map_parser
                           (take (val proposal_length - 8 - (val spi_size)))
                           (count (val num_transforms) parse_ikev2_transform) in
      ret (mk_proposal span
                       last
                       reserved
                       proposal_length
                       proposal_num
                       protocol_id
                       spi_size
                       num_transforms
                       spi
                       transforms).

Definition parse_ikev2_payload_sa (_ : nat16) : NomG IkeV2PayloadContent :=
  map (many1 parse_ikev2_proposal) SA.

Definition parse_ikev2_payload_kex (length : nat16) : NomG IkeV2PayloadContent :=
  if val length <? 4
  then
    fail
  else
    let! dh_group := map be_u16 mk_transformdh in
    let! reserved := be_u16 in
    let! kex_data := take (val length - 4) in
    let payload := mk_ExcPayload span dh_group reserved kex_data in
    ret (KE payload).

Definition parse_ikev2_payload_ident_init (length : nat16) : NomG IkeV2PayloadContent :=
  if val length <? 4
  then
    fail
  else
    let! id_type := map be_u8 mk_ident in
    let! reserved1 := be_u8 in
    let! reserved2 := be_u16 in
    let! ident_data := take (val length - 4) in
    let payload := mk_IdPayload span id_type reserved1 reserved2 ident_data in
    ret (IDi payload).

Definition parse_ikev2_payload_ident_resp (length : nat16) : NomG IkeV2PayloadContent :=
  if val length <? 4
  then
    fail
  else
    let! id_type := map be_u8 mk_ident in
    let! reserved1 := be_u8 in
    let! reserved2 := be_u16 in
    let! ident_data := take (val length - 4) in
    let payload := mk_IdPayload _ id_type reserved1 reserved2 ident_data in
    ret (IDr payload).

Definition parse_ikev2_payload_certificate (length : nat16) : NomG IkeV2PayloadContent :=
  if val length <? 1
  then
    fail
  else
    let! cert_encoding := map be_u8 mk_certEnc in
    let! cert_data := take (val length - 1) in
    let payload := mk_certiPayload _ cert_encoding cert_data in
    ret (CertificatePC payload).

Definition parse_ikev2_payload_certificate_request (length : nat16) : NomG IkeV2PayloadContent :=
  if val length <? 1
  then
    fail
  else
    let! cert_encoding := map be_u8 mk_certEnc in
    let! ca_data := take (val length - 1) in
    let payload := mk_certReqPayload _ cert_encoding ca_data in
    ret (CertificateRequestPC payload).

Definition parse_ikev2_payload_authentication (length : nat16) : NomG IkeV2PayloadContent :=
  if val length <? 4
  then
    fail
  else
    let! auth_method := map be_u8 mk_authMethod in
    let! auth_data := take (val length - 4) in
    let payload := mk_authPayload auth_method auth_data in
    ret (AuthenticationPC payload).

Definition parse_ikev2_payload_nonce (length : nat16) : NomB IkeV2PayloadContent :=
  let! nonce_data := take (val length) in
  ret (NoncePC (mk_noncePayload nonce_data)).

Definition parse_ikev2_payload_notify (length : nat16) : NomG IkeV2PayloadContent :=
  let! protocol_id := map be_u8 mk_prot in
  let! spi_size := be_u8 in
  let! notify_type := map be_u16 mk_notify in
  let! spi := cond (0 <? val spi_size) (take (val spi_size)) in
  let! notify_data := cond (8 + val spi_size <? val length) (take (val length - (8 + val spi_size))) in
  let payload := mk_notifyPayload protocol_id spi_size notify_type spi notify_data in
  ret (NotifyPC payload).

Definition parse_ikev2_payload_vendor_id (length : nat16) : NomB IkeV2PayloadContent :=
  if val length <? 8
  then
    fail
  else
    let! vendor_id := take (val length - 8) in
    ret (VendorIDPC (mk_vendorIdPayload vendor_id)).

Definition parse_ikev2_payload_delete (length : nat16) : NomG IkeV2PayloadContent :=
  if val length <? 8
  then
    fail
  else
    let! protocol_id := map be_u8 mk_prot in
    let! spi_size := be_u8 in
    let! num_spi := be_u16 in
    let! spi := take (val length - 8) in
    let payload := mk_deletePayload protocol_id spi_size num_spi spi in
    ret (DeletePC payload).

Definition parse_ts_addr (t : TSType) : NomB span :=
  match val (val_ts t) with
  | 7 => take 4
  | 8 => take 16
  | _ => fail
  end.

Definition parse_ikev2_ts : NomB TrafficSelector :=
  let! ts_type := map be_u8 mk_tstype in
  let! ip_proto_id := be_u8 in
  let! sel_length := be_u16 in
  let! start_port := be_u16 in
  let! end_port := be_u16 in
  let! start_addr := parse_ts_addr ts_type in
  let! end_addr := parse_ts_addr ts_type in
  ret (mk_trafficSelec
         ts_type
         ip_proto_id
         sel_length
         start_port
         end_port
         start_addr
         end_addr).

Definition parse_ikev2_payload_ts (length : nat16) : NomB TrafficSelectorPayload :=
  if val length <? 4
  then
    fail
  else
    let! num_ts := be_u8 in
    let! reserved := take 3 in
    let! ts := map_parser (take (val length - 4)) (many1 parse_ikev2_ts) in
    ret (mk_tsp num_ts reserved ts).

Definition parse_ikev2_payload_ts_init (length : nat16) : NomB IkeV2PayloadContent :=
  map (parse_ikev2_payload_ts length) TSi.

Definition parse_ikev2_payload_ts_resp (length : nat16) : NomB IkeV2PayloadContent :=
  map (parse_ikev2_payload_ts length) TSr.

Definition parse_ikev2_payload_encrypted (length : nat16) : NomB IkeV2PayloadContent :=
  map (take (val length)) (fun v => Encrypted (mk_EncPay _ v)).

Definition parse_ikev2_payload_unknown (length : nat16) : NomB IkeV2PayloadContent :=
  map (take (val length)) Unknown.

Definition parse_ikev2_payload_with_type (length : nat16)
           (next_payload_type : IkePayloadType) : NomB IkeV2PayloadContent :=
  map_parser (take (val length)) (match val (valpayload next_payload_type) with
                                  | 33 => parse_ikev2_payload_sa length
                                  | 34 => parse_ikev2_payload_kex length
                                  | 35 => parse_ikev2_payload_ident_init length
                                  | 36 => parse_ikev2_payload_ident_resp length
                                  | 37 => parse_ikev2_payload_certificate length
                                  | 38 => parse_ikev2_payload_certificate_request length
                                  | 39 => parse_ikev2_payload_authentication length
                                  | 40 => parse_ikev2_payload_nonce length
                                  | 41 => parse_ikev2_payload_notify length
                                  | 42 => parse_ikev2_payload_delete length
                                  | 43 => parse_ikev2_payload_vendor_id length
                                  | 44 => parse_ikev2_payload_ts_init length
                                  | 45 => parse_ikev2_payload_ts_resp length
                                  | 46 => parse_ikev2_payload_encrypted length
                                  | _ => parse_ikev2_payload_unknown length
                                  end).

Equations parse_ikev2_payload_list_fold (v : VECTOR IkeV2Payload)
          (p : IkeV2GenericPayload) : NomB (VECTOR IkeV2Payload) :=
  parse_ikev2_payload_list_fold v p :=
    if Vector.size (`v) =? 0
    then fail
    else
      match Vector.get v (Vector.size (`v) - 1) with
      | Datatypes.None => fail
      | Some last_payload =>
          if val (payload_length (hdrGen p)) <? 4
          then
            fail
          else
            scope
              (payloadGen p)
              (let! p2 := parse_ikev2_payload_with_type
                            (_16 (val (payload_length (hdrGen p)) - 4))
                            (next_payload_type (hdr last_payload)) in
               let! rem := length in
               if rem =? 0
               then ret (Vector.add v (mk_payload (hdrGen p) p2))
               else fail)
      end.
Next Obligation.
  intros. destruct (payload_length (hdrGen p)). simpl.
  eapply N.le_lt_trans. 2 : eapply len_correct. lia.
Qed.

#[tactic="NSize"]Equations parse_ikev2_payload_list (initial_type : IkePayloadType)
  : NomB (VECTOR IkeV2Payload) :=
  parse_ikev2_payload_list initial_type :=
    let acc := Vector.make IkeV2Payload 2 in
    let acc := Vector.add acc (mk_payload
                                (mk_payloadheader initial_type false (_8 0) (_16 0))
                                Dummy) in
    repeat Datatypes.None (fun acc =>
                             let! len := length in
                             if len =? 0
                             then fail
                             else
                               let! p := parse_ikev2_payload_generic in
                               parse_ikev2_payload_list_fold acc p) acc.

Definition parse_ikev2_message : NomB IkeV2Message :=
  let! hdr := parse_ikev2_header in
  let len := val (ikev2.length hdr) in
  if len <? 28
  then
    fail
  else
    let! msg := map_parser (take (len - 28)) (parse_ikev2_payload_list (next_payload hdr)) in
    ret (mk_message _ hdr msg).

#[tactic="NSize"] Equations IKEV2_INIT_REQ : list nat8 :=
  IKEV2_INIT_REQ :=
  [
    (_8 1); (_8 248); (_8 195); (_8 212); (_8 187); (_8 119); (_8 63); (_8 47); (_8 0); (_8 0); (_8 0); (_8 0); (_8 0); (_8 0); (_8 0); (_8 0);
    (_8 33); (_8 32); (_8 34); (_8 8); (_8 0); (_8 0); (_8 0); (_8 0); (_8 0); (_8 0); (_8 1); (_8 72); (_8 34); (_8 0); (_8 0); (_8 48);
    (_8 0); (_8 0); (_8 0); (_8 44); (_8 1); (_8 1); (_8 0); (_8 4); (_8 3); (_8 0); (_8 0); (_8 12); (_8 1); (_8 0); (_8 0); (_8 20);
    (_8 128); (_8 14); (_8 0); (_8 128); (_8 3); (_8 0); (_8 0); (_8 8); (_8 3); (_8 0); (_8 0); (_8 12); (_8 3); (_8 0); (_8 0); (_8 8);
    (_8 2); (_8 0); (_8 0); (_8 5); (_8 0); (_8 0); (_8 0); (_8 8); (_8 4); (_8 0); (_8 0); (_8 30); (_8 40); (_8 0); (_8 0); (_8 136);
    (_8 0); (_8 30); (_8 0); (_8 0); (_8 143); (_8 230); (_8 243); (_8 110); (_8 136); (_8 123); (_8 24); (_8 155); (_8 94); (_8 206); (_8 242); (_8 86);
    (_8 249); (_8 141); (_8 118); (_8 170); (_8 203); (_8 7); (_8 179); (_8 185); (_8 88); (_8 238); (_8 115); (_8 234); (_8 123); (_8 115); (_8 177); (_8 4);
    (_8 126); (_8 164); (_8 42); (_8 78); (_8 68); (_8 31); (_8 185); (_8 62); (_8 249); (_8 169); (_8 171); (_8 12); (_8 84); (_8 90); (_8 167); (_8 70);
    (_8 46); (_8 88); (_8 60); (_8 6); (_8 178); (_8 237); (_8 145); (_8 141); (_8 17); (_8 202); (_8 103); (_8 219); (_8 33); (_8 107); (_8 184); (_8 173);
    (_8 191); (_8 87); (_8 63); (_8 186); (_8 90); (_8 166); (_8 125); (_8 73); (_8 131); (_8 75); (_8 169); (_8 147); (_8 111); (_8 76); (_8 233); (_8 102);
    (_8 205); (_8 87); (_8 92); (_8 186); (_8 7); (_8 66); (_8 250); (_8 11); (_8 232); (_8 185); (_8 208); (_8 37); (_8 196); (_8 185); (_8 223); (_8 41);
    (_8 215); (_8 228); (_8 110); (_8 214); (_8 84); (_8 120); (_8 170); (_8 149); (_8 2); (_8 191); (_8 37); (_8 85); (_8 113); (_8 250); (_8 158); (_8 203);
    (_8 5); (_8 234); (_8 143); (_8 123); (_8 20); (_8 14); (_8 29); (_8 223); (_8 180); (_8 3); (_8 95); (_8 45); (_8 33); (_8 102); (_8 88); (_8 110);
    (_8 66); (_8 114); (_8 50); (_8 3); (_8 41); (_8 0); (_8 0); (_8 36); (_8 227); (_8 59); (_8 82); (_8 170); (_8 111); (_8 109); (_8 98); (_8 135);
    (_8 22); (_8 215); (_8 171); (_8 198); (_8 69); (_8 166); (_8 204); (_8 151); (_8 7); (_8 67); (_8 61); (_8 133); (_8 131); (_8 222); (_8 171); (_8 151);
    (_8 219); (_8 191); (_8 8); (_8 206); (_8 15); (_8 173); (_8 89); (_8 113); (_8 41); (_8 0); (_8 0); (_8 28); (_8 0); (_8 0); (_8 64); (_8 4);
    (_8 204); (_8 192); (_8 100); (_8 92); (_8 30); (_8 235); (_8 194); (_8 29); (_8 9); (_8 43); (_8 240); (_8 127); (_8 202); (_8 52); (_8 195); (_8 230);
    (_8 43); (_8 32); (_8 236); (_8 143); (_8 41); (_8 0); (_8 0); (_8 28); (_8 0); (_8 0); (_8 64); (_8 5); (_8 21); (_8 57); (_8 117); (_8 119);
    (_8 245); (_8 84); (_8 135); (_8 163); (_8 143); (_8 216); (_8 175); (_8 112); (_8 176); (_8 156); (_8 32); (_8 156); (_8 255); (_8 74); (_8 55); (_8 209);
    (_8 41); (_8 0); (_8 0); (_8 16); (_8 0); (_8 0); (_8 64); (_8 47); (_8 0); (_8 1); (_8 0); (_8 2); (_8 0); (_8 3); (_8 0); (_8 4);
    (_8 0); (_8 0); (_8 0); (_8 8); (_8 0); (_8 0); (_8 64); (_8 22)
  ].

Definition test_ikev2_init_req := run 57 parse_ikev2_header IKEV2_INIT_REQ (mk_span 0 28).
Compute (test_ikev2_init_req). (* OK *)

#[tactic="NSize"] Equations IKEV2_PAYLOAD_SA : list nat8 :=
  IKEV2_PAYLOAD_SA :=
  [
    (_8 34); (_8 0); (_8 0); (_8 40); (_8 0); (_8 0); (_8 0); (_8 36); (_8 1); (_8 1); (_8 0); (_8 3); (_8 3); (_8 0); (_8 0); (_8 12);
    (_8 1); (_8 0); (_8 0); (_8 20); (_8 128); (_8 14); (_8 0); (_8 128); (_8 3); (_8 0); (_8 0); (_8 8); (_8 2); (_8 0); (_8 0); (_8 5);
    (_8 0); (_8 0); (_8 0); (_8 8); (_8 4); (_8 0); (_8 0); (_8 30)
  ].

Definition test_ikev2_payload_sa :=
  run 9 parse_ikev2_payload_generic IKEV2_PAYLOAD_SA (mk_span 0 (N.of_nat (List.length IKEV2_PAYLOAD_SA))).
Compute (test_ikev2_payload_sa). (* OK *)

Program Definition test_ikev2_payload_sa_suite : Result (span * IkeV2PayloadContent) :=
  match test_ikev2_payload_sa with
  | NoRes | NoFuel => NoRes
  | Res (_, res) =>
      let attrs1 := [(_8 128); (_8 14); (_8 0); (_8 128)] in
      run 100 (@parse_ikev2_payload_sa (_16 0)) IKEV2_PAYLOAD_SA (payloadGen res)
  end.
Next Obligation.
  NSize.
Qed.
Next Obligation.
  NSize.
Qed.
Next Obligation.
  NSize.
Qed.
Next Obligation.
  NSize.
Qed.
Next Obligation.
  intros. simpl. lia.
Qed.

Compute (test_ikev2_payload_sa_suite). (* OK *)

Program Definition test_ikev2_parse_payload_many :=
  run 100 (@parse_ikev2_payload_list (mk_payload_type (_8 33))) IKEV2_INIT_REQ
    (mk_span 28 (N.of_nat (List.length IKEV2_INIT_REQ) - 28)).
Next Obligation.
  NSize.
Qed.

Compute (test_ikev2_parse_payload_many). (* A verifier mais semble OK *)

Compute (run 1000 parse_ikev2_message
             IKEV2_INIT_REQ
             (mk_span 0 (N.of_nat (List.length IKEV2_INIT_REQ)))).
