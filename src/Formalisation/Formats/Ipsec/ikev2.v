From Formalisation Require Import ikev2_transforms ikev2_notify.
From Formalisation Require Import Nom IpAddr.

Open Scope N_scope.

Record IkeExchangeType := mk_exc { valexc : nat8 }.

Record ProtocolID := mk_prot { valprot : nat8 }.

Record IkePayloadType := mk_payload_type { valpayload : nat8 }.

Record IkeV2HeaderS {S : Type} :=
  mk_header {
      init_spi : nat64;
      resp_spi : nat64;
      next_payload : IkePayloadType;
      maj_ver : nat8;
      min_ver : nat8;
      exch_type : IkeExchangeType;
      flags : nat8;
      msg_id : nat32;
      length : nat32
    }.

Definition IkeV2Header := @IkeV2HeaderS span.

Global Instance Foldable_IkeV2HeaderS : Foldable (@IkeV2HeaderS) :=
  Build_Foldable _ (fun _ _ _ b _ => b) (fun _ _ _ _ _ _ => Monoid.mempty).

Record IkeV2PayloadHeaderS {S : Type} :=
  mk_payloadheader {
      next_payload_type : IkePayloadType;
      critical : bool;
      reservedPH : nat8;
      payload_length : nat16
    }.

Arguments mk_payloadheader [S].

Definition IkeV2PayloadHeader := @IkeV2PayloadHeaderS span.

Global Instance Foldable_IkeV2PayloadHeader : Foldable (@IkeV2PayloadHeaderS) :=
  Build_Foldable _ (fun _ _ _ b _ => b) (fun _ _ _ _ _ _ => Monoid.mempty).


Record IkeV2GenericPayloadS {S : Type} :=
  mk_genericpayload {
      hdrGen : IkeV2PayloadHeader;
      payloadGen : S
    }.

Definition IkeV2GenericPayload := @IkeV2GenericPayloadS span.

Definition foldr_genpay A B (f : A -> B -> B) (b : B) ta : B := f (payloadGen ta) b.
Definition foldMap_genpay M `(Monoid.Monoid M) {A} (f : A -> M) ta : M := f (payloadGen ta).

Global Instance Foldable_IkeV2GenericPayload : Foldable (@IkeV2GenericPayloadS) :=
  Build_Foldable _ (foldr_genpay) foldMap_genpay.

Record IkeV2ProposalS {S} :=
  mk_proposal {
      last : nat8;
      reservedProposal : nat8;
      proposal_length : nat16;
      proposal_num : nat8;
      protocol_id : ProtocolID;
      spi_size : nat8;
      num_transforms : nat8;
      spi : option S;
      transforms : VECTOR (@IkeV2RawTransformS S)
    }.

Definition IkeV2Proposal := @IkeV2ProposalS span.

Definition foldr_propo A B (f : A -> B -> B) (b : B) ta : B :=
  let b := match spi ta with
           | Some v => f v b
           | None => b
           end in
  let s := List.fold_right (fun a l => foldMap (list A) _ (fun v => [v]) (snd a) ++ l)
                             [] (values (proj1_sig (transforms ta))) in
  List.fold_right f b s.

Definition foldMap_propo M `(Monoid.Monoid M) {A} (f : A -> M) ta : M :=
  foldr_propo _ _ (fun a b => Monoid.f (f a) b) Monoid.mempty ta.

Global Instance Foldable_IkeV2Proposal : Foldable (@IkeV2ProposalS) :=
  Build_Foldable _ (foldr_propo) foldMap_propo.

Record KeyExchangePayloadS {S : Type} :=
  mk_ExcPayload {
      dh_group : IkeTransformDHType;
      reserved : nat16;
      kex_data : S
    }.

Definition KeyExchangePayload := @KeyExchangePayloadS span.

Global Instance Foldable_KeyExchangePayload : Foldable (@KeyExchangePayloadS) :=
  Build_Foldable _ (fun _ _ f b a => f (kex_data a) b) (fun _ _ _ _ f a => f (kex_data a)).

Record IdentificationType := mk_ident { ident : nat8 }.

Record IdentificationPayloadS {S : Type} :=
  mk_IdPayload {
      id_type : IdentificationType;
      reserved1 : nat8;
      reserved2 : nat16;
      ident_data : S
    }.

Definition IdentificationPayload := @IdentificationPayloadS span.

Global Instance Foldable_IdentificationPayload : Foldable (@IdentificationPayloadS) :=
  Build_Foldable _ (fun _ _ f b a => f (ident_data a) b) (fun _ _ _ _ f a => f (ident_data a)).

Record CertificateEncoding := mk_certEnc { val_certEnc : nat8 }.

Record CertificatePayloadS {S : Type} :=
  mk_certiPayload {
      cert_encoding : CertificateEncoding;
      cert_data : S
    }.

Definition CertificatePayload := @CertificatePayloadS span.

Global Instance Foldable_CertificatePayload : Foldable (@CertificatePayloadS) :=
  Build_Foldable _ (fun _ _ f b a => f (cert_data a) b) (fun _ _ _ _ f a => f (cert_data a)).

Record CertificateRequestPayloadS {S : Type} :=
  mk_certReqPayload {
      cert_encodingREq : CertificateEncoding;
      ca_dataReq : S
    }.

Definition CertificateRequestPayload := @CertificateRequestPayloadS span.

Global Instance Foldable_CertificateRequestPayload : Foldable (@CertificateRequestPayloadS) :=
  Build_Foldable _ (fun _ _ f b a => f (ca_dataReq a) b) (fun _ _ _ _ f a => f (ca_dataReq a)).

Record AuthenticationMethod :=
  mk_authMethod {
      val_authMethod : nat8;
      is_unassigned : bool :=
        let v := val val_authMethod in
        ((4 <=? v) && (v <=? 8)) || ((15 <=? v) && (v <=? 200));
      is_private_use : bool :=
        201 <=? val val_authMethod
    }.

Record AuthenticationPayloadS {S : Type} :=
  mk_authPayload {
      auth_method : AuthenticationMethod;
      auth_data : S
    }.

Arguments mk_authPayload [S].

Definition AuthenticationPayload := @AuthenticationPayloadS span.

Global Instance Foldable_AuthenticationPayload : Foldable (@AuthenticationPayloadS) :=
  Build_Foldable _ (fun _ _ f b a => f (auth_data a) b) (fun _ _ _ _ f a => f (auth_data a)).

Record NoncePayloadS {S : Type} :=
  mk_noncePayload {
      nonce_data : S
    }.

Arguments mk_noncePayload [S].

Definition NoncePayload := @NoncePayloadS span.

Global Instance Foldable_NoncePayload : Foldable (@NoncePayloadS) :=
  Build_Foldable _ (fun _ _ f b a => f (nonce_data a) b) (fun _ _ _ _ f a => f (nonce_data a)).

Record NotifyPayloadS {S : Type} :=
  mk_notifyPayload {
      protocol_idNoti : ProtocolID;
      spi_sizeNoti : nat8;
      notify_type : NotifyType;
      num_spi : option S;
      spiNoti : option S
    }.

Arguments mk_notifyPayload [S].

Definition NotifyPayload := @NotifyPayloadS span.

Definition foldr_notifypay := fun A B (f : A -> B -> B) b a =>
                                match spiNoti a with
                                | Some s0 => f s0
                                | None => fun v => v
                                end (match num_spi a with
                                     | Some s0 => f s0 b
                                     | None => b
                                     end).

Definition foldmap_notify M `(Monoid.Monoid M) {A} (f : A -> M) ta : M :=
  foldr_notifypay _ _ (fun a b => Monoid.f (f a) b) Monoid.mempty ta.

Global Instance Foldable_NotifyPayload : Foldable (@NotifyPayloadS) :=
  Build_Foldable _ foldr_notifypay foldmap_notify.


Record DeletePayloadS {S : Type} :=
  mk_deletePayload {
      protocol_idDel : ProtocolID;
      spi_sizeDel : nat8;
      num_spiDel : nat16;
      spiDel : S
    }.

Arguments mk_deletePayload [S].

Definition DeletePayload := @DeletePayloadS span.

Global Instance Foldable_DeletePayload : Foldable (@DeletePayloadS) :=
  Build_Foldable _ (fun _ _ f b a => f (spiDel a) b) (fun _ _ _ _ f a => f (spiDel a)).

Record VendorIDPayloadS {S : Type} :=
  mk_vendorIdPayload {
      vendor_id : S
    }.

Arguments mk_vendorIdPayload [S].

Definition VendorIDPayload := @VendorIDPayloadS span.

Global Instance Foldable_VendorIDPayload : Foldable (@VendorIDPayloadS) :=
  Build_Foldable _ (fun _ _ f b a => f (vendor_id a) b) (fun _ _ _ _ f a => f (vendor_id a)).

Record TSType := mk_tstype { val_ts : nat8 }.

Record TrafficSelectorS {S} :=
  mk_trafficSelec {
      ts_type : TSType;
      ip_proto_id : nat8;
      sel_length : nat16;
      start_port : nat16;
      end_port : nat16;
      start_addr : S;
      end_addr : S
    }.

Arguments mk_trafficSelec [S].

Definition TrafficSelector := @TrafficSelectorS span.

Global Instance Foldable_TrafficSelector : Foldable (@TrafficSelectorS) :=
  Build_Foldable _ (fun _ _ f b a => f (start_addr a) (f (end_addr a) b))
                 (fun _ _ _ _ f a =>  Monoid.f (f (start_addr a)) (f (end_addr a))).

Definition ipv4_from_slice (s : span) : NomG Ipv4 :=
  let! a4 := read s 0 in
  let! b4 := read s 1 in
  let! c4 := read s 2 in
  let! d4 := read s 3 in
  ret (mk_ipv4 a4 b4 c4 d4).

(* TODO : Embellir *)
Definition ipv6_from_slice (s : span) : NomG Ipv6 :=
  let! a06 := @read nat8 s 0 in
  let! a16 := read s 1 in
  let! b06 := @read nat8 s 2 in
  let! b16 := read s 3 in
  let! c06 := @read nat8 s 4 in
  let! c16 := read s 5 in
  let! d06 := @read nat8  s 6 in
  let! d16 := read s 7 in
  let! e06 := @read nat8  s 8 in
  let! e16 := read s 9 in
  let! f06 := @read nat8 s 10 in
  let! f16 := read s 11 in
  let! g06 := @read nat8 s 12 in
  let! g16 := read s 13 in
  let! h06 := @read nat8 s 14 in
  let! h16 := read s 15 in
  ret (mk_ipv6 (a06 ↑ a16) (b06 ↑ b16) (c06 ↑ c16) (d06 ↑ d16)
               (e06 ↑ e16) (f06 ↑ f16) (g06 ↑ g16) (h06 ↑ h16)).

Definition get_ts_type (v : TrafficSelector) : TSType := ts_type v.

Definition get_start_addr (v : TrafficSelector) : NomG (option IpAddr) :=
  match val (val_ts (ts_type v)) with
  | 7 => let! ipv4 := ipv4_from_slice (start_addr v) in
        ret (Some (V4 ipv4))
  | 8 => let! ipv6 := ipv6_from_slice (start_addr v) in
        ret (Some (V6 ipv6))
  | _ => ret Datatypes.None
  end.


Definition get_end_addr (v : TrafficSelector) : NomG (option IpAddr) :=
  match val (val_ts (ts_type v)) with
  | 7 => let! ipv4 := ipv4_from_slice (end_addr v) in
        ret (Some (V4 ipv4))
  | 8 => let! ipv6 := ipv6_from_slice (end_addr v) in
        ret (Some (V6 ipv6))
  | _ => ret Datatypes.None
  end.

Record TrafficSelectorPayloadS {S} :=
  mk_tsp {
      num_ts : nat8;
      reserved_tsp : S;
      ts : VECTOR (@TrafficSelectorS S)
    }.

Arguments mk_tsp [S].

Definition TrafficSelectorPayload := @TrafficSelectorPayloadS span.

Definition foldr_trafficselectorpay A B (f : A -> B -> B) b a :=
  let ts_list := List.fold_right f b (List.fold_right (fun a l => foldMap (list A) _ (fun v => [v]) (snd a) ++ l) [] (Vector.values (proj1_sig (ts a)))) in
  f (reserved_tsp a) ts_list.


Definition foldmap_trafficselectorpay M `(Monoid.Monoid M) {A} (f : A -> M) ta : M :=
  foldr_trafficselectorpay _ _ (fun a b => Monoid.f (f a) b) Monoid.mempty ta.


Global Instance Foldable_TrafficSelectorPayload : Foldable (@TrafficSelectorPayloadS) :=
  Build_Foldable _ foldr_trafficselectorpay foldmap_trafficselectorpay.

Record EncryptedPayloadS {S} := mk_EncPay { spanEncPay : S }.

Definition EncryptedPayload := @EncryptedPayloadS span.

Global Instance Foldable_EncryptedPayload : Foldable (@EncryptedPayloadS) :=
  Build_Foldable _ (fun _ _ f b a => f (spanEncPay a) b) (fun _ _ _ _ f a => f (spanEncPay a)).


Inductive IkeV2PayloadContentS {S : Type} :=
| SA : VECTOR (@IkeV2ProposalS S) -> IkeV2PayloadContentS
| KE : (@KeyExchangePayloadS S) -> IkeV2PayloadContentS
| IDi : (@IdentificationPayloadS S) -> IkeV2PayloadContentS
| IDr : (@IdentificationPayloadS S) -> IkeV2PayloadContentS
| CertificatePC : (@CertificatePayloadS S) -> IkeV2PayloadContentS
| CertificateRequestPC : (@CertificateRequestPayloadS S) -> IkeV2PayloadContentS
| AuthenticationPC : (@AuthenticationPayloadS S) -> IkeV2PayloadContentS
| NoncePC : (@NoncePayloadS S) -> IkeV2PayloadContentS
| NotifyPC : (@NotifyPayloadS S) -> IkeV2PayloadContentS
| DeletePC : (@DeletePayloadS S) -> IkeV2PayloadContentS
| VendorIDPC : (@VendorIDPayloadS S) -> IkeV2PayloadContentS
| TSi : (@TrafficSelectorPayloadS S) -> IkeV2PayloadContentS
| TSr : (@TrafficSelectorPayloadS S) -> IkeV2PayloadContentS
| Encrypted : (@EncryptedPayloadS S) -> IkeV2PayloadContentS
| Unknown : S -> IkeV2PayloadContentS
| Dummy : IkeV2PayloadContentS.


Definition IkeV2PayloadContent := @IkeV2PayloadContentS span.

Definition foldr_content {A B} (f : A -> B -> B) b ta :=
  match ta with
  | SA l =>
    List.fold_right f b (List.fold_right (fun a l => foldMap (list A) _ (fun v => [v]) (snd a) ++ l) [] (Vector.values (`l)))
  | CertificateRequestPC data | CertificatePC data | IDr data
  | NotifyPC data  | NoncePC data | AuthenticationPC data  | IDi data
  | TSr data | TSi data | VendorIDPC data | DeletePC data | KE data
  | Encrypted data => foldr _ _ f b data
  | Unknown data => f data b
  | Dummy => b
  end.

Definition foldMap_content M `(Monoid.Monoid M) {A} (f : A -> M) ta : M :=
  foldr_content (fun a b => Monoid.f (f a) b) Monoid.mempty ta.

Global Instance Foldable_IkeV2PayloadContentS : Foldable (@IkeV2PayloadContentS) :=
  Build_Foldable _ (@foldr_content) (@foldMap_content).


Record IkeV2PayloadS {S : Type} :=
  mk_payload {
      hdr : (@IkeV2PayloadHeaderS S);
      content : (@IkeV2PayloadContentS S)
    }.

Arguments mk_payload [S].

Definition IkeV2Payload := @IkeV2PayloadS span.

Definition foldr_payload {A B} (f : A -> B -> B) b ta :=
  foldr _ _ f (foldr _ _ f b (hdr ta)) (content ta).

Definition foldMap_payload M `(Monoid.Monoid M) {A} (f : A -> M) ta : M :=
  foldr_payload (fun a b => Monoid.f (f a) b) Monoid.mempty ta.

Global Instance Foldable_IkeV2PayloadS : Foldable (@IkeV2PayloadS) :=
  Build_Foldable _ (@foldr_payload) (@foldMap_payload).

Record IkeV2MessageS (S : Type) :=
  mk_message {
      header : @IkeV2HeaderS S;
      payloads : VECTOR (@IkeV2PayloadS S)
    }.

Definition IkeV2Message := IkeV2MessageS span.

Global Instance Foldable_IkeV2MessageS : Foldable (@IkeV2MessageS).
constructor.
intros A B f b message. destruct message as [hdr pay].
eapply (@foldr (@IkeV2HeaderS)). eapply Foldable_IkeV2HeaderS. eapply f. 2 : eapply hdr.
eapply (@foldr VECTOR). eapply Vector.Foldable_vector. 2 : eapply b. 2 : eapply pay.
intros ike r. eapply (foldr _ _ f r ike).
intros M sg monoid A app message. destruct message as [hdr pay].
eapply (Monoid.f).
eapply (@foldMap (@IkeV2HeaderS)). eapply Foldable_IkeV2HeaderS. auto. eauto. eapply hdr.
eapply (@foldMap (@VECTOR)). eapply Foldable_vector. auto. 2 : eapply pay. intros ivp.
eapply (@foldMap (@IkeV2PayloadS)). eapply Foldable_IkeV2PayloadS. auto. eapply app.
eapply ivp.
Defined.
