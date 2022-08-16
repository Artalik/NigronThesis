From Formalisation Require Import ikev2_transforms ikev2_notify.
From Formalisation Require Import Nom IpAddr.

Open Scope N_scope.

Definition IkeExchangeType := nat8.

Definition ProtocolID := nat8.

Definition IkePayloadType := nat8.

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
  Build_Foldable _ (fun _ _ _ _ _ _ => Monoid.mempty).

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
  Build_Foldable _ (fun _ _ _ _ _ _ => Monoid.mempty).


Record IkeV2GenericPayloadS {S : Type} :=
  mk_genericpayload {
      hdrGen : IkeV2PayloadHeader;
      payloadGen : S
    }.

Definition IkeV2GenericPayload := @IkeV2GenericPayloadS span.

Global Instance Foldable_IkeV2GenericPayload : Foldable (@IkeV2GenericPayloadS) :=
  Build_Foldable _ (fun _ _ _ _ f a => f (payloadGen a)).

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

Global Instance Foldable_IkeV2Proposal : Foldable (@IkeV2ProposalS).
econstructor. intros. destruct X0.
eapply Monoid.f. destruct spi0. eapply (X a). eapply Monoid.mempty.
eapply (@foldMap). eapply (@Foldable_Vector). eapply Foldable_IkeV2Transform. eapply H.
eapply X. eapply transforms0.
Defined.

Record KeyExchangePayloadS {S : Type} :=
  mk_ExcPayload {
      dh_group : IkeTransformDHType;
      reserved : nat16;
      kex_data : S
    }.

Definition KeyExchangePayload := @KeyExchangePayloadS span.

Global Instance Foldable_KeyExchangePayload : Foldable (@KeyExchangePayloadS).
econstructor. intros. eapply (X (kex_data X0)). Defined.

Definition IdentificationType := nat8.

Record IdentificationPayloadS {S : Type} :=
  mk_IdPayload {
      id_type : IdentificationType;
      reserved1 : nat8;
      reserved2 : nat16;
      ident_data : S
    }.

Definition IdentificationPayload := @IdentificationPayloadS span.

Global Instance Foldable_IdentificationPayload : Foldable (@IdentificationPayloadS).
econstructor. intros. eapply (X (ident_data X0)).
Defined.

Definition CertificateEncoding := nat8.

Record CertificatePayloadS {S : Type} :=
  mk_certiPayload {
      cert_encoding : CertificateEncoding;
      cert_data : S
    }.

Definition CertificatePayload := @CertificatePayloadS span.

Global Instance Foldable_CertificatePayload : Foldable (@CertificatePayloadS).
econstructor. intros. eapply (X (cert_data X0)).
Defined.

Record CertificateRequestPayloadS {S : Type} :=
  mk_certReqPayload {
      cert_encodingREq : CertificateEncoding;
      ca_dataReq : S
    }.

Definition CertificateRequestPayload := @CertificateRequestPayloadS span.

Global Instance Foldable_CertificateRequestPayload : Foldable (@CertificateRequestPayloadS).
econstructor. intros. eapply (X (ca_dataReq X0)).
Defined.

Definition AuthenticationMethod := nat8.

Definition is_unassigned (n : AuthenticationMethod): bool :=
  let v := val n in
  ((4 <=? v) && (v <=? 8)) || ((15 <=? v) && (v <=? 200)).

Definition is_private_use (n : AuthenticationMethod) : bool :=
  201 <=? val n.

Record AuthenticationPayloadS {S : Type} :=
  mk_authPayload {
      auth_method : AuthenticationMethod;
      auth_data : S
    }.

Arguments mk_authPayload [S].

Definition AuthenticationPayload := @AuthenticationPayloadS span.

Global Instance Foldable_AuthenticationPayload : Foldable (@AuthenticationPayloadS).
econstructor. intros. eapply (X (auth_data X0)).
Defined.

Definition NoncePayloadS {S : Type} := S.

Definition NoncePayload := @NoncePayloadS span.

Global Instance Foldable_NoncePayload : Foldable (@NoncePayloadS).
econstructor. intros. eapply (X X0).
Defined.

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

Global Instance Foldable_NotifyPayload : Foldable (@NotifyPayloadS).
econstructor. intros.
eapply Monoid.f. destruct (num_spi X0). eapply (X a). eapply Monoid.mempty.
destruct (spiNoti X0). eapply (X a). eapply Monoid.mempty.
Defined.

Record DeletePayloadS {S : Type} :=
  mk_deletePayload {
      protocol_idDel : ProtocolID;
      spi_sizeDel : nat8;
      num_spiDel : nat16;
      spiDel : S
    }.

Arguments mk_deletePayload [S].

Definition DeletePayload := @DeletePayloadS span.

Global Instance Foldable_DeletePayload : Foldable (@DeletePayloadS).
econstructor. intros. eapply (X (spiDel X0)).
Defined.

Definition VendorIDPayloadS {S : Type} := S.

Definition VendorIDPayload := @VendorIDPayloadS span.

Global Instance Foldable_VendorIDPayload : Foldable (@VendorIDPayloadS).
econstructor. intros. eapply (X X0).
Defined.


Definition TSType := nat8.

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

Global Instance Foldable_TrafficSelector : Foldable (@TrafficSelectorS).
econstructor. intros. eapply Monoid.f. eapply (X (start_addr X0)).
  eapply (X (end_addr X0)).
Defined.

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
  match val (ts_type v) with
  | 7 => let! ipv4 := ipv4_from_slice (start_addr v) in
        ret (Some (V4 ipv4))
  | 8 => let! ipv6 := ipv6_from_slice (start_addr v) in
        ret (Some (V6 ipv6))
  | _ => ret Datatypes.None
  end.


Definition get_end_addr (v : TrafficSelector) : NomG (option IpAddr) :=
  match val (ts_type v) with
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

Global Instance Foldable_TrafficSelectorPayload : Foldable (@TrafficSelectorPayloadS).
econstructor. intros.
eapply Monoid.f. eapply (X (reserved_tsp X0)).
eapply (@foldMap).  eapply Foldable_Vector. eapply H. eapply X. eapply (ts X0).
Defined.

Definition EncryptedPayloadS {S : Type} := S.

Definition EncryptedPayload := @EncryptedPayloadS span.

Global Instance Foldable_EncryptedPayload : Foldable (@EncryptedPayloadS).
econstructor. intros. eapply (X X0).
Defined.

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

Definition foldMap_content M (sg : Monoid.Semigroup M) (H : Monoid.Monoid M) {A} (f : A -> M) ta :=
  match ta with
  | SA l =>
      @foldMap (fun X => VECTOR (@IkeV2ProposalS X)) Foldable_Vector M _ _ _ f l
  | CertificateRequestPC data | CertificatePC data | IDr data
  | NotifyPC data  | NoncePC data | AuthenticationPC data  | IDi data
  | TSr data | TSi data | VendorIDPC data | DeletePC data | KE data
  | Encrypted data => foldMap M _ f data
  | Unknown data => f data
  | Dummy => Monoid.mempty
  end.

Global Instance Foldable_IkeV2PayloadContentS : Foldable (@IkeV2PayloadContentS) :=
  Build_Foldable _ (@foldMap_content).


Record IkeV2PayloadS {S : Type} :=
  mk_payload {
      hdr : (@IkeV2PayloadHeaderS S);
      content : (@IkeV2PayloadContentS S)
    }.

Arguments mk_payload [S].

Definition IkeV2Payload := @IkeV2PayloadS span.

Global Instance Foldable_IkeV2PayloadS : Foldable (@IkeV2PayloadS).
econstructor. intros. eapply Monoid.f. eapply @foldMap.
eapply Foldable_IkeV2PayloadHeader. eapply H. eapply X. eapply (hdr X0).
eapply @foldMap.
eapply Foldable_IkeV2PayloadContentS. eapply H. eapply X. eapply (content X0).
Defined.


(* Record IkeV2MessageS (S : Type) := *)
(*   mk_message { *)
(*       header : @IkeV2HeaderS S; *)
(*       payloads : VECTOR (@IkeV2PayloadS S) *)
(*     }. *)

(* Definition IkeV2Message := IkeV2MessageS span. *)

(* Global Instance Foldable_IkeV2MessageS : Foldable (@IkeV2MessageS). *)
(* econstructor. intros. eapply Monoid.f. eapply @foldMap. *)
(* eapply Foldable_IkeV2HeaderS. eapply H. eapply X. eapply (header _ X0). *)
(* eapply (@Foldable_Vector). eapply Foldable_IkeV2PayloadS. eapply H. eapply X. *)
(* eapply (payloads _ X0). *)
(* Defined. *)
