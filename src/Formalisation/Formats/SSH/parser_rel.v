From Formalisation Require Import SizeNat.
From Formalisation Require Import Nom parser.
From Raffinement Require Import PHOAS RelNomPHOAS.

Inductive list_val :=
| Nil : list_val
| CONS : forall X, PHOAS.val X -> list_val -> list_val.

Ltac list_sem_val f l :=
  match f with
  | ?f (@sem_val ?ty ?v) =>
      let l := constr:(CONS ty v l) in list_sem_val f l
  | ?f _ => list_sem_val f l
  | _ => l
  end.

Ltac list_val f :=
  let l := list_sem_val f constr:(Nil) in pose l.

Ltac build_prod ty vals :=
  match ty with
  | Pair ?l ?r =>
      let l := build_prod l vals in
      match l with
      | @pair _ _ ?l ?vs =>
          let r := build_prod r vs in
          match r with
            | @pair _ _ ?r ?vs =>
                constr:((@EBin val _ _ _ EPair l r, vs))
          end
      end
  | ?l =>
      match vals with
      | CONS _ ?v ?vs =>
          constr:((@Var val _ v, vs))
      end
  end.

Ltac build ty vals :=
  let v := build_prod ty vals in
  match v with
  | @pair _ _ ?r ?vs =>
      r
  end.

Ltac ret_match :=
  match goal with
  | |- @adequate _ ?p _ (@ret _ _ ?f) _ _ _ =>
      let l := list_sem_val f constr:(Nil) in
      let v := build p l in
      eapply (ret_adequate _ _ _ v)
  | |- @adequate _ ?p _ (@ret _ _ ?f) _ _ _ =>
      unfold p; ret_match
  end.

Open Scope N_scope.

Definition banner := Pair Span Span.

Definition banner_rel (t : span) (b : SshBanner) (p : type_to_Type banner) :=
  protover b = p.1 /\ swver b = p.2.

Definition ssh_parse_banner_rel :
  {code | forall data s, adequate banner_rel ssh_parse_banner code data s}.
  eapply exist. intros data s. unfold ssh_parse_banner.
  step. eapply (tag_adequate (Const (EString "SSH-"))); repeat econstructor.
  step. eapply (is_not_adequate (Const (EString "-"))); repeat econstructor.
  step. eapply (char_adequate (Const (ENatN (bin_combinators.ascii_to_nat8 "-")))); repeat econstructor.
  step. eapply alt_adequate.
  eapply (is_not_adequate (Const (EString _))); repeat econstructor; eauto.
  eapply consequence_adequate. eapply rest_adequate.
  intros t2 v hv [P3 [P1 P2]]; auto. simpl in *. subst.
  ret_match; repeat econstructor; eauto.
Defined.

Lemma ssh_parse_banner_adequate :
  forall data s, adequate banner_rel ssh_parse_banner (proj1_sig ssh_parse_banner_rel) data s.
Proof. intros. destruct ssh_parse_banner_rel as [p I]. eapply I; eauto. Qed.

Definition record_header := Pair (Pair (NatN 32) (NatN 8)) (NatN 8).

Definition record_header_rel s t (b : SshRecordHeader) (p : type_to_Type record_header):=
  len t = len s - 6 /\ pkt_len b = p.1.1 /\ padding_len b = p.1.2 /\ msg_code b = MessageCode_from_u8 p.2.

Definition ssh_parse_record_header_rel :
  {code | forall data s, adequate (record_header_rel s) ssh_parse_record_header code data s}.
  eapply exist. intros data s. unfold ssh_parse_record_header.
  step. eapply verify_adequate.
  2 : eapply be_u32_adequate.
  intros. simpl in *. destruct H.
  instantiate (1 := (fun vy => EBin ELt (Const (ENat 1)) (EUna EVal (Var vy)))).
  eexists. split; repeat econstructor; eauto. simpl. subst. auto.
  step. eapply be_u8_adequate.
  step. eapply be_u8_adequate.
  be_spec_clean. subst. destruct H as [[P3 P1] P2]. subst.
  eapply (ret_adequate _ _ _ (EBin EPair (EBin EPair (Var vres) (Var vres0)) (Var vres1)));
    repeat econstructor; eauto. lia.
Defined.

Lemma ssh_parse_record_header_adequate :
  forall data s, adequate (record_header_rel s) ssh_parse_record_header (proj1_sig ssh_parse_record_header_rel) data s.
Proof. destruct ssh_parse_record_header_rel. auto. Qed.

Definition record_record_rel (t : span) (b : SshRecordHeader) (p : type_to_Type record_header):=
  pkt_len b = p.1.1 /\ padding_len b = p.1.2 /\ msg_code b = MessageCode_from_u8 p.2.

Definition ssh_parse_record_rel :
  { code | forall data s, adequate record_record_rel ssh_parse_record code data s}.
  eapply exist. intros data s. unfold ssh_parse_record.
  step. eapply verify_adequate.
  2 : eapply be_u32_adequate.
  intros. simpl in *. destruct H.
  intros. instantiate (1:= (fun hx => EBin ELt (Const (ENat 1)) (EUna EVal (Var hx)))).
  eexists. split; repeat econstructor; eauto. simpl. subst. eauto.
  step. eapply be_u8_adequate.
  step. eapply be_u8_adequate.
  be_spec_clean. destruct H as [[P3 P4] P2]. subst. repeat step. clean_up.
  eapply (ret_adequate _ _ _ (EBin EPair (EBin EPair (Var vres) (Var vres0)) (Var vres1)));
    repeat econstructor.
Defined.

Lemma ssh_parse_record_adequate :
  forall data s, adequate record_record_rel ssh_parse_record (proj1_sig ssh_parse_record_rel) data s.
Proof. destruct ssh_parse_record_rel. auto. Qed.

Definition parse_string_rel :
  { code | forall data s, adequate (fun _ => span_eq data) parse_string code data s}.
  eapply exist. intros data s. unfold parse_string.
  eapply length_data_adequate. step. eapply be_u32_adequate.
  destruct H. step.
Defined.

Lemma parse_string_adequate :
  forall data s, adequate (fun _ => span_eq data) parse_string (proj1_sig parse_string_rel) data s.
Proof. destruct parse_string_rel. auto. Qed.


Definition packet_key_exchange : type :=
  Pair
  (Pair (Pair (Pair (Pair Span Span) Span) (Pair (Pair Span Span) Span))
     (Pair (Pair Span Span) (Pair (Pair Span Span) Span))) (Pair (NatN 8) (NatN 32)).

Definition packetkeyexchange_rel (p : SshPacketKeyExchangeS span) (b : type_to_Type packet_key_exchange) :=
  cookie _ p = b.1.1.1.1.1 /\
    kex_algs _ p = b.1.1.1.1.2 /\
    server_host_key_algs _ p = b.1.1.1.2 /\
    encr_algs_client_to_server _ p = b.1.1.2.1.1 /\
    encr_algs_server_to_client _ p = b.1.1.2.1.2 /\
    max_algs_client_to_server _ p = b.1.1.2.2 /\
    max_algs_server_to_client _ p = b.1.2.1.1 /\
    comp_algs_client_to_server _ p = b.1.2.1.2 /\
    comp_algs_server_to_client _ p = b.1.2.2.1.1 /\
    langs_client_to_server _ p = b.1.2.2.1.2 /\
    langs_server_to_client _ p = b.1.2.2.2 /\
    first_kex_packet_follows _ p = b.2.1 /\
    reserved _ p = b.2.2.

Definition ssh_parse_key_exchange_rel :
  { code | forall data s, adequate (fun _ => packetkeyexchange_rel) ssh_parse_key_exchange code data s}.
  eapply exist. intros. unfold ssh_parse_key_exchange.
  repeat step. unfold usize_16. step.
  1-10 : eapply parse_string_adequate.
  eapply be_u8_adequate. eapply be_u32_adequate.
  simpl in *. destruct H10. destruct H11. repeat clean_up. subst.
  ret_match; repeat econstructor.
Defined.

Lemma ssh_parse_key_exchange_adequate :
  forall data s, adequate (fun _ => packetkeyexchange_rel) ssh_parse_key_exchange (proj1_sig ssh_parse_key_exchange_rel) data s.
Proof. destruct ssh_parse_key_exchange_rel. auto. Qed.
