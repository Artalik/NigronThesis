From Formalisation Require Import SizeNat.
From Formalisation Require Import Nom ssh.
From Raffinement Require Import PHOAS RelNomPHOAS.

Definition parse_string_rel :
  { code : PHOAS Span |
    forall data s, adequate (fun _ => span_eq data) parse_string code data s}.
  eapply exist. unfold parse_string. intros.
  eapply length_data_adequate.
  step. eapply be_u32_adequate.
  be_spec_clean. step.
Defined.

Lemma parse_string_adequate data s :
    adequate (fun _ => span_eq data) parse_string (`parse_string_rel) data s.
Proof. destruct parse_string_rel. eapply a. Qed.


Definition parse_packet_dh_init_rel :
  { code : PHOAS (Unknown "SSHPacket") |
    forall data s, adequate (fun _ _ _ => True%type) parse_packet_dh_init code data s}.
  eapply exist. intros. unfold parse_packet_dh_init.
  unfold combinator.map.
  step. eapply parse_string_adequate.
  eapply (extern_adequate "SSHPacket" "create_DiffieHellmanInit"
            (CONS (Var vres) NIL)).
Defined.

Definition parse_packet_dh_init_adequate : forall data s,
    adequate (fun _ _ _ => True%type) parse_packet_dh_init (`parse_packet_dh_init_rel) data s.
Proof. destruct parse_packet_dh_init_rel. eapply a. Qed.


Definition parse_packet_dh_reply_rel :
  { code : PHOAS (Unknown "SSHPacket") |
    forall data s, adequate (fun _ _ _ => True%type) parse_packet_dh_reply code data s}.
  eapply exist. intros. unfold parse_packet_dh_reply.
  step. eapply parse_string_adequate.
  step. eapply parse_string_adequate.
  step. eapply parse_string_adequate.
  eapply (extern_adequate "SSHPacket" "create_DiffieHellmanReply"
            (CONS (Var vres) (CONS (Var vres0) (CONS (Var vres1) NIL)))).
Defined.

Lemma parse_packet_dh_reply_adequate data s :
    adequate (fun _ _ _ => True%type) parse_packet_dh_reply (`parse_packet_dh_reply_rel) data s.
Proof. destruct parse_packet_dh_reply_rel. eapply a. Qed.

Definition parse_packet_debug_rel :
  { code : PHOAS (Unknown "SSHPacket") |
    forall data s, adequate (fun _ _ _ => True%type) parse_packet_debug code data s}.
  eapply exist. intros. unfold parse_packet_debug.
  step. eapply be_u8_adequate.
  step. eapply parse_string_adequate.
  step. eapply parse_string_adequate.
  eapply (extern_adequate "SSHPacket" "create_Debug"
            (CONS (EBin ELt (Const (ENat 0)) (EUna EVal (Var vres)))
               (CONS (Var vres0)
                  (CONS (Var vres1) NIL)))).
Defined.

Lemma parse_packet_debug_adequate data s :
    adequate (fun _ _ _ => True%type) parse_packet_debug (`parse_packet_debug_rel) data s.
Proof. destruct parse_packet_debug_rel. eapply a. Qed.


Definition parse_packet_disconnect_rel :
  { code : PHOAS (Unknown "SSHPacket") |
    forall data s, adequate (fun _ _ _ => True%type) parse_packet_disconnect code data s}.
  eapply exist. intros. unfold parse_packet_disconnect.
  step. eapply be_u32_adequate.
  step. eapply parse_string_adequate.
  step. eapply parse_string_adequate.
  eapply (extern_adequate "SSHPacket" "create_Disconnect"
            (CONS (Var vres)
               (CONS (Var vres0)
                  (CONS (Var vres1) NIL)))).
Defined.

Lemma parse_packet_disconnect_adequate data s :
    adequate (fun _ _ _ => True%type) parse_packet_disconnect (`parse_packet_disconnect_rel) data s.
Proof. destruct parse_packet_disconnect_rel. eapply a. Qed.

Definition parse_packet_key_exchange_rel :
  { code : PHOAS (Unknown "SSHPacket") |
    forall data s, adequate (fun _ _ _ => True%type) parse_packet_key_exchange code data s}.
  eapply exist. unfold parse_packet_key_exchange. intros.
  step. unfold usize_16. step.
  step. eapply parse_string_adequate.
  step. eapply parse_string_adequate.
  step. eapply parse_string_adequate.
  step. eapply parse_string_adequate.
  step. eapply parse_string_adequate.
  step. eapply parse_string_adequate.
  step. eapply parse_string_adequate.
  step. eapply parse_string_adequate.
  step. eapply parse_string_adequate.
  step. eapply parse_string_adequate.
  step. eapply be_u8_adequate.
  step. eapply be_u32_adequate.
  eapply (extern_adequate "SSHPacket" "create_KeyExchange"
            (CONS (Var vres)
               (CONS (Var vres0)
                  (CONS (Var vres1)
                     (CONS (Var vres2)
                        (CONS (Var vres3)
                           (CONS (Var vres4)
                              (CONS (Var vres5)
                                 (CONS (Var vres6)
                                    (CONS (Var vres7)
                                       (CONS (Var vres8)
                                          (CONS (Var vres9)
                                                (CONS (Var vres10)
                                                   NIL))))))))))))).
Defined.


Lemma parse_packet_key_exchange_adequate data s :
  adequate (fun _ _ _ => True%type) parse_packet_key_exchange
    (`parse_packet_key_exchange_rel) data s.
Proof. destruct parse_packet_key_exchange_rel. eapply a. Qed.

Definition parse_ssh_packet_rel :
  { code : PHOAS (Pair (Unknown "SSHPacket") Span) |
    forall data s, adequate (fun _ _ _ => True%type) parse_ssh_packet code data s}.
  eapply exist. intros. unfold parse_ssh_packet.
  step. eapply be_u32_adequate.
  step. eapply be_u8_adequate.
  be_spec_clean. step.
  step. step.
  eapply map_parser_adequate. eapply consequence_adequate. step.
  intros. repeat clean_up. subst. repeat econstructor. auto.
  intros. step. eapply be_u8_adequate.
  eapply (natN_switch_adequate _ (EUna EVal (Var vres1))); repeat econstructor; eauto.
  be_spec_clean. subst. repeat econstructor.

  eapply (LScons_adequate _ _ 31).
  eapply parse_packet_dh_reply_adequate.

  eapply (LScons_adequate _ _ 30).
  eapply parse_packet_dh_init_adequate.

  eapply (LScons_adequate _ _ 21).
  eapply (extern_adequate "SSHPacket" "create_NewKeys" NIL).

  eapply (LScons_adequate _ _ 20).
  eapply parse_packet_key_exchange_adequate.

  eapply (LScons_adequate _ _ 6).
  unfold combinator.map.
  step. eapply parse_string_adequate.
  eapply (extern_adequate "SSHPacket" "create_ServiceAccept" (CONS (Var vres2) NIL)).

  eapply (LScons_adequate _ _ 5).
  unfold combinator.map.
  step. eapply parse_string_adequate.
  eapply (extern_adequate "SSHPacket" "create_ServiceRequest" (CONS (Var vres2) NIL)).

  eapply (LScons_adequate _ _ 4).
  eapply parse_packet_debug_adequate.

  eapply (LScons_adequate _ _ 3).
  unfold combinator.map.
  step. eapply be_u32_adequate.
  eapply (extern_adequate "SSHPacket" "create_Unimplemented" (CONS (Var vres2) NIL)).

  eapply (LScons_adequate _ _ 2).
  unfold combinator.map.
  step. eapply parse_string_adequate.
  eapply (extern_adequate "SSHPacket" "create_Ignore" (CONS (Var vres2) NIL)).

  eapply (LScons_adequate _ _ 1).
  eapply parse_packet_disconnect_adequate.

  eapply LSnil_adequate. intros elem elem_neq.
  destruct elem as [|elem]; try (exfalso; apply elem_neq; repeat constructor; done).
  Ltac solve_default :=
    eapply fail_adequate.
  solve_default.
  repeat (destruct elem; try (exfalso; apply elem_neq; repeat constructor; done);
          try solve_default).
  step. eapply (take_verif_adequate _ _ (EUna EVal (Var vres0))).
  be_spec_clean. subst. repeat econstructor.
  eapply (ret_adequate _ _ _ (EBin EPair (Var vres1) (Var vres2))).
  be_spec_clean. repeat clean_up. subst. repeat econstructor.
  auto.
Defined.

Definition equiv_parse_ssh_packet_rel {var} :
  {code : @PHOAS var _ | equiv_prog Nil _ (`parse_ssh_packet_rel) code}.
  eapply exist. repeat econstructor.
Defined.
