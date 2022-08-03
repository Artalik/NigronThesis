From Formalisation Require Import SizeNat Nom IpAddr radius_attr.
From Raffinement Require Import PHOAS RelNomPHOAS.

Definition parse_attribute_content_rel (ht : VAL (NatN 8)) :
  {code : PHOAS (Unknown "radius_attribute") | forall data s vt t,
      sem_VAL ht vt ->
      sem_val vt = t ->
      adequate (fun _ _ _ => True%type)(parse_attribute_content t) code data s}.
  eapply exist. intros. unfold parse_attribute_content. subst.
  eapply (natN_switch_adequate _ (EUna EVal ht)); repeat econstructor; eauto.

  (* 31 *)
  eapply (LScons_adequate _ _ 31).
  step. eapply rest_adequate. destruct H0 as [P0 [P1 P2]].
  eapply (cstruct_adequate "radius_attribute" "create_CallingStationId" (CONS (Var vres) NIL)).

  (* 11 *)
  eapply (LScons_adequate _ _ 11).
  step. eapply rest_adequate. destruct H0 as [P0 [P1 P2]].
  eapply (cstruct_adequate "radius_attribute" "create_FilterId" (CONS (Var vres) NIL)).

  (* 7 *)
  eapply (LScons_adequate _ _ 7).
  eapply bind_adequate. eapply be_u32_adequate. intros. be_spec_clean.
  eapply (cstruct_adequate "radius_attribute" "create_Protocol" (CONS (Var vres) NIL)).

  (* 13 *)
  eapply (LScons_adequate _ _ 13).
  eapply bind_adequate. eapply be_u32_adequate. intros. be_spec_clean.
  eapply (cstruct_adequate "radius_attribute" "create_Compression" (CONS (Var vres) NIL)).

  (* 9 *)
  eapply (LScons_adequate _ _ 9).
  eapply map_parser_adequate. eapply consequence_adequate. unfold size4u. step.
  intros. clean_up. split; auto. intros. step.
  eapply get_ipv4_adequate.
  eapply (cstruct_adequate "radius_attribute" "create_FramedIPNetmask" (CONS (Var vres) NIL)).

  (* 5 *)
  eapply (LScons_adequate _ _ 5).
  eapply bind_adequate. eapply be_u32_adequate. intros. be_spec_clean. subst.
  eapply (cstruct_adequate "radius_attribute" "create_NasPort" (CONS (Var vres) NIL)).

    (* 3 *)
  eapply (LScons_adequate _ _ 3).
  repeat step. eapply be_u8_adequate.
  eapply rest_adequate. be_spec_clean. destruct H2 as [P3 [P4 P2]]. subst.
  eapply (cstruct_adequate "radius_attribute" "create_ChapPassword" (CONS (Var vres0) (CONS (Var vres1) NIL))).

  (* 30 *)
  eapply (LScons_adequate _ _ 30).
  repeat step. eapply rest_adequate. destruct H0 as [P0 [P1 P2]]. subst.
  eapply (cstruct_adequate "radius_attribute" "create_CalledStationId" (CONS (Var vres) NIL)).

  (* 26 *)
  eapply (LScons_adequate _ _ 26).
  repeat step. eapply be_u32_adequate. eapply rest_adequate.
  repeat clean_up. destruct H2 as [P2 [P3 P4]]. subst.
  eapply (cstruct_adequate "radius_attribute" "create_VendorSpecific" (CONS (Var vres0) (CONS (Var vres1) NIL))).

  (* 10 *)
  eapply (LScons_adequate _ _ 10).
  eapply bind_adequate. eapply be_u32_adequate. intros. repeat clean_up. subst.
  eapply (cstruct_adequate "radius_attribute" "create_Routing" (CONS (Var vres) NIL)).

  (* 6 *)
  eapply (LScons_adequate _ _ 6).
  eapply bind_adequate. eapply be_u32_adequate. intros. repeat clean_up. subst.
  eapply (cstruct_adequate "radius_attribute" "create_Service" (CONS (Var vres) NIL)).

  (* 12 *)
  eapply (LScons_adequate _ _ 12).
  eapply bind_adequate. eapply be_u32_adequate. intros. repeat clean_up. subst.
  eapply (cstruct_adequate "radius_attribute" "create_FramedMTU" (CONS (Var vres) NIL)).

  (* 8 *)
  eapply (LScons_adequate _ _ 8).
  eapply map_parser_adequate. eapply consequence_adequate. unfold size4u. step.
  intros. clean_up. split; auto. intros.
  step. eapply get_ipv4_adequate.
  eapply (cstruct_adequate "radius_attribute" "create_FramedIPAddress" (CONS (Var vres) NIL)).

  (* 4 *)
  eapply (LScons_adequate _ _ 4).
  eapply map_parser_adequate. eapply consequence_adequate. unfold size4u. step.
  intros. clean_up. split; auto. intros.
  step. eapply get_ipv4_adequate.
  eapply (cstruct_adequate "radius_attribute" "create_NasIPAddress" (CONS (Var vres) NIL)).

  (* 2 *)
  eapply (LScons_adequate _ _ 2).
  step. eapply rest_adequate.
  eapply (cstruct_adequate "radius_attribute" "create_UserPassword" (CONS (Var vres) NIL)).

  (* 1 *)
  eapply (LScons_adequate _ _ 1).
  step. eapply rest_adequate.
  eapply (cstruct_adequate "radius_attribute" "create_UserName" (CONS (Var vres) NIL)).

  (* default *)
  eapply LSnil_adequate. intros elem elem_neq.
  destruct elem as [|elem]; try (exfalso; apply elem_neq; repeat constructor; done).
  Ltac solve_default ht :=
    step; [eapply rest_adequate |
            match goal with
            | H : rest_spec _ _ _ (sem_val ?vres) |- _ =>
                let P0 := fresh "P" in
                let P1 := fresh "P" in
                let P2 := fresh "P" in
                destruct H as [P0 [P1 P2]]; subst;
                eapply (cstruct_adequate "radius_attribute" "create_Unknown" (CONS ht (CONS (Var vres) NIL)))
          end].
    solve_default ht.
    repeat (destruct elem; try (exfalso; apply elem_neq; repeat constructor; done);
            try solve_default ht).
Defined.

Lemma parse_attribute_content_adequate (ht : VAL (NatN 8)) :
    forall data s vt t,
      sem_VAL ht vt ->
      sem_val vt = t ->
      adequate (fun _ _ _ => True%type)(parse_attribute_content t)
        (proj1_sig (parse_attribute_content_rel ht)) data s.
Proof. intros. destruct parse_attribute_content_rel. eauto. Qed.


Definition parse_radius_attribute_rel :
  {code : PHOAS (Unknown "radius_attribute") | forall data vs, adequate (fun _ _ _ => True%type) parse_radius_attribute code data vs}.
  eapply exist. intros data vs. unfold parse_radius_attribute.
  repeat step. eapply be_u8_adequate. eapply verify_adequate.
  2 : eapply be_u8_adequate. be_spec_clean. intros vy x s [P2 P1]. subst.
  instantiate (1 := fun vy => EBin ELe (Const (ENat 2)) (EUna EVal (Var vy))).
  eexists. split; repeat econstructor; eauto. be_spec_clean.
  destruct H0 as [[P1 P3] P2]. subst.
  eapply map_parser_adequate. eapply consequence_adequate. step.
  intros. repeat clean_up. split; auto.
  intros. eapply (parse_attribute_content_adequate (Var vres)); repeat econstructor; eauto.
Defined.

Lemma parse_radius_attribute_adequate : forall data vs,
    adequate (fun _ _ _ => True%type) parse_radius_attribute (proj1_sig parse_radius_attribute_rel) data vs.
Proof. intros. destruct parse_radius_attribute_rel. eauto. Qed.

Definition equiv_parse_radius_attribute_rel {var} :
  {code : @PHOAS var _ | equiv_prog Nil _ (`parse_radius_attribute_rel) code}.
  eapply exist. repeat econstructor.
Defined.
