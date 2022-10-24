From SepLogic Require Export SepBasicCore SepSet.
From Classes Require Import Foldable.
From Equations Require Import Equations.
From Formalisation Require Import Span Vector Inject disjoint.

Definition iProp := monPred biInd hpropI.

Open Scope N_scope.

Equations IsFresh_aux (pos : N) (len : N): iProp by wf (N.to_nat len) lt :=
  IsFresh_aux pos 0 := emp;
  IsFresh_aux pos len :=
    & pos ∗ IsFresh_aux (N.succ pos) (N.pred len).
Next Obligation.
  intros. lia.
Defined.

Definition IsFresh (s : span) := IsFresh_aux (pos s) (len s).

(* IsFresh facts *)

Lemma IsFresh_len_succ : forall pos len,
    ⊢ IsFresh {| pos := pos; len := N.succ len |} -∗
    & pos ∗ IsFresh {| pos := N.succ pos; len := len |}.
Proof.
  iIntros. unfold IsFresh. simpl. rewrite <- N.succ_pos_spec.
  rewrite IsFresh_aux_equation_2. rewrite N.succ_pos_spec. rewrite N.pred_succ.
  auto.
Qed.


Lemma IsFresh_Map : forall n v,
    ⊢ ([∗ set] n ∈ list_to_set (seq v n), & n)
      -∗ IsFresh_aux v n.
Proof.
  induction n using N.peano_ind; simpl; intros.
  - auto.
  - iIntros "HA". rewrite <- N.succ_pos_spec.
    rewrite IsFresh_aux_equation_2. rewrite seq_equation_2.
    rewrite N.succ_pos_spec. rewrite N.pred_succ. simpl.
    iDestruct (big_sepS_union with "HA") as "[HA HB]".
    + repeat intro. apply elem_of_list_to_set in H0. apply elem_of_list_In in H0.
      eapply in_seq in H0 as [m [P0 P1]]. eapply elem_of_singleton_1 in H. subst.
      rewrite decode_encode in P1. inversion P1. lia.
    + iSplitL "HA".
      * iDestruct encode_singleton as "[HB _]". iApply "HB".
        iApply big_sepS_singleton. iFrame.
      * iApply IHn. iApply "HB".
Qed.

Lemma IsFresh_injectSL : forall s,
    ⊢ IsFresh s -∗ injectSL (pos s) (pos s + len s).
Proof.
  intros [pos0 len0]. revert pos0. simpl. induction len0 using N.peano_ind; intros.
  - simpl. iIntros "HA". iApply injectSL_emp; auto. lia.
  - iIntros "HA". unfold IsFresh. simpl. rewrite <- N.succ_pos_spec.
    rewrite IsFresh_aux_equation_2. rewrite N.succ_pos_spec. rewrite N.pred_succ.
    iDestruct "HA" as "[HA HB]".
    iDestruct (IHlen0 with "[HB]") as "HB".
    + unfold IsFresh. simpl. iApply "HB".
    + unfold injectSL.
      rewrite (inject_aux_add_head (pos0 + N.succ len0)). 2 : lia.
      iApply big_sepS_union. apply inject_add_disjoint.
      iSplitL "HA".
      * iApply big_sepS_singleton; auto.
      * rewrite N.add_succ_l -N.add_succ_r. iApply "HB".
Qed.

Lemma inject_IsFresh : forall fin span start,
    start = pos span ->
    fin = (pos span + len span)%N ->
    ⊢ injectSL start fin -∗ IsFresh span.
Proof.
  intros fin s start P0 P1.
  iIntros "HA". subst. unfold injectSL, inject, inject_aux.
  rewrite N.add_comm. rewrite N.add_sub.
  iApply (IsFresh_Map with "HA").
Qed.


Lemma inject_IsFresh_2 : forall span,
    ⊢ injectSL (pos span) (pos span + len span) -∗ IsFresh span.
Proof.
  intros s.
  iIntros "HA". subst. unfold injectSL, inject, inject_aux.
  rewrite N.add_comm. rewrite N.add_sub.
  iApply (IsFresh_Map with "HA").
Qed.

Lemma single_IsFresh : forall sing s,
    ⊢ & sing -∗ IsFresh s -∗ ⌜sing ∉ inject (pos s) (pos s + len s)⌝.
Proof.
  intros sing s. destruct s as [pos len]. simpl. revert sing pos.
  induction len using N.peano_ind.
  - simpl; iIntros. rewrite (inject_empty pos); auto. lia.
  - simpl; iIntros. iNorm. iDestruct (IsFresh_len_succ with "HE") as "[HA HB]".
    iDestruct (IHlen with "HC HB") as "%".
    iDestruct (singleton_neq with "HC HA") as "%". iPureIntro.
    rewrite <- N.add_succ_comm. rewrite inject_add. 2 : lia.
    rewrite inject_singleton. intro. apply elem_of_union in H1 as [H2 | H2].
    + apply H0. apply elem_of_singleton_1 in H2. auto.
    + apply (H H2).
Qed.

Lemma IsFresh_spec : forall s0 s1,
    ⊢ IsFresh s0 -∗ IsFresh s1 -∗ ⌜disjoint s0 s1⌝.
Proof.
  intros [p0 l0]. revert p0. induction l0 using N.peano_ind.
  - simpl; iIntros. unfold disjoint. rewrite (inject_empty p0); auto. simpl. lia.
  - simpl; iIntros. iNorm. iDestruct (IsFresh_len_succ with "HC") as "[HA HB]".
    iDestruct (single_IsFresh with "HA HE") as "%".
    iDestruct (IHl0 with "HB HE") as "%". simpl in H0. iPureIntro.
    unfold disjoint; simpl. rewrite <- N.add_succ_comm. rewrite inject_add. 2 : lia.
    apply disjoint_union_l. split.
    + rewrite inject_singleton. apply disjoint_singleton_l. apply H.
    + eapply H0.
Qed.

Lemma IsFresh_aux_inject_incl :
  ∀ len pos h,
    IsFresh_aux pos len () h → inject pos (pos + len) ⊆ h.
Proof.
  induction len using N.peano_ind; intros pos h IS.
  -- rewrite inject_empty. 2 : lia. set_solver.
  -- rewrite <- N.succ_pos_spec in IS.
     rewrite IsFresh_aux_equation_2 in IS.
     rewrite N.succ_pos_spec in IS. rewrite N.pred_succ in IS.
     eapply (monPred_at_sep tt (& pos)) in IS.
     unfold hpropI in IS. simpl in *.
     unfold bi_sep in IS. inversion_star h P. clear IS.
     inversion P0. subst. clear P0. eapply IHlen in P1.
     rewrite inject_aux_add_head.
     assert (N.succ pos + len = pos + N.succ len) by lia. rewrite <- H.
     set_solver. lia.
Qed.

Definition M_to_list `{Foldable M} {X} (m : M X) : list X :=
  Foldable.foldMap (list X) X (fun s => [s]) m.

Definition all_disjointSL (l : list span) := [∗ list] v ∈ l, IsFresh v.

Lemma all_disjointSL_incl : forall l v,
  v ∈ l ->
  ∀ h, all_disjointSL l () h →
       inject (pos v) (pos v + len v) ⊆ h.
Proof.
  induction l; intros v P; inversion P; subst; intros h ALL.
  - clear IHl. unfold all_disjointSL in ALL. simpl in *.
    eapply (monPred_at_sep tt (IsFresh a)) in ALL.
    unfold hpropI in ALL. simpl in *.
    unfold bi_sep in ALL. inversion_star h P.
    unfold IsFresh in P1. destruct a. simpl in *. rewrite P0.
    eapply IsFresh_aux_inject_incl in P1. set_solver.
  - unfold all_disjointSL in ALL. simpl in *.
    eapply (monPred_at_sep tt (IsFresh a)) in ALL.
    unfold hpropI in ALL. simpl in *.
    unfold bi_sep in ALL. inversion_star h P.
    rewrite P0. transitivity h1. 2 : set_solver.
    eapply IHl; auto.
Qed.


Definition all_disjointMSL `{Foldable M} (m : M span) : iProp :=
  all_disjointSL (M_to_list m).

Definition all_disjointM {M} `{Foldable M} (m : M span) : Prop :=
  all_disjoint (M_to_list m).

Lemma all_disjoint_SL_to_Prop : forall l, <absorb> all_disjointSL l ⊢ ⌜ all_disjoint l ⌝.
Proof.
  unfold all_disjoint.
  iIntros (l) ">HA". repeat (iApply (@pure_forall_2 _ iPropBiPureForall); iIntros).
  apply elem_of_list_lookup_1 in a2 as [i2 H2].
  apply elem_of_list_lookup_1 in a3 as [i3 H3].
  iDestruct (big_sepL_delete with "HA") as "[HA HC]"; eauto.
  iDestruct (big_sepL_delete with "HC") as "[HB HC]". eapply H2.
  destruct (decide (i2 = i3)). subst. rewrite H2 in H3. inversion H3. contradiction.
  iDestruct (IsFresh_spec with "HB HA") as "%". iPureIntro. apply H.
Qed.

Lemma all_disjoint_spec : forall l, all_disjointSL l ⊢ ⌜ all_disjoint l ⌝.
Proof.
  iIntros. iApply all_disjoint_SL_to_Prop. auto.
Qed.

Theorem all_disjointM_SL_to_Prop : forall `{Foldable M} m,
    <absorb> all_disjointMSL m ⊢ ⌜ all_disjointM m ⌝.
Proof. iIntros "* HA". iApply (all_disjoint_SL_to_Prop with "HA"). Qed.

Theorem all_disjointM_spec : forall `{Foldable M} m,
    all_disjointSL (M_to_list m) ⊢ ⌜ all_disjoint (M_to_list m) ⌝.
Proof. iIntros "* HA". iApply (all_disjoint_SL_to_Prop with "HA"). Qed.


Lemma all_disjointMSL_vector `{Foldable V} : forall (acc : VECTOR (V span)) (v : V span),
    all_disjointMSL v ∗ all_disjointMSL acc ⊢ all_disjointMSL (add acc v).
Proof.
  intros acc. destruct acc as [[cap size] VEC]. revert cap size VEC.
  induction values; simpl; intros.
  - iIntros. iNorm. unfold all_disjointMSL, all_disjointSL.
    simpl. destruct H. simpl. edestruct add_vector_list.
    erewrite H. simpl. iFrame. auto.
  - iIntros. iNorm. unfold all_disjointMSL, all_disjointSL.
    simpl. destruct H. simpl. edestruct add_vector_list.
    erewrite H. simpl. rewrite foldr_app. simpl.
    iDestruct "HC" as "[HC HD]". iFrame. simpl_list.
    iDestruct (IHvalues with "[HB HD]") as "HB". iFrame.
    unfold all_disjointMSL, all_disjointSL. simpl.
    edestruct add_vector_list. erewrite H0. simpl.
    rewrite foldr_app.
    simpl. simpl_list. iApply "HB".
    Unshelve.
    3 : { constructor. simpl. reflexivity.
          simpl. reflexivity. }
Qed.
