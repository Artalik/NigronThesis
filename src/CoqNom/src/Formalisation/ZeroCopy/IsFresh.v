From SepLogic Require Export SepBasicCore SepSet.
From Classes Require Import Foldable.
From Equations Require Import Equations.
From Formalisation Require Import Span Inject disjoint.

Definition iProp := monPred biInd hpropI.

Open Scope N_scope.

Fail
(* =IsFresh_aux= *)
Equations IsFresh_aux (pos : N) (len : N): iProp :=
  IsFresh_aux pos 0 := emp;
  IsFresh_aux pos len := & pos ∗ IsFresh_aux (succ pos) (pred len).
(* =end= *)

Equations IsFresh_aux (pos : N) (len : N): iProp by wf (N.to_nat len) lt :=
  IsFresh_aux pos 0 := emp;
  IsFresh_aux pos len :=
    & pos ∗ IsFresh_aux (N.succ pos) (N.pred len).
Next Obligation.
  intros. lia.
Defined.

(* =IsFresh= *)
Definition IsFresh (s : span) := IsFresh_aux (pos s) (len s).
(* =end= *)

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
      eapply in_seq in H0. eapply elem_of_singleton_1 in H. lia.
    + iSplitL "HA".
      * iApply big_sepS_singleton. iApply "HA".
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
  - simpl; iIntros. unfold disjoint, set_span.
    rewrite (inject_empty p0); auto. simpl. lia.
  - simpl; iIntros. iNorm. iDestruct (IsFresh_len_succ with "HC") as "[HA HB]".
    iDestruct (single_IsFresh with "HA HE") as "%".
    iDestruct (IHl0 with "HB HE") as "%". simpl in H0. iPureIntro.
    unfold disjoint, set_span; simpl.
    rewrite <- N.add_succ_comm. rewrite inject_add. 2 : lia.
    apply disjoint_union_l. split.
    + rewrite inject_singleton. apply disjoint_singleton_l. apply H.
    + eapply H0.
Qed.

Fail
(* =IsFresh_spec= *)
Lemma IsFresh_spec : forall s t, IsFresh s ∗ IsFresh t ⊢ ⌜disjoint s t⌝.
(* =end= *)

(* =M_to_list= *)
Definition M_to_list `{Foldable M} {X} (m : M X) : list X :=
  Foldable.foldr _ _ (fun a b => a :: b) [] m.
(* =end= *)

(* =all_disjointSL= *)
Definition all_disjointSL (l : list span) := [∗ list] v ∈ l, IsFresh v.
(* =end= *)

(* =all_disjointMSL= *)
Definition all_disjointMSL `{Foldable M} (m : M span) : iProp :=
  all_disjointSL (M_to_list m).
(* =end= *)

(* =all_disjointM= *)
Definition all_disjointM `{Foldable M} (m : M span) : Prop :=
  all_disjoint (M_to_list m).
(* =end= *)

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

(* =all_disjoint_spec= *)
Lemma all_disjoint_spec : forall l, all_disjointSL l ⊢ ⌜ all_disjoint l ⌝.
(* =end= *)
Proof.
  iIntros. iApply all_disjoint_SL_to_Prop. auto.
Qed.

Theorem all_disjointM_SL_to_Prop : forall `{Foldable M} m,
    <absorb> all_disjointMSL m ⊢ ⌜ all_disjointM m ⌝.
Proof. iIntros "* HA". iApply (all_disjoint_SL_to_Prop with "HA"). Qed.

(* =all_disjointM_spec= *)
Theorem all_disjointM_spec `{Foldable M} m :
    all_disjointMSL m ⊢ ⌜ all_disjointM m ⌝.
(* =end= *)
Proof. iIntros "* HA". iApply (all_disjoint_SL_to_Prop with "HA"). Qed.
