From stdpp Require Import numbers.
From Equations Require Import Equations.
From SepLogic Require Export SepBasicCore SepSet.

Open Scope N_scope.

Equations seq (start len : N) : list N by wf (N.to_nat len) lt:=
  seq start 0 := nil;
  seq start pos :=
    start :: seq (N.succ start) (N.pred pos).
Next Obligation.
  intros. lia.
Defined.

Lemma seq_app : ∀ len1 len2 start : N,
    seq start (len1 + len2) = seq start len1 ++ seq (start + len1) len2.
Proof.
  intro len1; induction len1 as [|len1' IHlen] using N.peano_ind; intros; simpl in *.
  - now rewrite N.add_0_r.
  - rewrite N.add_succ_l. rewrite <- N.add_succ_r.
    rewrite IHlen. rewrite <- (N.add_1_r len1').
    rewrite IHlen. rewrite <- app_assoc. f_equal.
    rewrite N.one_succ. rewrite <- N.succ_pos_spec.
    rewrite seq_equation_2. rewrite N.succ_pos_spec. rewrite N.pred_succ.
    rewrite <- (N.succ_pos_spec 0).
    rewrite seq_equation_2. rewrite N.succ_pos_spec. rewrite N.pred_succ.
    rewrite <- app_comm_cons. f_equal. rewrite seq_equation_1. simpl.
    f_equal. lia.
Qed.

Lemma in_seq : ∀ len start n : N, List.In n (seq start len) ↔ start <= n < start + len.
  intros. revert start. induction len as [|len IHlen] using N.peano_ind; simpl; intros start.
  - rewrite N.add_0_r. split;[easy|].
    intros (H,H'). apply (N.lt_irrefl start).
    eapply N.le_lt_trans; eassumption.
  - rewrite <- N.succ_pos_spec. rewrite seq_equation_2.
    rewrite N.succ_pos_spec. rewrite N.pred_succ. split.
    + intros [P|P]; subst; intuition.
      * lia.
      * eapply IHlen in P. lia.
      * eapply IHlen in P. lia.
    + intros [P0 P1]. destruct (start =? n) eqn:?.
      * eapply N.eqb_eq in Heqb. constructor. auto.
      * right. eapply N.eqb_neq in Heqb. eapply IHlen. lia.
Qed.

Definition inject_aux start n := seq start (n - start).

Definition inject (start : N) (fin : N) : gset N :=
  list_to_set (inject_aux start fin).

Definition injectSL (start : N) (fin : N) := [∗ set] n ∈ inject start fin, & n.

Lemma inject_aux_add : forall n start s,
    start <= s ->
    inject_aux start (s + n) = inject_aux start s ++ inject_aux s (s + n).
Proof.
  induction n using N.peano_ind; intros.
  - rewrite N.add_0_r. unfold inject_aux. rewrite N.sub_diag.
    simpl. simpl_list. reflexivity.
  - rewrite N.add_succ_r. rewrite <- N.add_succ_l. rewrite IHn.
    unfold inject_aux. rewrite (N.sub_succ_l _ s). 2-3 : lia.
    rewrite <- N.add_1_r. rewrite seq_app.
    rewrite N.add_sub_assoc. rewrite N.add_comm. rewrite <- N.add_sub_assoc.
    rewrite N.sub_diag. rewrite <- app_assoc. f_equal. rewrite N.add_0_r.
    rewrite N.add_comm. rewrite <- N.add_sub_assoc.
    rewrite N.sub_diag. rewrite N.add_0_r.
    rewrite <- N.add_sub_assoc. rewrite N.sub_succ_l. rewrite N.sub_diag.
    2-6 : lia. rewrite N.add_comm. rewrite seq_app. f_equal. f_equal. lia.
Qed.

Lemma inject_add_aux : forall (l1 l2 : list N),
    l1 ## l2 -> (list_to_set (l1 ++ l2) : gset N) = list_to_set l1 ∪ list_to_set l2.
Proof.
  induction l1; intros.
  - simpl. rewrite union_empty_l_L. reflexivity.
  - simpl. rewrite <- union_assoc_L. f_equal. apply IHl1.
    repeat intro. eapply H.  2 : eauto. constructor. apply H0.
Qed.

Lemma inject_mono_r : forall s f1 f2,
    (f1 <= f2)%N ->
    inject s f1 ⊆ inject s f2.
Proof.
  intros.
  unfold inject, inject_aux.
  repeat intro. apply elem_of_list_to_set. apply elem_of_list_to_set in H0.
  apply elem_of_list_In. apply elem_of_list_In in H0.
  apply in_seq in H0. apply in_seq. lia.
Qed.

Lemma inject_mono_l : forall s1 s2 f ,
    (s1 <= s2)%N ->
    inject s2 f ⊆ inject s1 f.
Proof.
  intros.
  unfold inject, inject_aux.
  repeat intro. apply elem_of_list_to_set. apply elem_of_list_to_set in H0.
  apply elem_of_list_In. apply elem_of_list_In in H0.
  apply in_seq in H0. apply in_seq. lia.
Qed.

Lemma inject_sup_aux_aux : forall l x,
    x ∈ (list_to_set l : gset N) ->
    x ∈ l.
Proof.
  induction l.
  - intros. inversion H.
  - intros. destruct (N.eq_dec x a).
    + subst. constructor.
    + constructor. apply IHl.
      rewrite list_to_set_cons in H. apply elem_of_union in H.
      destruct H. apply elem_of_singleton_1 in H. subst. contradiction. apply H.
Qed.

Lemma inject_sup_aux : forall l1 l2,
    (list_to_set l1 : gset N) ⊆ list_to_set l2 ->
    l1 ⊆ l2.
Proof.
  induction l1 as [ | x l1 IH].
  - intros. apply list_subseteq_nil.
  - intros. intros x' IHl1. inversion IHl1.
    + subst. assert (x ∈ (list_to_set (x :: l1) : gset N)).
      * rewrite list_to_set_cons. apply elem_of_union_l. eapply elem_of_singleton_2; auto.
      * apply H in H0. apply inject_sup_aux_aux. apply H0.
    + subst. apply IH; auto.
      intros v vIH. apply H. rewrite list_to_set_cons. apply elem_of_union_r. auto.
Qed.

Lemma inject_add_disjoint : forall v fin, {[v]} ## inject (N.succ v) fin.
Proof.
  unfold inject, inject_aux. repeat intro.
  apply elem_of_singleton_1 in H. subst.
  apply inject_sup_aux_aux in H0.
  apply elem_of_list_In in H0. eapply in_seq in H0. lia.
Qed.

Lemma inject_aux_disjoint : forall start int fin, inject_aux start int ## inject_aux int fin.
Proof.
  intros start int fin p H H0.
  unfold inject_aux in H. unfold inject_aux in H0.
  apply elem_of_list_In in H. apply elem_of_list_In in H0.
  apply in_seq in H. apply in_seq in H0. lia.
Qed.

Lemma inject_disjoint : forall start int fin, inject start int ## inject int fin.
Proof.
  unfold inject, inject_aux. repeat intro.
  apply inject_sup_aux_aux in H. apply inject_sup_aux_aux in H0.
  apply elem_of_list_In in H. apply elem_of_list_In in H0.
  apply in_seq in H. apply in_seq in H0. lia.
Qed.

Lemma inject_aux_add_head : forall fin start,
    start < fin ->
    inject start fin = {[start]} ∪ inject (N.succ start) fin.
Proof.
  unfold inject, inject_aux. intros.
  rewrite <- list_to_set_cons. f_equal.
  pose H. apply N.sub_gt in l.
  assert (forall n, n <> 0 -> ∃ v, n = N.succ v).
  - intros. exists (n - 1). lia.
  - apply H0 in l as [v P]. rewrite P. rewrite <- N.succ_pos_spec.
    rewrite seq_equation_2. rewrite N.succ_pos_spec. rewrite N.pred_succ.
    f_equal. f_equal; lia.
Qed.

Lemma inject_add : forall n start s,
    start <= s ->
    inject start (s + n) = inject start s ∪ inject s (s + n).
Proof.
  intros. pose H. eapply (inject_aux_add n) in l. unfold inject.
  rewrite <- inject_add_aux. f_equal. rewrite inject_aux_add; auto.
  apply inject_aux_disjoint.
Qed.

Lemma inject_union : forall int start fin,
    start <= int ->
    int <= fin ->
    inject start fin = inject start int ∪ inject int fin.
Proof.
  intros. epose H0. apply N.le_exists_sub in l as [p [P0 _]].
  rewrite P0. rewrite N.add_comm. rewrite inject_add. 2 : lia.
  reflexivity.
Qed.

Lemma inject_empty : forall v1 v2, v2 <= v1 -> inject v1 v2 = ∅.
Proof.
  intros. unfold inject, inject_aux.
  apply N.sub_0_le in H. rewrite H. simpl. reflexivity.
Qed.

Lemma injectSL_emp : forall v1 v2, v2 <= v1 -> ⊢ injectSL v1 v2 ∗-∗ emp.
Proof. intros. unfold injectSL. rewrite inject_empty; auto. Qed.

Lemma inject_singleton : forall pos, inject pos (N.succ pos) = {[pos]}.
Proof.
  intro pos. unfold inject, inject_aux.
  assert (N.succ pos - pos = 1) by lia. rewrite H. clear H.
  simpl. rewrite N.one_succ. rewrite <- N.succ_pos_spec.
  rewrite seq_equation_2. rewrite N.succ_pos_spec. rewrite N.pred_succ.
  simpl. rewrite seq_equation_1. rewrite union_empty_r_L. auto.
Qed.
