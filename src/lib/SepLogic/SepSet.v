From iris Require Export bi.bi proofmode.tactics proofmode.monpred.

From stdpp Require Export mapset gmap.


Section hprop.

  (* Operators *)

(* =hprop= *)
Definition hprop := gset positive -> Prop.
(* =end= *)

(* =entails= *)
Definition entails (P Q : hprop) : Prop := forall h, P h -> Q h.
(* =end= *)

Notation "P ==> Q" := (entails P Q).

(* =himpl= *)
Definition himpl (P Q : hprop) := (* P -> Q *)
  fun h => P h -> Q h.
(* =end= *)

(* =hand= *)
Definition hand (P Q : hprop) : hprop := (* P /\ Q *)
  fun h => P h /\ Q h.
(* =end= *)

(* =hor= *)
Definition hor (P Q : hprop) : hprop := (* P \/ Q *)
  fun h => P h \/ Q h.
(* =end= *)

(* =hempty= *)
Definition hempty : hprop := fun h => h = ∅.
(* =end= *)

(* =hsingle= *)
Definition hsingle `{Countable X} (l : X) : hprop :=
  fun h =>  h = {[ encode l ]}.
(* =end= *)

(* =set_ctx= *)
Definition set_ctx (ctx : gset positive) : hprop := fun h => h = ctx.
(* =end= *)

(* =hstar= *)
Definition hstar (P Q : hprop) : hprop :=
  fun h => exists h1 h2, P h1 /\ Q h2 /\ h1 ## h2 /\ h = h1 ∪ h2.
(* =end= *)

(* =hexist= *)
Definition hexist {A} (J : A -> hprop) : hprop := (* ∃ a, J *)
  fun h => exists a, J a h.
(* =end= *)

(* =hforal= *)
Definition hforal {A} (J : A -> hprop) : hprop := (* forall a, J *)
  fun h => forall a, J a h.
(* =end= *)

(* =hpure= *)
Definition hpure (P : Prop) : hprop := fun _ => P.
(* =end= *)

Definition hpure_aff (P:Prop) : hprop := fun h => P /\ hempty h.

Definition hwand (H1 H2 : hprop) : hprop :=
  hexist (fun (H:hprop) => (hstar H (hpure_aff ((hstar H H1) ==> H2)))).

Definition qwand A (Q1 Q2:A->hprop) :=
  hforal (fun x => hwand (Q1 x) (Q2 x)).

  Lemma hempty_intro : hempty ∅.
  Proof using. reflexivity. Qed.

  Local Notation "'empty'" := (∅ : gset positive).

  Local Notation "h1 \u h2" := (h1 ∪ h2) (at level 37, right associativity).

  Local Notation "'Hexists' x1 , H" := (hexist (fun x1 => H))
                                         (at level 39, x1 name, H at level 50).
  Local Notation "'Hexists' x1 x2 , H" := (Hexists x1, Hexists x2, H)
                                            (at level 39, x1 name, x2 name, H at level 50).
  Local Notation "'Hexists' x1 x2 x3 , H" := (Hexists x1, Hexists x2, Hexists x3, H)
                                               (at level 39, x1 name, x2 name, x3 name, H at level 50).

  Local Notation "'\[]'" := (hempty)
                              (at level 0).

  Local Notation "\[ P ]" := (hpure P)
                               (at level 0, P at level 99, format "\[ P ]").

  Local Notation "H1 '\*' H2" := (hstar H1 H2)
                                   (at level 41, right associativity).

  Ltac inversion_star h P :=
    match goal with
    | H : (_ \* _) _ |- _ =>
      let W := fresh h in
      let w := fresh P in
      inversion H as (W&w);
      let W := fresh h in
      destruct w as (W&w);
      do 3 (let w0 := fresh P in
            destruct w as (w0&w))
    end.

  Definition hpersistent (H:hprop) : hprop := fun _ => H ∅.

  Definition hlater (H : hprop) := H.

  Definition equiv (P0 P1 : hprop) := forall h, P0 h <-> P1 h.

  Instance equiv_hprop : Equiv hprop.
  Proof.
   intros P0 P1. apply (equiv P0 P1).
  Defined.

  Instance dist_hprop : Dist hprop.
  Proof.
    intros _ P0 P1. apply (equiv P0 P1).
  Defined.

  Program Canonical Structure testofe := @Ofe hprop _ _ _.
  Next Obligation.
    split.
    - intros; split; intros; auto. apply (H 0).
    - intros; split; repeat intro; auto.
      + split; intro; apply H; auto.
      + split; intro.
        apply H0. apply H. auto.
        apply H. apply H0. auto.
    - intros. intro. apply H.
  Defined.


  Program Canonical Structure hpropI : bi :=
    Bi hprop _ _ entails hempty hpure hand hor
       himpl (@hforal) (@hexist) hstar hwand hpersistent hlater _ _ _ _.
  Next Obligation.
    repeat split; try(solve_proper); eauto.
    - intros H h P. assumption.
    - rewrite /Transitive. intros. intros h P. eauto.
    - repeat intro. apply H. auto.
    - repeat intro. apply H. auto.
    - destruct H; intro; apply H; auto.
    - destruct H; intro; apply H0; auto.
    - intro; apply H; auto.
    - intro. apply H; auto.
    - destruct H1. apply H. auto.
    - apply H0. destruct H1. auto.
    - apply H. destruct H1. auto.
    - apply H0. destruct H1. auto.
    - intro. destruct H1. left. apply H. auto. right. apply H0. auto.
    - intro. destruct H1. left. apply H. auto. right. apply H0. auto.
    - repeat intro. apply H0. apply H1. apply H. auto.
    - repeat intro. apply H0. apply H1. apply H. auto.
    - repeat intro. apply H. apply H0.
    - repeat intro. apply H. apply H0.
    - repeat intro. edestruct H0. exists x0. apply H. apply H1.
    - repeat intro. edestruct H0. exists x0. apply H. apply H1.
    - intros. inversion_star h P. exists h0, h1. repeat split; auto. apply H; auto. apply H0; auto.
    - intros. inversion_star h P. exists h0, h1. repeat split; auto. apply H; auto. apply H0; auto.
    - rewrite /hwand. repeat intro. destruct H1. inversion_star h P.
      exists x1, h0, h1. destruct P1. repeat split; auto. repeat intro. inversion_star h P.
      apply H0. apply H2. exists h3, h4. repeat split; auto. apply H. auto.
    - rewrite /hwand. repeat intro. destruct H1. inversion_star h P.
      exists x1, h0, h1. destruct P1. repeat split; auto. repeat intro. inversion_star h P.
      apply H0. apply H2. exists h3, h4. repeat split; auto. apply H. auto.
    - intro. apply H. apply H0.
    - intro. apply H. apply H0.
    - rewrite /hpure. intros φ P imp h P0. apply imp; auto.
    - rewrite /hand. intros P Q h (P0&P1). apply P0.
    - rewrite /hand. intros P Q h (P0&P1). apply P1.
    - rewrite /hor. intros P Q h P0. auto.
    - rewrite /hor. intros P Q h P0. auto.
    - rewrite /hor. intros P Q h P0 P1 h0 P2. destruct P2; auto.
    - intros P Q R P0 h P2 P3. apply P0. split; auto.
    - intros P Q R P0 h P2. destruct P2. apply P0 in H. apply H in H0. auto.
    - intros x W a H h P h0. apply H. apply P.
    - intros h Q a H H0. apply H0.
    - intros x W H P Q. exists H. apply Q.
    - intros x W Q P h P0. destruct P0. eapply P. apply H.
    - intros P P' Q Q' A B C D. inversion_star h P. exists h; exists h0. repeat split; auto.
    - intros x W A. exists empty; exists W. repeat split; auto.
      apply disjoint_empty_l. rewrite union_empty_l_L. auto.
    - intros P h Q. inversion_star H H. inversion H3. subst.
      rewrite union_empty_l_L. apply H4.
    - intros P Q h R. inversion_star H H. exists H2; exists H0. repeat split; auto. subst.
      apply union_comm_L.
    - intros P Q R h P0. inversion_star h P. clear P0. inversion_star h P. clear P2.
      exists h2. exists (h3 ∪ h1). repeat split; auto. exists h3, h1. repeat split; auto.
      subst. eapply disjoint_union_l; eauto. eapply disjoint_union_r. subst.
      split; auto. eapply disjoint_union_l. rewrite union_comm. eauto.
      subst. rewrite union_assoc_L. auto.
    - intros P Q R P0 h P1. exists P. exists h; exists empty. repeat split; auto.
      apply disjoint_empty_r. rewrite union_empty_r_L. auto.
    - intros P Q R W h P0. inversion_star h P. apply W in P2. destruct P2. inversion_star h H.
      inversion H2. apply H4. exists h2; exists h1. repeat split; auto; subst.
      + apply disjoint_union_l in P4. apply P4.
      + inversion H5. subst. rewrite union_empty_r_L. auto.
    - rewrite /hpersistent. intros P Q H h P0. apply H. apply P0.
    - rewrite /hpersistent in H. rewrite /hand in H. destruct H. exact H.
    - rewrite /hpersistent in H. rewrite /hand in H. destruct H. exact H0.
    - rewrite /hpersistent. intros P Q h P0. inversion_star h P0. apply P2.
    - intros P Q x W. destruct W. exists empty; exists x. repeat split; auto.
      apply disjoint_empty_l. rewrite union_empty_l_L. auto.
  Defined.
  Next Obligation.
    repeat split; try(solve_proper); eauto.
    - intro. apply H. auto.
    - intro. apply H. auto.
    - intros A Φ h a. rewrite /hlater. unfold hforal in *. unfold hlater in a. apply a.
    - intros A Φ h a. rewrite /hor. unfold hlater in *. destruct a. right. exists x. apply H.
    - intros Hp h P. unfold hlater in *. right. intro. apply P.
  Defined.

  Instance inhabited_unit : Inhabited unit.
  Proof.
    split. apply ().
  Qed.

  Instance PreOrder_unit : PreOrder (fun (t1 t2 : unit) => t1 = t2).
  Proof.
    split; repeat red; intros; trivial. destruct x,y,z. reflexivity.
  Qed.

  Program Canonical Structure biInd := BiIndex unit inhabited_unit _ PreOrder_unit.

  Definition single `{Countable X} (l : X) : @monPred biInd hpropI
    := MonPred (fun _ => hsingle l) _.

  Definition ctx (h : gset positive) : monPred biInd hpropI := MonPred (fun _ => set_ctx h) _.

  Ltac inv H := inversion H; clear H; subst.

  Local Open Scope bi_scope.

  Local Notation "'&&' l" :=
    (ctx l) (at level 20) : bi_scope.

Local Notation "'&' l" :=
  (single l) (at level 20) : bi_scope.

(* =singleton_neq= *)
Lemma singleton_neq `{Countable X} : forall (l l' : X), ⊢ & l -∗ & l' -∗ ⌜l ≠ l'⌝.
(* =end= *)
Proof.
  MonPred.unseal. rename H into count.
  split. MonPred.unseal. repeat red. intros. destruct i. destruct a. clear H0.
  inv H. exists emp, empty, empty. repeat split; auto.
  intros h H j C. clear C. clear j. inversion_star h P. clear H. inv P0. clear P2.
  red in P1. rewrite union_empty_l_L. exists (set_ctx h1), h1, empty.
  repeat split; eauto. subst. intros h H eq. inversion_star h P. clear H.
  red in P1. red in P0. subst. erewrite disjoint_singleton_l in P2. apply P2.
  apply lookup_singleton. apply disjoint_empty_r. rewrite union_empty_r_L. auto.
  apply disjoint_empty_r. rewrite union_empty_r_L. auto.
Qed.

Fail
(* =singleton_neq_2= *)
Lemma singleton_neq `{Countable X} : forall (v t : X), & v ∗ & t ⊢ ⌜v ≠ t⌝.
(* =end= *)
(* Proof. iIntros (v t) "[HA HB]". iApply (singleton_neq with "HA HB"). Qed. *)

  Lemma emp_trivial : ⊢ (emp : monPred biInd hpropI). simpl. auto. Qed.

  Global Instance affine_heap_empty : Affine (ctx ∅).
  Proof.
    split. intro. MonPred.unseal. repeat red. intros. apply H.
  Qed.

  Lemma init_heap : ⊢ ctx ∅.
  Proof.
    split. MonPred.unseal. repeat red. intros. apply H.
  Qed.


  Global Instance iPropBiPureForall : BiPureForall (monPredI biInd hpropI).
    constructor. MonPred.unseal. repeat red. intros. apply H.
  Qed.

  Global Instance iPropBiPersistentForall : BiPersistentlyForall (monPredI biInd hpropI).
  constructor. MonPred.unseal. repeat red. intros. eapply H.
  Qed.

  Global Instance iPropBiPositivei : BiPositive (monPredI biInd hpropI).
  constructor. MonPred.unseal. repeat red. intros.
  repeat red in H. destruct H. inversion H. subst. red in H0. inversion_star h P.
  assert (h = ∅). set_solver. assert (h0 = ∅). set_solver. subst.
  exists ∅, ∅. repeat split; auto.
  Qed.


  Lemma instance_heap : forall (P : monPred biInd hpropI) (Q : Prop), (forall tmps, P () tmps -> Q) -> (P ⊢ ⌜Q⌝).
  Proof.
    MonPred.unseal. intros. split. repeat red. intros.
    eapply H. destruct i. eapply H0.
  Qed.

  Lemma soundness_pure_2 h (Φ : Prop) : (⌜ Φ ⌝ : monPred biInd hpropI) () h -> Φ.
  Proof. MonPred.unseal. auto. Qed.


(* =soundness_pure= *)
Lemma soundness_pure h (P : Prop) : (&& h ⊢ ⌜ P ⌝) -> P.
(* =end= *)
Proof.
  MonPred.unseal=> -[H]. repeat red in H.
  pose (e := H () h). eapply e. reflexivity.
Qed.


Lemma pure_soundness (Φ : Prop) : (⊢ ⌜ Φ ⌝ : monPred biInd hpropI) -> Φ.
Proof.
  intros. eapply (soundness_pure ∅). iIntros "_". iApply H.
Qed.

  Definition iProp := monPred biInd hpropI.

  Lemma soundness (Φ : iProp) h : (⊢&& h -∗ Φ) -> Φ () h.
  Proof.
    MonPred.unseal=> -[H]. repeat red in H.
    pose (e := H () ∅).
    simpl in *. edestruct e.
    - MonPred.unseal. reflexivity.
    - repeat red. repeat split; auto.
    - inversion_star h P. inversion P1. apply H1. exists empty; exists h.
      inversion H2; subst. rewrite union_empty_r_L in P; subst.
      repeat split; auto. apply disjoint_empty_l. rewrite union_empty_l_L. auto.
  Qed.

  Lemma completeness (Φ : iProp) h : Φ () h -> (⊢&& h -∗ Φ).
  Proof.
    MonPred.unseal. split. MonPred.unseal. simpl. repeat red. intros. exists emp. exists h0; exists empty.
    repeat split; auto.
    intros h1 P0. inversion_star h P. simpl in *. rewrite <- P2 in *. inversion P1.
    subst. rewrite union_empty_l_L. rewrite <- P2. destruct a. apply H.
    apply disjoint_empty_r. rewrite union_empty_r_L. auto.
  Qed.

  Lemma equivalence (Φ : iProp) h : Φ () h <-> (&& h ⊢ Φ).
  Proof.
    split.
    intros. iIntros "HA". iApply completeness; eauto.
    intros. apply soundness. iIntros "HA". iApply (H with "HA").
  Qed.

  Lemma heap_ctx_split (h h' : gset positive) : h ## h' -> (⊢&& (h \u h') -∗ && h ∗ && h').
  Proof.
    MonPred.unseal. split. MonPred.unseal. repeat red.
    intros. exists hempty. inversion H0; subst.
    exists empty; exists empty. repeat split; auto.
    + repeat intro. inversion_star h P. inversion P1. subst.
      exists h; exists h'. repeat split; auto. inversion P0; subst.
      rewrite union_empty_l_L. reflexivity.
    + apply disjoint_empty_l.
    + rewrite union_empty_l_L. reflexivity.
  Qed.

  Lemma heap_ctx_split_2 (h h' : gset positive) : h ## h' -> (⊢&& h ∗ && h' -∗ && (h \u h')).
  Proof.
    MonPred.unseal. split. MonPred.unseal. repeat red.
    intros. exists hempty. inversion H0; subst.
    exists empty; exists empty. repeat split; auto.
    + repeat intro. inversion_star h P. clear H2. inversion P0. subst. clear P2. clear P0.
      rewrite union_empty_l_L. red in P1. inversion_star h P. clear P1.
      inversion P0. inversion P2. subst. reflexivity.
    + apply disjoint_empty_l.
    + rewrite union_empty_l_L. reflexivity.
  Qed.

  Lemma heap_ctx_split_sing (h : gset positive) l : h ## ({[ l ]}) ->
                                             (⊢&& ({[ l ]} \u h) -∗ && h ∗ & l).
  Proof.
    iIntros (?) "HA". iApply heap_ctx_split; auto. rewrite union_comm_L. auto.
  Qed.

  Lemma heap_ctx_split_sing_2 (h : gset positive) l : h ## ({[ l ]}) ->
                                             (&& h ∗ & l ⊢&& ({[ l ]} \u h) ).
  Proof.
    iIntros (?) "[HA HB]". iApply heap_ctx_split_2; auto. iFrame.
  Qed.


  Lemma big_op_ctx h : && h ⊣⊢ [∗ set] v ∈ h, & v.
  Proof.
    induction h as [| y h not_in IH] using set_ind_L.
    - iSplit; auto. iIntros "HA". iDestruct (big_sepS_empty with "HA") as "_". iApply init_heap.
    - iSplit; auto.
      + iIntros "HA". iDestruct (heap_ctx_split_sing with "HA") as "[HA HB]". set_solver.
        iApply big_sepS_union. set_solver.
        iSplitL "HB". iApply (big_sepS_singleton with "HB").
        iApply (IH with "HA").
      +  iIntros "HA". iDestruct (big_sepS_union with "HA") as "[HA HB]". set_solver.
        iApply heap_ctx_split_sing_2. set_solver.
        iSplitL "HB". iApply (IH with "HB"). iApply big_sepS_singleton. iFrame.
  Qed.

  Lemma encode_singleton `{Countable X}: forall (v :X), & (encode v) ⊣⊢ & v.
  Proof.
    split. repeat red. intros. split; intros.
    - unfold hpropI in *. simpl in *. unfold hsingle in *.
      unfold pos_countable in *. unfold encode in *. simpl in *. auto.
    - unfold hpropI in *. simpl in *. unfold hsingle in *.
      unfold pos_countable in *. unfold encode in *. simpl in *. auto.
  Qed.

End hprop.

Notation "'empty'" := (∅ : gset).

Notation "'\[]'" := (hempty) (at level 0).

Notation "\[ P ]" := (hpure P) (at level 0, P at level 99, format "\[ P ]").

Notation "H1 '\*' H2" := (hstar H1 H2) (at level 41, right associativity).

Ltac inversion_star h P :=
  match goal with
  | H : (_ \* _) _ |- _ =>
    let W := fresh h in
    let w := fresh P in
    inversion H as (W&w);
    let W := fresh h in
    destruct w as (W&w);
    do 3 (let w0 := fresh P in
          destruct w as (w0&w))
  end.

Open Scope bi_scope.

Notation "'&' l" :=
  (single l) (at level 20).

Notation "'&&' h" :=
  (ctx h) (at level 20).
