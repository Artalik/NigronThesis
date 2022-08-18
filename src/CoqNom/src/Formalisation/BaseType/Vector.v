From Classes Require Import Foldable.
From Equations Require Import Equations.
From stdpp Require Import numbers list.

Module Values.

  Open Scope N_scope.

  Definition values X := list (N * X).

  Fixpoint lookup {X} (v : values X) (pos : N) : option X :=
    match v with
    | [] => None
    | (k,v) :: t => if k =? pos then Some v else lookup t pos
    end.

  Fixpoint set {X} (vs : values X) (pos : N) (value : X) : values X :=
    match vs with
    | [] => (pos, value) :: []
    | (k, v) :: t =>
        match N.eq_dec k pos with
        | left _ => (k, value) :: t
        | right _ => (k, v) :: set t pos value
        end
    end.

  Fixpoint size {X} (vs : values X) : N :=
    match vs with
    | [] => 0
    | (k, v) :: t =>
        N.succ k `max` (size t)
    end.

  Lemma set_size : forall A (vs : values A) pos v,
      size (set vs pos v) = size vs `max` (N.succ pos).
  Proof.
    induction vs.
    - intros. simpl. apply N.max_comm.
    - intros pos v. simpl. destruct a.
      destruct (N.eq_dec n pos).
      + simpl. subst. rewrite <- N.max_comm. rewrite <- N.max_assoc.
        rewrite N.max_id. reflexivity.
      + simpl. rewrite <- N.max_assoc. f_equal. apply IHvs.
  Defined.


  Global Instance Foldable_Values : Foldable values.
  econstructor. intros. destruct sg, H.
  eapply list.foldr. intros c b. eapply (f b (X c.2)). eapply mempty. eapply X0.
  Defined.


  Lemma values_size : forall X (l : Values.values X),
      0 < Values.size l ->
      exists v, Values.lookup l (Values.size l - 1) = Some v.
  Proof.
    induction l; simpl; intros.
    - lia.
    - destruct a.
      destruct (n =? N.succ n `max` Values.size l - 1) eqn:?. exists x. reflexivity.
      eapply N.eqb_neq in Heqb. revert H Heqb. eapply N.max_case.
      + intros P IH. rewrite <- N.pred_sub in IH. rewrite N.pred_succ in IH.
        contradiction IH. auto.
      + intros P IH. apply IHl in P. exact P.
  Qed.


  Lemma size_add : forall A vs (pos : N) (v : A),
      size vs <= pos ->
      Values.set vs pos v = vs ++ [(pos, v)].
  Proof.
    induction vs; simpl in *.
    - intros. reflexivity.
    - intros pos v LE. destruct a.
      destruct (N.eq_dec n pos).
      + subst. lia.
      + rewrite IHvs. reflexivity. lia.
  Qed.

  Close Scope N_scope.

End Values.

Import Values.

Open Scope N_scope.

Definition lt_dec (n0 n1 : N) : {n0 < n1} + {n1 <= n0}.
  destruct (N.ltb n0 n1) eqn:P.
  - apply N.ltb_lt in P. left. exact P.
  - apply N.ltb_ge in P. right. exact P.
Defined.

(* =vector= *)
Record vector A :=
  mk_vector { capacity : N; size : N; values : values A }.
(* =end= *)

Arguments capacity {A}.
Arguments size {A}.
Arguments values {A}.

Structure Vector {A} (vec : vector A) :=
  properties_vector {
      Size_wf : Values.size (values vec) = size vec;
      Capacity_wf : size vec <= capacity vec
    }.

Definition VECTOR A := {arr : vector A | Vector arr}.

Equations make (A : Type) (n : N) : VECTOR A :=
  make A n := exist _ (mk_vector A n N0 []) _.
Next Obligation.
  econstructor; simpl in *.
  reflexivity.
  eapply N.le_0_l.
Defined.

Equations set {A} (vec : VECTOR A) (pos : N) (v : A) : VECTOR A by wf (N.to_nat (N.succ pos - capacity (`vec))) lt :=
  set vec pos v :=
    let cap := capacity (`vec) in
    match lt_dec pos cap with
    | right _ =>
        let arr := exist _ (mk_vector A (cap + ((cap / 2) `max` 1)) (size (`vec)) (values (`vec))) _ in
        set arr pos v
    | left _ =>
        let size := N.succ pos `max` size (`vec) in
        exist _ (mk_vector A (capacity (`vec)) size (Values.set (values (`vec)) pos v)) _
    end.
Next Obligation.
  destruct vec as [vec Vec]. destruct Vec.
  constructor; simpl in *.
  - rewrite <- Size_wf0. clear Size_wf0. induction (values vec). simpl in *. reflexivity.
    simpl. destruct a. destruct (N.eq_dec n pos).
    + subst. simpl. rewrite N.max_assoc. rewrite N.max_id. reflexivity.
    + simpl in * . rewrite IHv0. do 2 (rewrite N.max_assoc). f_equal.
      rewrite N.max_comm. reflexivity.
  - eapply N.max_lub_iff. split. eapply N.le_succ_l. exact l. eapply Capacity_wf0.
Defined.
Next Obligation.
  destruct vec as [vec Vec]. destruct Vec.
  econstructor; simpl in *.
  - exact Size_wf0.
  - etransitivity. eapply Capacity_wf0. eapply N.le_add_r.
Defined.
Next Obligation.
  intros. simpl. lia.
Defined.

Global Transparent make.
Global Transparent set.

Definition test_perf0 := make N 10.

Compute test_perf0.

Definition test_perf_test :=
  let vec := make N 10 in
  set vec 10000 10.

Compute test_perf_test.

Definition add {A} (vec : VECTOR A) (v : A) : VECTOR A := set vec (size (`vec)) v.


Definition test_perf_test_suite :=
  add (add (add test_perf_test 10) 8) 0.

Compute test_perf_test_suite.

Definition get {A} (vec : VECTOR A) (pos : N) : option A := lookup (values (`vec)) pos.

Fixpoint list_to_vector_aux {X} (l : list X) (vec : VECTOR X) :=
  match l with
  | [] => vec
  | h :: t => list_to_vector_aux t (add vec h)
  end.

Definition list_to_vector {X} (l : list X) :=
  list_to_vector_aux l (Vector.make X 10).

Definition vector_to_list {X} (vec : VECTOR X) : list (N * X) := Vector.values (`vec).

Notation "'[]↓' vec" := (vector_to_list vec)(at level 20).

Definition eq_dec_option {X} (comp : ∀ x y : X, {x = y} + {x ≠ y})
           (x y : option X) : {x = y} + {x ≠ y}.
Proof.
  destruct x,y.
  - destruct (comp x x0) as [eq|neq].
    + left. f_equal. exact eq.
    + right. intro some. eapply neq. eapply Some_inj in some. exact some.
  - right. intro neq. eapply Some_ne_None. exact neq.
  - right. intro neq. eapply None_ne_Some. exact neq.
  - left. reflexivity.
Defined.

Definition eqb_option {X} (comp : ∀ x y : X, {x = y} + {x ≠ y})
           (x y : option X) : bool :=
  proj1_sig (Sumbool.bool_of_sumbool (eq_dec_option comp x y)).

Equations ext_eq_aux {X} (comp : ∀ x y : X, {x = y} + {x ≠ y})
          (a1 a2 : Values.values X) (n : N) : bool by wf (N.to_nat n) lt :=
  ext_eq_aux comp a1 a2 0 :=
    eqb_option comp (lookup a1 0) (lookup a2 0);
  ext_eq_aux comp a1 a2 n :=
    andb (eqb_option comp (lookup a1 n) (lookup a2 n)) (ext_eq_aux comp a1 a2 (N.pred n)).
Next Obligation.
  lia.
Defined.

Definition ext_eq {X} (comp : ∀ x y : X, {x = y} + {x ≠ y}) (a1 a2 : VECTOR X) : bool :=
  if size (`a1) =? size (`a2)
  then
    ext_eq_aux comp (values (`a1)) (values (`a2)) (size (`a1))
  else
    false.

Global Instance Foldable_vector : Foldable VECTOR.
econstructor.
intros M sg m A f vec. destruct sg. destruct m.
eapply foldr. intros a b. eapply (f0 (f a.2) b). eapply mempty. eapply (vector_to_list vec).
Defined.

Global Instance Foldable_Vector `{Foldable M}: Foldable (fun X => VECTOR (M X)).
econstructor.
intros M0 sg m0 A f vec. destruct H. destruct sg.
destruct Foldable_vector.
eapply foldMap0. eapply m0.
intros ma. eapply foldMap. eapply m0. eapply f. eapply ma. eapply vec.
Defined.

Close Scope N_scope.


Lemma set_vector_list : forall (pos : N) A (vec : VECTOR A) v,
  ∃ n : N, []↓Vector.set vec pos v = match Vector.lt_dec pos (Vector.size (`vec)) with
                                     | left _ => []↓Vector.set vec pos v
                                     | right _ => []↓vec ++  [(n,v)]
                                     end.
Proof.
  intros pos A vec v. destruct (Vector.lt_dec pos (size (`vec))).
  exists pos. reflexivity.
  exists pos. revert l. eapply Vector.FunctionalElimination_set. clear pos A v vec.
  intros A vec pos v IH size_pos P0 P1. simpl in *.
  destruct (Vector.lt_dec pos (Vector.capacity (`vec))).
  - destruct vec as [vec Vec]. simpl in *. destruct Vec. unfold vector_to_list.
    eapply size_add. simpl in *. lia.
  - eapply P0; auto.
Qed.


Lemma add_vector_list : forall A (v :A) (vec : VECTOR A),
  exists n, []↓add vec v = []↓vec ++ [(n,v)].
Proof.
  intros A v vec. edestruct (set_vector_list (Vector.size (`vec)) A vec v).
  exists x. unfold Vector.add. rewrite H.
  destruct (Vector.lt_dec (size (`vec)) (size (`vec))). lia.
  reflexivity.
Qed.
