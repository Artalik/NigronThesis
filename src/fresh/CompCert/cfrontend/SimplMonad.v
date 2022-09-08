Require Import FunctionalExtensionality.
Require Import Errors.
Require Import SepSet.
Require Import Ctypes.
Require Export FreeMonad.

Definition ident := positive.

Record generator : Type := mkgenerator { gen_next : ident;
                                         gen_trail: list (ident * type)
                             }.

Parameter first_unused_ident : unit -> ident.

Definition initial_generator (x : unit) : generator :=
  mkgenerator (first_unused_ident x) nil.

Inductive MON : Type -> Type :=
| errorOp : Errors.errmsg -> forall {X}, MON X
| gensymOp : type -> MON ident
| trailOp : unit -> MON (list (ident * type)).

Definition mon := Free MON.

Definition error {X} (e : Errors.errmsg) : mon X := gen (errorOp e).
Definition gensym (t : type) : mon ident := gen (gensymOp t).
Definition trail (_ : unit): mon (list (ident * type)) := gen (trailOp tt).

Definition wp {X} (e : mon X) (Q : X -> iProp) : iProp.
  revert X e Q. fix wp 2. intros X e Q. destruct e as [T x|T e|T1 T2 m f].
  (* ret *)
  - eapply (Q x).
  - destruct e.
    (* error *)
    + eapply True.
    (* gensym *)
    + eapply (∀ l, & l -∗ Q l).
    (* trail *)
    + eapply (∀ l, Q l).
  (* bind *)
  - eapply (wp T1 m (fun x => wp T2 (f x) Q)).
Defined.

Notation "'{{' P } } e {{ v ; Q } }" := (P ⊢ wp e (fun v => Q))
                                          (at level 20,
                                            format "'[hv' {{  P  } }  '/  ' e  '/'  {{  v ;  Q  } } ']'").

(** triple rules *)

Lemma wp_consequence : forall {X} (P Q : X -> iProp) (f : mon X),
    ⊢ wp f P -∗
      (∀ x, P x -∗ Q x) -∗
      wp f Q.
Proof.
  induction f as [v | Y [] |]; simpl; intros; auto.
  - iIntros "HA HB". iApply ("HB" with "HA").
  - iIntros "HA * HB * HC". iApply "HB". iApply ("HA" with "HC").
  - iIntros "HA HB *". iApply "HB". iApply "HA".
  - iIntros "HA HB". iApply (IHf with "HA"). iIntros (x) "HA". iApply (H with "HA HB").
Qed.

Lemma wp_bind {X Y} (e : mon X) (f :  X → mon Y) (Q : Y -> iProp)  (Q' : X -> iProp) :
  wp e Q' ⊢ (∀ v,  Q' v -∗ wp (f v) Q ) -∗ wp (bind e f) Q %I.
Proof.
  iIntros "HA HB". simpl. iApply (wp_consequence with "HA"). auto.
Qed.

Lemma ret_spec {X} (v : X) H (Q : X -> iProp) :
  (H ⊢ Q v) -> {{ H }} ret v {{ v'; Q v' }}.
Proof. simpl; iIntros. iApply H0; auto. Qed.

Lemma bind_spec {X Y} (e : mon X) (f : X -> mon Y) Q Q' H :
  ({{ H }} e {{ v; Q' v }}) ->
  (∀ v, {{ Q' v }} (f v) {{ v'; Q v' }}) ->
  {{ H }} (bind e f) {{ v; Q v}}.
Proof.
  intros. iIntros "HA".
  iApply (wp_bind e f _ Q' with "[HA]").
  - iApply (H0 with "[HA]"); auto.
  - iIntros (v) "HC". iApply (H1 with "[HC]"); auto.
Qed.

Lemma consequence {X} H H' (Q : X -> iProp) (Q' : X -> iProp) (e : mon X) :
  ({{ H' }} e {{ v; Q' v }}) ->
  (forall v, Q' v ⊢ Q v) ->
  (H ⊢ H') ->
  {{ H }} e {{ v; Q v }}.
Proof.
  intros. iIntros "HA". iDestruct (H2 with "HA") as "HA".
  iDestruct (H0 with "HA") as "HA". iApply (wp_consequence with "HA"). iIntros "*". iApply H1.
Qed.

Lemma frame_bind : forall (P : iProp), ⊢ P -∗ emp ∗ P.
Proof. iIntros "* $". Qed.

Lemma frame {X} H R Q (e : mon X) :
  ({{ H }} e {{ v; Q v }}) ->
  {{ H ∗ R }} e {{ v; Q v ∗ R }}.
Proof.
  intro P. iIntros "[HA HC]". iApply (wp_consequence with "[HA]").
  iApply P; auto. iIntros; iFrame.
Qed.

Lemma intro_true_r {X} H Q (e : mon X) :
  ({{ emp ∗ H }} e {{ v; Q v }}) ->
  {{ H }} e {{ v; Q v }}.
Proof.
  intro P. iIntros "HA". iApply (P with "[HA]").
  iFrame.
Qed.

Lemma exists_spec {X Y} v' H (Q : X -> Y -> iProp) (e : mon X) :
  ({{ H }} e {{ v; Q v v' }}) ->
  {{ H }} e {{ v; ∃ t, Q v t }}.
Proof.
  intros. iApply consequence. iApply H0.  all : eauto.
Qed.

Ltac Frame := eapply intro_true_r; eapply frame.

(** Effects rules *)

Lemma rule_gensym t : {{ emp }} gensym t {{ l; & l }}.
Proof. simpl; auto. Qed.

Lemma rule_error {X} P (Q : X -> iProp) e : {{ P }} error e {{ v; Q v }}.
Proof. auto. Qed.

Lemma rule_trail  : {{ emp }} trail tt {{ _; emp  }}.
Proof. auto. Qed.

Definition inject_aux n :=
  List.map Pos.of_nat
    (seq (Pos.to_nat (first_unused_ident ()))
       (Pos.to_nat n - Pos.to_nat (first_unused_ident ()))).

Lemma inject_last : forall n,
    Pos.le (first_unused_ident ()) n -> inject_aux (Pos.succ n) = inject_aux n ++ [n].
Proof.
  intros n lt. unfold inject_aux. rewrite <- (Pos2Nat.id n).
  assert (forall (n : nat), [Pos.of_nat n] = Pos.of_nat n :: map Pos.of_nat nil) by auto.
  rewrite H. rewrite <- map_cons. rewrite <- map_app. f_equal.
  rewrite Pos2Nat.id. assert (forall (n : nat), [n] = seq n 1) by auto. rewrite H0.
  assert ((Pos.to_nat (first_unused_ident ())) +
            (Pos.to_nat n - Pos.to_nat (first_unused_ident ()))
          = Pos.to_nat n) by lia.
  rewrite <- H1 at 2. rewrite <- seq_app. f_equal. lia.
Qed.

Lemma next_disjoint : forall n, Pos.le (first_unused_ident ()) n ->  (inject_aux n) ## [n].
Proof.
  repeat intro. inversion H1. subst.
  - unfold inject_aux in H0. apply elem_of_list_In in H0. apply Coqlib.list_in_map_inv in H0.
    destruct H0 as [x [P0 P2]].
    apply in_seq in P2. destruct P2. lia.
  - inversion H4.
Qed.

Lemma unused_nil : inject_aux (first_unused_ident ()) = nil.
Proof.
  unfold inject_aux. rewrite PeanoNat.Nat.sub_diag. simpl. reflexivity.
Qed.

Definition inject n : gset ident :=
  list_to_set (inject_aux n).

Lemma unused_map : inject (first_unused_ident ()) = ∅.
Proof.
  unfold inject. rewrite unused_nil. simpl. auto.
Qed.

Lemma inject_last_set : forall n,
    Pos.le (first_unused_ident ()) n -> inject (Pos.succ n) = {[ n ]} ∪ (inject n).
Proof.
  intros. unfold inject. rewrite inject_last; auto.
  rewrite list_to_set_app_L. simpl. rewrite union_empty_r_L.
  rewrite union_comm_L. auto.
Qed.

Lemma inject_disjoint : forall n, Pos.le (first_unused_ident ()) n -> inject n ## {[ n ]}.
Proof.
  intros. apply disjoint_singleton_r. unfold inject.
  apply not_elem_of_list_to_set. intro. eapply next_disjoint; eauto.
  constructor.
Qed.

Definition eval {X} (m : mon X) : generator -> res (generator * X).
  revert X m. fix eval 2. intros X m. destruct m as [T x|T e|T1 T2 m f].
  - apply (fun s => OK (s, x)).
  - destruct e as [err | ty | ].
    + eapply (fun s => Error err).
    + eapply (fun s =>
                let h := gen_trail s in
                let n := gen_next s in
                OK (mkgenerator (Pos.succ n) ((n,ty) :: h), n)).
    + eapply (fun s => OK (s, gen_trail s)).
  - intro s. destruct (eval T1 m s) as [[g v]| err].
    + eapply (eval T2 (f v) g).
    + eapply (Error err).
Defined.

Definition run {X} (m: mon X): res X :=
  match eval m (initial_generator tt) with
  | OK (_, v) => OK v
  | Error e => Error e
  end.

Open Scope positive_scope.

Lemma eval_mono : forall X (m : mon X) g_init g_res res,
    eval m g_init = OK (g_res, res) ->
    gen_next g_init <= gen_next g_res.
Proof.
  induction m as [T x|T [err | ty |]|T1 T2 m f]; intros.
  - inversion H. lia.
  - inversion H.
  - inversion H. simpl in *. lia.
  - inversion H. lia.
  - simpl in H0. destruct (eval m g_init) as [[g_int v]| ] eqn:?.
    eapply H in H0. eapply f in Heqr. lia. inversion H0.
Qed.

Close Scope positive_scope.

Section Eval_Adequacy.
  Variable X: Type.
  Implicit Type m: mon X.
  Implicit Type P: iProp.
  Implicit Type Q: X -> iProp.
  Implicit Type v: X.

  Lemma adequacy_wp : forall m Q g_init g_res v,
      Pos.le (first_unused_ident tt) (gen_next g_init) ->
      (&& (inject (gen_next g_init)) ⊢ wp m Q) ->
      eval m g_init = OK (g_res, v) ->
      (Q v) () (inject (gen_next g_res)).
  Proof.
    revert X.
    fix ind 2.
    destruct m as [v| Y []|]; intros.
    - inversion H1; subst. apply soundness. iApply H0.
    - inversion H1.
    - apply soundness. inversion_clear H1. simpl in *.
      iIntros "HA". rewrite inject_last_set; auto.
      iDestruct (heap_ctx_split_sing with "HA") as "[HA HB]".
      apply inject_disjoint; auto. iDestruct (H0 with "HA") as "HA".
      iApply ("HA" with "HB").
    - simpl in *. inversion H1. subst. apply soundness.
      iIntros "HA". iApply (H0 with "HA").
    - simpl in *. destruct (eval m g_init) as [[g_int v_int]| err] eqn:eval_m.
      + eapply ind in H0; eauto.
        eapply ind. 3 : eapply H1.
        etransitivity. eapply H. eapply eval_mono; eauto.
        iIntros "HA". eapply completeness in H0. iApply (H0 with "HA").
      + inversion H1.
  Qed.

  Lemma adequacy_init : forall e Q g v,
      (⊢ wp e Q) ->
      eval e (initial_generator tt) = OK (g, v) ->
      (Q v) () (inject (gen_next g)).
  Proof.
    intros. eapply adequacy_wp; eauto. simpl. lia.
    rewrite unused_map. auto.
  Qed.

  Lemma adequacy_core : forall e Q g_init v g_res H,
      Pos.le (first_unused_ident tt) (gen_next g_init) ->
      (&& (inject (gen_next g_init)) ⊢ H) -> ({{ H }} e {{ v; Q v }}) ->
      eval e g_init = OK (g_res, v) ->
      (Q v) () (inject (gen_next g_res)).
  Proof.
    intros. eapply adequacy_wp; eauto. iIntros "HA". iDestruct (H1 with "HA") as "HA".
    iApply (H2 with "HA"); auto.
  Qed.

  Lemma adequacy_triple_init : forall e Q v g H,
      (⊢ H) -> ({{ H }} e {{ v; Q v }}) ->
      eval e (initial_generator tt) = OK (g, v) ->
      (Q v) () (inject (gen_next g)).
  Proof.
    intros. eapply adequacy_init; eauto. iApply H1; eauto.
  Qed.

End Eval_Adequacy.

Lemma adequacy_wp_pure {X} : forall (e : mon X) (Q : X -> Prop) g_init v g_res,
    Pos.le (first_unused_ident tt) (gen_next g_init) ->
    (&& (inject (gen_next g_init)) ⊢ wp e (fun v =>  ⌜Q v⌝)) ->
    eval e g_init = OK (g_res, v) ->
    Q v.
Proof.
  intros. apply (soundness_pure (inject (gen_next g_res))). iApply completeness.
  eapply (adequacy_wp _ _ _ _ _ _ H H0 H1).
Qed.

Lemma adequacy_pure {X} : forall (e : mon X) (Q : X -> Prop) g_init v g_res H,
    Pos.le (first_unused_ident tt) (gen_next g_init) ->
    (&& (inject (gen_next g_init)) ⊢ H) -> ({{ H }} e {{ v; ⌜ Q v ⌝}}) ->
    eval e g_init = OK (g_res, v) ->
    Q v.
Proof.
  intros. eapply adequacy_wp_pure; eauto. iIntros "HA". iDestruct (H1 with "HA") as "HA".
  iDestruct (H2 with "HA") as "$".
Qed.

Section Adequacy.
  Variable X: Type.
  Implicit Type m: mon X.
  Implicit Type P: iProp.
  Implicit Type Q: X -> Prop.
  Implicit Type v: X.

  Lemma adequacy: forall m Q v,
      ({{ emp }} m {{ v; ⌜ Q v ⌝}}) ->
      run m = OK v -> Q v.
  Proof.
    intros m.
    unfold run. intros.
    destruct (eval m (initial_generator tt)) eqn:H2.
    destruct p. inversion H0. subst.
    eapply adequacy_pure; eauto.
    simpl. lia. rewrite unused_map.
    iIntros "_".
    iApply H. auto.
    inversion H0.
  Qed.

End Adequacy.
