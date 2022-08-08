From Formalisation Require Import Nom Inject EquationalTheory FuelMono.

Section mono.

  Open Scope N_scope.

  Context {atom : Type}.


  Class Monotone {X} (f : MonSem X%type) :=
    mk_mono {
        monotone : forall s sres x,
          f s = Res (sres, x) ->
          pos s <= pos sres /\ pos sres + len sres <= pos s + len s;
      }.

  Lemma run_ret : forall fuel X (x : X) s (a : list atom), run fuel (ret x) a s = Res (s, x).
  Proof.
    intros. destruct fuel; reflexivity.
  Qed.

  Instance ret_mono : forall X (x :X), Monotone (Nom.run_ret x).
  Proof. intros. constructor. intros. inversion H. subst. split; lia. Defined.

  Instance bind_mono : forall X (e1 : MonSem X) Y (e2 : X -> MonSem Y),
      Monotone e1 -> (forall (x : X), Monotone (e2 x)) -> Monotone (run_bind e1 e2).
  Proof.
    intros X e1 Y e2 [mono_e1] mono_e2. constructor.
    intros s sres x0 run. unfold_MonSem.
    destruct (e1 s) as [[s_res res] | |] eqn:Pe1.
    eapply mono_e1 in Pe1 as [P0 P1]. eapply (mono_e2 res) in run as [P2 P3]. split; lia.
    all : inversion run.
  Defined.

  Instance fail_mono : forall X, @Monotone X run_fail.
  Proof. intros. constructor. intros. inversion H. Defined.


  Instance get_mono : Monotone run_get.
  Proof. constructor. intros. inversion H. split; reflexivity. Defined.


  Instance length_mono : Monotone run_length.
  Proof. constructor. intros. inversion H. split; reflexivity. Defined.

  Instance take_mono : forall n, Monotone (Nom.run_take n).
  Proof.
    intros. constructor. intros. unfold run_take in H.
    unfold_MonSem. destruct (n <=? len s) eqn:P.
    eapply N.leb_le in P. inversion H. subst. simpl. split; lia.
    inversion H.
  Defined.

  Instance try_with_mono : forall X (e1 : MonSem X) e2,
      Monotone e1 -> Monotone e2 -> Monotone (Nom.run_try_with e1 e2).
  Proof.
    intros X e1 e2 [mono_e1] [mono_e2]. constructor.
    intros s sres x run. unfold_MonSem.
    destruct (e1 s) as [[s_res res] | |] eqn:Pe1. inversion run. subst. eapply mono_e1; eauto.
    destruct (e2 s) as [[s_res res] | |] eqn:Pe2. inversion run. subst. eapply mono_e2; eauto.
    all : inversion run.
  Defined.


  Instance alt_mono : forall X (e1 e2 : NomG X) data
                        (run : forall X, NomG X -> list atom -> MonSem X),
      Monotone (run X e1 data) ->
      Monotone (run X e2 data) ->
      Monotone (Nom.run_alt run e1 e2 data).
  Proof.
    intros X e1 e2 data run mono_e1 mono_e2. unfold run_alt.
    eapply try_with_mono; auto.
  Defined.

  Instance scope_mono : forall X range (e : NomG X) data (run : forall X, NomG X -> list atom -> MonSem X),
      Monotone (run X e data) -> Monotone (Nom.run_local run (Some range) e data).
  Proof.
    intros X range e data run mono_run. unfold run_local.
    unfold_MonSem. constructor. intros.
    destruct (run X e data range) as [[s_res res]| |]; inversion_clear H.
    split; lia.
  Defined.

  Instance peek_mono : forall X (e : NomG X) data
                         (run : forall X, NomG X -> list atom -> MonSem X),
      Monotone (run X e data) -> Monotone (Nom.run_local run None e data).
  Proof.
    intros X e data run mono_run. unfold run_local.
    constructor. intros. unfold_MonSem.
    destruct (run X e data s) as [[s_res res]| |] eqn:?; inversion_clear H.
    split; lia.
  Defined.

  Lemma run_repeat_Some_monotone :
    forall n fuel X e b data (run_mono : forall fuel base, Monotone (run fuel (e base) data)),
      Monotone ((@run) atom fuel X (Nom.repeat (Some n) e b) data).
  Proof.
    induction n using N.peano_ind; simpl; intros.
    - eapply bind_mono. eapply ret_mono. intro. eapply ret_mono.
    - rewrite N2Nat.inj_succ.
      eapply bind_mono. eapply bind_mono. eapply run_mono.
      intros. eapply (IHn fuel _ _ x) in run_mono.
      simpl in run_mono. destruct run_mono.
      constructor. intros. eapply monotone0. rewrite ret_neutral_right. eauto.
      intros. eapply ret_mono.
  Qed.

  Instance read_mono : forall s n a, @Monotone atom (Nom.run_read s n a).
  Proof. intros. constructor. intros. eapply run_read_eq_span in H. subst. split; lia. Defined.

  Lemma repeat_some_next_step : forall n fuel X Y c (b : X) (k : X -> NomG Y) data s,
      @run atom fuel _ (let! v := Nom.repeat (Some (N.succ n)) c b in k v) data s =
        run fuel (let! v := c b in
                  let! v := Nom.repeat (Some n) c v in
                  k v) data s.
  Proof.
    intros. simpl. rewrite N2Nat.inj_succ. rewrite Nom.bind_assoc.
    rewrite run_bind_monsem. simpl. reflexivity.
  Qed.

  Lemma mono_repeat_none_aux : forall fuel0 fuel1 X v c data,
    (forall (res : X) (fuel : nat) (data : list atom), Monotone (run fuel (c res) data)) ->
      Monotone ((fix sem_repeat_none (n : nat) (x0 : X) {struct n} : MonSem X :=
                   match n with
                   | 0%nat => λ _ : span, NoFuel
                   | S n0 =>
                       run_try_with (let* v0 := run fuel0 (c x0) data in sem_repeat_none n0 v0)
                         (Nom.run_ret x0)
                   end) fuel1 v).
  Proof.
    induction fuel1; simpl; intros; constructor.
    - intros. inversion H0.
    - eapply try_with_mono. 2 : eapply ret_mono.
      eapply bind_mono. eapply H. intro. eapply IHfuel1. eapply H.
  Qed.


  Lemma mono_repeat_none: forall fuel X (c : X -> @NomG atom X) b data,
      (∀ (res : X) (fuel : nat) (data : list atom), Monotone (run fuel (c res) data)) ->
      Monotone (run fuel (Nom.repeat None c b) data).
  Proof.
    intros. simpl. constructor. intro. rewrite ret_neutral_right.
    eapply mono_repeat_none_aux. eapply H.
  Qed.

  Lemma run_monotone : forall X e fuel data,
      Monotone (@run atom fuel X e data).
  Proof.
    Ltac bind_mono_mono op_mono :=
      eapply bind_mono;
      [eapply op_mono;
       idtac
      | intros].
    intros X e.
    eapply (Nom_ind (fun X e => forall (fuel : nat) (data : list atom), Monotone (run fuel e data)));
      intros.
    - eapply ret_mono.
    - eapply fail_mono.
    - bind_mono_mono length_mono. eapply H.
    - bind_mono_mono take_mono. eapply H.
    - bind_mono_mono read_mono. eapply H.
    - bind_mono_mono alt_mono. eapply H. eapply H0. eapply H1.
    - bind_mono_mono scope_mono. eapply H. eapply H0.
    - bind_mono_mono peek_mono. eapply H. eapply H0.
    - destruct o.
      + revert b. induction n using N.peano_ind; intros b.
        * simpl. apply bind_mono. eapply ret_mono. intros. eapply H0.
        * constructor. intros s sres x. rewrite repeat_some_next_step.
          rewrite run_bind_monsem.
          intros. eapply bind_mono. 3 : eapply H1.
          eapply H. intros. eapply IHn.
      + constructor. intros s sres x. rewrite run_bind_monsem.
        intros. eapply bind_mono. 3 : eapply H1.
        2 : intro; eapply H0. eapply mono_repeat_none. eapply H.
  Qed.

  Global Instance run_mono : forall fuel X (e : NomG X) (a : list atom),
      Monotone (run fuel e a).
  Proof.
    intros fuel X e a. constructor. intros s res x Hrun. eapply run_monotone. exact Hrun.
  Qed.

  Close Scope N_scope.

End mono.
