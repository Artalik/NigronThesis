From Formalisation Require Import Nom EquationalTheory.

Section fuel_mono.

  Context {atom : Type}.

  Definition NomG := @NomG atom.

  Lemma repeat_none_fuel_mono : forall fuele fuel fuel0 fuel1 X (c : X -> NomG X) s b a res,
      (∀ (res : X) (a : list atom) (s : span) (res0 : Result (span * X)) (fuele fuel : nat),
          run fuele (c res) a s = res0 →
          res0 ≠ NoFuel →
          (fuele ≤ fuel)%nat →
          run fuel (c res) a s = res0) ->
      (fix sem_repeat_none (n : nat) (x : X) {struct n} : MonSem X :=
       match n with
            | 0%nat => λ _ : span, NoFuel
            | S n0 =>
                run_try_with (let* v := run fuel0 (c x) s in sem_repeat_none n0 v) (run_ret x)
            end) fuele b a = res ->
      (fuele <= fuel)%nat ->
      (fuel0 ≤ fuel1)%nat →
      res <> NoFuel ->
        (fix sem_repeat_none (n : nat) (x : X) {struct n} : MonSem X :=
           match n with
           | 0%nat => λ _ : span, NoFuel
           | S n0 =>
               run_try_with (let* v := run fuel1 (c x) s in sem_repeat_none n0 v) (run_ret x)
           end) fuel b a = res.
  Proof.
    induction fuele; simpl; intros.
    - subst. contradiction.
    - unfold_MonSem. destruct (run fuel0 (c b) s a) eqn:?. destruct x.
      + assert (fuel = S (pred fuel)) by lia. rewrite H4.
        eapply H in Heqr; eauto. rewrite Heqr.
        destruct ((fix sem_repeat_none (n : nat) (x : X) {struct n} : MonSem X :=
            match n with
            | 0%nat => λ _ : span, NoFuel
            | S n0 =>
                λ s0 : span,
                  match
                    match run fuel0 (c x) s s0 with
                    | Res (s, x1) => sem_repeat_none n0 x1 s
                    | NoRes => NoRes
                    | NoFuel => NoFuel
                    end
                  with
                  | Res (s, v) => Res (s, v)
                  | NoRes => Res (s0, x)
                  | NoFuel => NoFuel
                  end
            end) fuele x s0) eqn:?. destruct x0.
        erewrite IHfuele.
        2 : eapply H.
        2 : eapply Heqr0. simpl. auto. lia. lia. auto.
        erewrite IHfuele.
        2 : eapply H.
        2 : eapply Heqr0. simpl. auto. lia. lia. auto.
        subst. contradiction.
      + assert (fuel = S (pred fuel)) by lia. rewrite H4.
        erewrite H. 2 : eapply Heqr. simpl. auto. auto. lia.
      + subst. contradiction.
  Qed.

  Lemma repeat_some_fuel_mono : forall n fuel0 fuel1 X (c : X -> NomG X) s b data res,
      (∀ (res : X) (a : list atom) (s : span) (res0 : Result (span * X)) (fuele fuel : nat),
          run fuele (c res) a s = res0 →
          res0 ≠ NoFuel →
          (fuele ≤ fuel)%nat →
          run fuel (c res) a s = res0) ->
      (fix sem_repeat_some (n : nat) (x : X) {struct n} : MonSem X :=
       match n with
            | 0%nat => λ s : span, Res (s, x)
            | S n0 =>
                λ s : span,
                    match run fuel0 (c x) data s with
                    | Res (s0, x1) => sem_repeat_some n0 x1 s0
                    | NoRes => NoRes
                    | NoFuel => NoFuel
                    end
            end) n b s = res ->
      (fuel0 ≤ fuel1)%nat →
      res <> NoFuel ->
      (fix sem_repeat_some (n : nat) (x : X) {struct n} : MonSem X :=
         match n with
         | 0%nat => λ s : span, Res (s, x)
         | S n0 =>
             λ s : span,
               match run fuel1 (c x) data s with
               | Res (s0, x1) => sem_repeat_some n0 x1 s0
               | NoRes => NoRes
               | NoFuel => NoFuel
               end
         end) n b s = res.
  Proof.
    induction n; simpl; intros.
    - subst. reflexivity.
    - destruct (run fuel0 (c b) data s) eqn:?. destruct x.
      + eapply H in Heqr; eauto. rewrite Heqr.
        eapply IHn; eauto.
      + erewrite H. 2 : eapply Heqr. simpl. auto. auto. lia.
      + subst. contradiction.
  Qed.

  Lemma run_fuel_mono : forall X (e : NomG X) s a res fuele fuel,
      run fuele e s a = res ->
      res <> NoFuel ->
      (fuele <= fuel)%nat ->
      run fuel e s a = res.
  Proof.
    intros X e.
    eapply (Nom_ind
              (fun X e => forall (s : list atom) (a : span) (res : Result (span * X)) (fuele fuel : nat),
                   run fuele e s a = res → res ≠ NoFuel → (fuele ≤ fuel)%nat → run fuel e s a = res));
      intros.
    - rewrite run_ret_eq. rewrite run_ret_eq in H. auto.
    - rewrite fail_absorb_left in H. rewrite fail_absorb_left.
      rewrite <- H. reflexivity.
    - rewrite <- H0. repeat rewrite run_bind_monsem.
      unfold_MonSem. simpl. erewrite H; eauto.
      intro. apply H1. rewrite <- H0.
      repeat rewrite run_bind_monsem.
      unfold_MonSem. simpl. auto.
    - rewrite run_bind_monsem. rewrite run_bind_monsem in H0.
      unfold_MonSem. unfold run in *. simpl in *.
      rewrite ret_neutral_right. rewrite ret_neutral_right in H0.
      destruct (run_take n a); auto. destruct x.
      erewrite H; eauto. intro. subst. contradiction.
    - rewrite run_bind_monsem. rewrite run_bind_monsem in H0.
      unfold_MonSem. unfold run in *. simpl in *.
      rewrite ret_neutral_right. rewrite ret_neutral_right in H0.
      destruct (run_read s pos s0 a); auto. destruct x.
      erewrite H; eauto. intro. subst. contradiction.
    - rewrite run_bind_monsem. rewrite run_bind_monsem in H2.
      unfold_MonSem. simpl in *.
      rewrite ret_neutral_right. rewrite ret_neutral_right in H2.
      unfold run_alt in *. unfold_MonSem.
      destruct (run fuele c1 s a) eqn:?. destruct x.
      + erewrite H; eauto. simpl.
        erewrite H1; eauto.
        subst. auto.
      + erewrite H; eauto. simpl.
        destruct (run fuele c2 s a) eqn:?. destruct x.
        * erewrite H0; eauto. simpl.
          erewrite H1; eauto. intro. subst. contradiction.
        * erewrite H0; eauto. simpl. auto.
        * exfalso. apply H3. auto.
      + exfalso. apply H3. auto.
    - rewrite run_bind_monsem. rewrite run_bind_monsem in H1.
      unfold_MonSem. simpl in *.
      rewrite ret_neutral_right. rewrite ret_neutral_right in H1.
      unfold run_scope in *. unfold_MonSem.
      destruct (run fuele c s0 s) eqn:?. destruct x.
      + erewrite H; eauto. simpl.
        erewrite H0; eauto. intro. subst. contradiction.
      + erewrite H; eauto. simpl. auto.
      + exfalso. eapply H2. auto.
    - rewrite run_bind_monsem. rewrite run_bind_monsem in H1.
      unfold_MonSem. simpl in *.
      rewrite ret_neutral_right. rewrite ret_neutral_right in H1.
      unfold run_peek in *. unfold_MonSem.
      destruct (run fuele c s a) eqn:?. destruct x.
      + erewrite H; eauto. simpl.
        erewrite H0; eauto. intro. subst. contradiction.
      + erewrite H; eauto. simpl. auto.
      + exfalso. eapply H2. auto.
    - edestruct o.
      + simpl in *. unfold_MonSem.
        destruct ((fix sem_repeat_some (n : nat) (x : X1) {struct n} : MonSem X1 :=
                     match n with
                     | 0%nat => λ s : span, Res (s, x)
                     | S n0 =>
                         λ s0 : span,
                           match run fuel (c x) s s0 with
                           | Res (s, x1) => sem_repeat_some n0 x1 s
                           | NoRes => NoRes
                           | NoFuel => NoFuel
                           end
                     end) (N.to_nat n) b a) eqn:?. destruct x.
        * erewrite repeat_some_fuel_mono in Heqr.
          erewrite Heqr in H1. eauto. eapply H. reflexivity. lia.
          intro. rewrite H4 in H1. subst. contradiction.
        * erewrite repeat_some_fuel_mono in Heqr.
          erewrite Heqr in H1. eauto. eapply H. reflexivity. lia.
          intro. rewrite H4 in H1. subst. contradiction.
        * erewrite repeat_some_fuel_mono in Heqr.
          erewrite Heqr in H1. eauto. eapply H. reflexivity. lia.
          intro. rewrite H4 in H1. subst. contradiction.
      + rewrite run_bind_monsem. rewrite run_bind_monsem in H1.
        unfold_MonSem. simpl in *.
        rewrite ret_neutral_right. rewrite ret_neutral_right in H1.
        destruct ((fix sem_repeat_none (n : nat) (x : X1) {struct n} : MonSem X1 :=
            match n with
            | 0%nat => λ _ : span, NoFuel
            | S n0 =>
                run_try_with (let* v := run fuele (c x) s in sem_repeat_none n0 v) (run_ret x)
            end) fuele b a) eqn:?. destruct x.
        * eapply repeat_none_fuel_mono in Heqr. erewrite Heqr.
          eapply H0. eauto. auto. lia. auto. lia. lia. auto.
        * eapply repeat_none_fuel_mono in Heqr. erewrite Heqr.
          auto. auto. lia. auto. auto.
        * subst. contradiction.
  Qed.

  Lemma run_bind_weak :
    ∀ (fuele fuelk : nat) (X Y : Type)  (e : NomG X) (k : X → NomG Y) (s : span)
      (a : list atom) (s_res : span) (v1 : X) (res : Result (span * Y)),
      run fuele e a s = Res (s_res, v1) →
      run fuelk (k v1) a s_res = res →
      res ≠ NoFuel →
      ∃ fuel : nat, run fuel (bind e k) a s = res.
  Proof.
    intros. exists (fuele `max` fuelk)%nat. eapply run_bind_decompose; eapply run_fuel_mono; eauto.
    lia. lia.
  Qed.

End fuel_mono.
