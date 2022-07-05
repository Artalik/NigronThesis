From Formalisation Require Import Nom ProgramLogic Inject Monotone.
From Formalisation Require Import EquationalTheory.

Section adequacy.

  Context {atom : Type}.

  Definition NomG := @NomG atom.

  Class Sound {X} (run : MonSem X) (e : NomG X) :=
    mk_sound {
        mono : Monotone run;
        sound : forall s sres v Q,
          run s = Res (sres, v) ->
            ⊢ wp e (fun v => <absorb> Q v) -∗
              injectSL (pos s) (pos sres) -∗ <absorb> Q v
      }.


  Lemma bind_soundness : forall X (e : NomG X) rune Y (k : X -> NomG Y) runk,
      Sound rune e ->
      (forall v, Sound (runk v) (k v)) ->
      Sound (run_bind rune runk) (let! v := e in
                                  k v).
  Proof.
    intros X e rune Y k runk [mono_e sound_e] sound_k.
    constructor. eapply bind_mono. eapply mono_e. intro. eapply (sound_k x).
    intros s sres v Q RUN.
    iIntros "wp HA". unfold_MonSem. destruct (rune s) as [[s_res res]| |] eqn:P.
    pose P as grow_e. eapply mono_e in grow_e as [P0 _].
    pose RUN as grow_k. eapply sound_k in grow_k as [P1 _].
    unfold injectSL. rewrite (inject_union (pos s_res)). 2-3 : lia.
    iDestruct (big_sepS_union with "HA") as "[HA HB]". eapply inject_disjoint.
    destruct (sound_k res) as [mono_k wp_k].
    iDestruct (bind_wp with "wp") as "wp".
    iDestruct (sound_e with "[wp] HA") as ">HA". eapply P.
    iApply (wp_consequence with "wp"). iIntros (v0) "HA". iApply "HA".
    iApply (wp_k with "HA HB"); auto. all : inversion RUN.
  Qed.

  Lemma ret_soundness : forall X x,
      @Sound X (Nom.run_ret x) (ret x).
  Proof.
    intros. constructor. eapply ret_mono.
    intros. inversion H. iIntros "HA HB". iApply "HA".
  Qed.

  Lemma fail_soundness : forall X,
      @Sound X run_fail fail.
  Proof. intros. constructor. eapply fail_mono. intros. inversion H. Qed.

  Lemma length_soundness : Sound run_length Nom.length.
  Proof.
    constructor. eapply length_mono.
    intros. simpl in *. iIntros "HA HB". iApply "HA".
  Qed.

  Lemma read_soundness : forall s n a, Sound (run_read s n a) (Nom.read s n).
  Proof.
    constructor. eapply read_mono.
    intros. simpl in *. iIntros "HA HB". iApply "HA".
  Qed.

  Lemma incl_exists : forall (s1 s2 : gset N),
      s1 ⊆ s2 -> ∃ s3, s1 ∪ s3 = s2 /\ s1 ## s3.
  Proof.
    induction s1 as [| y X not_in IH] using set_ind_L.
    - intros. exists s2. split. rewrite union_empty_l_L. reflexivity. apply disjoint_empty_l.
    - intros. apply union_subseteq in H as [P0 P1].
      apply IH in P1 as [s3 P2].
      exists (s3 ∖ {[y]}). destruct P2 as [P2 P4].
      rewrite <- P2.
      rewrite <- union_assoc_L. rewrite union_comm_L. rewrite <- union_assoc_L. split.
      + f_equal. rewrite difference_union_L. rewrite union_comm_L.
        destruct (subseteq_union_L {[y]} s3). apply H. clear H H0. intros x P3. inversion P3.
        apply lookup_singleton_Some in H0 as [H0 _]. subst.
        apply elem_of_subseteq_singleton in P0.
        apply elem_of_union in P0. destruct P0; auto.
        apply not_in in H. exfalso. apply H.
      + apply disjoint_union_l. split.
        * apply disjoint_difference_r1. auto.
        * apply disjoint_difference_r2. auto.
  Qed.

  Lemma take_soundness_2 : forall n s s_res res,
      run_take n s = Res (s_res, res) ->
      inject (pos res) (pos res + len res) ⊆ inject (pos s) (pos s_res).
  Proof.
    unfold run_take. unfold_MonSem. intros. destruct (n <=? len s) eqn:P.
    - inversion_clear H. simpl. reflexivity.
    - inversion H.
  Qed.

  Lemma take_soundness : forall n, Sound (run_take n) (Nom.take n).
  Proof.
    intros. constructor. apply take_mono.
    simpl. intros. iIntros "wp HA".
    eapply take_soundness_2 in H. unfold injectSL.
    eapply incl_exists in H as [set_diff [P4 P5]]. rewrite <- P4.
    iDestruct (big_sepS_union with "HA") as "[HA _]". eapply P5.
    iApply ("wp" with "[HA]"). iApply (inject_IsFresh with "HA"); reflexivity.
  Qed.

  (* Lemma alt_soundness : forall run X (c1 c2 : NomG X) data, *)
  (*     Sound (run X c1 data) c1 -> *)
  (*     Sound (run X c2 data) c2 -> *)
  (*     Sound (run_alt c1 c2 data) (Nom.alt c1 c2). *)
  (* Proof. *)
  (*   intros run X c1 c2 data [mono_c1 sound_c1] [mono_c2 sound_c2]. *)
  (*   constructor. apply alt_mono; auto. *)
  (*   simpl. intros s res v Q RUN. iIntros "wp HA". iNorm. *)
  (*   unfold run_alt in RUN. unfold_MonSem. *)
  (*   destruct (run X c1 data s) as [[sres1 res1] | |] eqn:Pc1. *)
  (*   - inversion RUN. subst. iDestruct "wp" as "[wp _]". *)
  (*     iDestruct (sound_c1 with "wp") as "HB"; eauto. *)
  (*     iApply ("HB" with "HA"). *)
  (*   - iDestruct "wp" as "[_ wp]". *)
  (*     iDestruct (sound_c2 with "wp") as "HB"; eauto. *)
  (*     iApply ("HB" with "HA"). *)
  (*   - inversion RUN. *)
  (* Qed. *)

  Lemma run_incl : forall X (run : forall {X}, NomG X -> list atom -> MonSem X)
                     (e : NomG X) (a : list atom) s1 s2 v start,
      Monotone (run e a) ->
      run e a s1 = Res (s2, v) ->
      inject start (pos s2) ⊆ inject start (pos s1 + len s1) .
  Proof.
    intros X run e a s1 s2 v start run_mono RUN.
    eapply run_mono in RUN. apply inject_mono_r. lia.
  Qed.

  Lemma inject_incl : forall (s1 s2 : gset N),
      s1 ⊆ s2 -> ⊢ ([∗ set] n ∈ s2, & n) -∗
                  ([∗ set] n ∈ s1, & n) ∗ ([∗ set] n ∈ (s2 ∖ s1), & n).
  Proof.
    intros. epose (s := H). apply incl_exists in s as [s3 [P0 P1]].
    eapply union_difference_L in H. subst.
    rewrite difference_union_distr_l_L.
    rewrite difference_diag_L. rewrite union_empty_l_L.
    iIntros "HA". iDestruct (big_sepS_union with "HA") as "[HA HB]". exact P1.
    apply disjoint_sym in P1. rewrite difference_disjoint_L. 2 : exact P1.
    iFrame.
  Qed.

  (* Lemma run_repeat_Some_soundness : *)
  (*   forall (run : forall X, NomG X -> list atom -> MonSem X) X (e : X -> NomG X) data, *)
  (*     (forall res, Sound (run X (e res) data) (e res)) -> *)
  (*     forall n b, *)
  (*       Sound (@run_repeat_Some atom run n X e b data) (Nom.repeat (Some n) e b). *)
  (* Proof. *)
  (*   intros run X e data sound_e n b. *)
  (*   constructor. constructor. intros. eapply run_repeat_Some_monotone; eauto. eapply sound_e. *)
  (*   simpl. intros s sres v Q RUN. *)
  (*   revert n b s sres RUN. destruct n using N.peano_ind; intros. *)
  (*   - iIntros "HA HD". iDestruct "HA" as (Q') "[HA [#HB HC]]". *)
  (*     rewrite run_repeat_Some_equation_1 in RUN. inversion_clear RUN. *)
  (*     iClear "HD". iApply ("HC" with "HA"). *)
  (*   - iIntros "HA HD". iDestruct "HA" as (Q') "[HA [#HB HC]]". *)
  (*     rewrite <- N.succ_pos_spec in RUN. rewrite run_repeat_Some_equation_2 in RUN. *)
  (*     rewrite N.succ_pos_spec in RUN. rewrite N.pred_succ in RUN. *)
  (*     destruct run as [[sres1 res1]| |] eqn:Pe. *)
  (*     destruct (sound_e b) as [mono_e1 sound_e1]. *)
  (*     pose Pe as grow. eapply sound_e in grow as [P0 _]. unfold injectSL. *)
  (*     pose RUN as grow. eapply run_repeat_Some_monotone in grow as [P1 _]. *)
  (*     rewrite (inject_union (pos sres1)). 2-3 : lia. *)
  (*     iDestruct (big_sepS_union with "HD") as "[HD HE]". eapply inject_disjoint. *)
  (*     iDestruct ("HB" with "HA") as "HA". *)
  (*     iDestruct (sound_e1 with "[HA] HD") as ">HA". eapply Pe. *)
  (*     iApply (wp_consequence with "HA"). iIntros (v0) "HA". iApply "HA". *)
  (*     iApply (IHn with "[HA HC] HE"). eapply RUN. *)
  (*     iExists Q'. iFrame. iSplitL; auto. *)
  (*     intros. eapply sound_e. *)
  (*     all : inversion RUN. *)
  (* Qed. *)

  (* Lemma run_repeat_None_soundness : *)
  (*   forall (run : forall X, NomG X -> list atom -> MonSem X) fuel X (e : X -> NomG X) data, *)
  (*     (forall res, Sound (run X (e res) data) (e res)) -> *)
  (*     forall b, *)
  (*       Sound (@run_repeat_None atom run fuel X e b data) (Nom.repeat None e b). *)
  (* Proof. *)
  (*   intros run fuel X e data sound_e b. *)
  (*   constructor. constructor. intros. eapply run_repeat_None_monotone; eauto. eapply sound_e. *)
  (*   simpl. intros s sres v Q RUN. *)
  (*   revert fuel b s sres RUN. induction fuel; intros. *)
  (*   - iIntros "HA HD". iDestruct "HA" as (Q') "[HA [#HB HC]]". *)
  (*     rewrite run_repeat_None_equation_1 in RUN. *)
  (*     destruct (run X (e b) data s) as [[sres0 res0]| |] eqn:P0. *)
  (*     destruct (Nat.eq_dec 0 0). inversion RUN. exfalso. apply n. reflexivity. *)
  (*     inversion_clear RUN. iClear "HD". iApply ("HC" with "HA"). *)
  (*     inversion RUN. *)
  (*   - iIntros "HA HD". iDestruct "HA" as (Q') "[HA [#HB HC]]". *)
  (*     rewrite run_repeat_None_equation_1 in RUN. *)
  (*     destruct (run X (e b) data s) as [[sres0 res0]| |] eqn:P0. *)
  (*     destruct (Nat.eq_dec (S fuel) 0). inversion RUN. *)
  (*     rewrite <- pred_of_minus in RUN. rewrite Nat.pred_succ in RUN. *)
  (*     pose P0 as grow. eapply sound_e in grow as [Pgrow _]. *)
  (*     pose RUN as grow. eapply run_repeat_None_monotone in grow as [PgrowRep _]. *)
  (*     unfold injectSL. rewrite (inject_union (pos sres0)). 2-3 : lia. *)
  (*     iDestruct (big_sepS_union with "HD") as "[HD HE]". eapply inject_disjoint. *)
  (*     destruct (sound_e b) as [_ sound_e1]. *)
  (*     iDestruct (sound_e1 with "[HA] HD") as ">HA". eapply P0. *)
  (*     iDestruct ("HB" with "HA") as "HA". iApply (wp_consequence with "HA"). *)
  (*     iIntros (v0) "HA". iApply "HA". *)
  (*     iApply (IHfuel with "[HA HC] HE"); eauto. *)
  (*     iExists Q'. iFrame. iSplitL; auto. *)
  (*     intros. eapply sound_e. *)
  (*     inversion_clear RUN. iClear "HD". iApply ("HC" with "HA"). *)
  (*     inversion RUN. *)
  (* Qed. *)

  (* Lemma repeat_soundness : *)
  (*   forall (run : forall X, NomG X -> list atom -> MonSem X) fuel X (e : X -> NomG X) data, *)
  (*     (forall res, Sound (run X (e res) data) (e res)) -> *)
  (*     forall o b, *)
  (*       Sound (@run_repeat atom run fuel o X e b data) (Nom.repeat o e b). *)
  (* Proof. *)
  (*   destruct o; intros. *)
  (*   - edestruct run_repeat_Some_soundness. eapply H. *)
  (*     constructor. eapply mono0. eapply sound0. *)
  (*   - edestruct run_repeat_None_soundness. eapply H. *)
  (*     constructor. eapply mono0. eapply sound0. *)
  (* Qed. *)


  Lemma alt_soundness : forall X (c1 c2 : NomG X) data fuel,
      Sound (run fuel c1 data) c1 ->
      Sound (run fuel c2 data) c2 ->
      Sound (run_alt (@run atom fuel) c1 c2 data) (Nom.alt c1 c2).
  Proof.
    intros X c1 c2 data fuel [mono_c1 sound_c1] [mono_c2 sound_c2].
    constructor. apply alt_mono; auto.
    simpl. intros s res v Q RUN. iIntros "wp HA". iNorm.
    unfold run_alt in RUN. unfold_MonSem.
    destruct (run fuel c1 data s) as [[sres1 res1] | |] eqn:Pc1.
    - inversion RUN. subst. iDestruct "wp" as "[wp _]".
      iDestruct (sound_c1 with "wp") as "HB"; eauto.
      iApply ("HB" with "HA").
    - iDestruct "wp" as "[_ wp]".
      iDestruct (sound_c2 with "wp") as "HB"; eauto.
      iApply ("HB" with "HA").
    - inversion RUN.
  Qed.

  Lemma scope_soundness : forall X range (c : NomG X) data fuel,
      Sound (run fuel c data) c ->
      Sound (run_scope (@run atom fuel) range c data) (Nom.scope range c).
  Proof.
    intros X range c data fuel [mono_c sound_c].
    constructor. apply scope_mono. auto.
    simpl. intros s res v Q RUN. iIntros "[HB wp] _".
    unfold run_scope in RUN. unfold_MonSem.
    destruct (run fuel c data range) as [[sres1 res1] | |] eqn:Pc;
      inversion RUN. subst.
    iDestruct (IsFresh_injectSL with "HB") as "HB".
    iDestruct (inject_incl with "HB") as "[HB _]".
    eapply run_incl. eapply mono_c. eapply Pc.
    iDestruct (sound_c with "wp HB") as "$". eapply Pc.
  Qed.

  Lemma peek_soundness : forall X (c : NomG X) data fuel,
      Sound (run fuel c data) c ->
      Sound (run_peek (@run atom fuel) c data) (Nom.peek c).
  Proof.
    intros X c data fuel [mono_c sound_c].
    constructor. apply peek_mono. auto.
    simpl. intros s res v Q RUN. iIntros "HB _". iApply "HB".
  Qed.

  (* Lemma run_repeat_None_sound : forall fuel0 fuel1 X (c : X -> NomG X) b data, *)
  (*     (forall fuel x, Sound (run_sem (NomG_to_sem fuel (c x)) data) (c x)) -> *)
  (*     Sound (run_repeat_None *)
  (*                 (REPEAT_to_sem fuel0 (fun x => NomG_to_sem fuel1 (c x))) b data). *)
  (* Proof. *)
  (*   induction fuel0 using N.peano_ind; simpl; intros. *)
  (*   - rewrite REPEAT_to_sem_equation_1. simpl. *)
  (*     constructor. intros. inversion H0. *)
  (*   - rewrite <- N.succ_pos_spec. erewrite REPEAT_to_sem_equation_2. *)
  (*     rewrite N.succ_pos_spec. rewrite N.pred_succ. *)
  (*     constructor. intros s sres x. *)
  (*     assert (run_repeat_None (REPEATS c (REPEAT_to_sem fuel0 c)) b data s = *)
  (*            run_try_with *)
  (*              (run_bind (run_sem (c b) data) *)
  (*                 (fun v => run_repeat_None (REPEAT_to_sem fuel0 c) v data)) *)
  (*              (Nom.run_ret b) s) by f_equal. *)
  (*     rewrite H0. intros. *)
  (*     eapply try_with_mono. 3 : eapply H1. 2 : eapply ret_mono. *)
  (*     eapply bind_mono. eapply H. intro. eapply IHfuel0. *)
  (*     eapply H. *)
  (* Qed. *)

  Lemma no_NoRes : forall fuel0 X (c : X -> NomG X) x s0 fuel data,
                     (fix sem_repeat_none (n : nat) (x : X) {struct n} : MonSem X :=
             match n with
             | 0%nat => λ _ : span, NoFuel
             | S n0 =>
                 λ s : span,
                   match
                     match run fuel (c x) data s with
                     | Res (s0, x1) => sem_repeat_none n0 x1 s0
                     | NoRes => NoRes
                     | NoFuel => NoFuel
                     end
                   with
                   | Res (s0, v) => Res (s0, v)
                   | NoRes => Res (s, x)
                   | NoFuel => NoFuel
                   end
             end) fuel0 x s0 <> NoRes.
  Proof.
    induction fuel0; simpl; intros. auto.
    destruct (run fuel (c x) data s0). destruct x0.
    2-3 : auto. destruct ((fix sem_repeat_none (n : nat) (x1 : X) {struct n} : MonSem X :=
       match n with
       | 0%nat => λ _ : span, NoFuel
       | S n0 =>
           λ s1 : span,
             match
               match run fuel (c x1) data s1 with
               | Res (s2, x3) => sem_repeat_none n0 x3 s2
               | NoRes => NoRes
               | NoFuel => NoFuel
               end
             with
             | Res (s2, v) => Res (s2, v)
             | NoRes => Res (s1, x1)
             | NoFuel => NoFuel
             end
       end) fuel0 x0 s). destruct x1.
    auto. auto. auto.
  Qed.

  Lemma repeat_none_soundness : forall fuel0 X (c : X -> NomG X) b data fuel,
          (∀ (res : X) data fuel, Sound (run fuel (c res) data) (c res)) ->
          Sound ((fix sem_repeat_none (n : nat) (x : X) {struct n} : MonSem X :=
               match n with
               | 0%nat => λ _ : span, NoFuel
               | S n0 =>
                   run_try_with (let* v := run fuel (c x) data in sem_repeat_none n0 v)
                     (Nom.run_ret x)
               end) fuel0 b) (Nom.repeat None c b).
  Proof.
    induction fuel0; simpl; intros.
    - constructor. constructor; intros. inversion H0. intros. inversion H0.
    - constructor. eapply try_with_mono. 2 : eapply ret_mono.
      eapply bind_mono. eapply H. intro. eapply Monotone.test.
      intros. eapply H.
      simpl. intros. unfold_MonSem.
      destruct (run fuel (c b) data s) eqn:?. destruct x.
      + epose (grow := Heqr). destruct (H b data fuel) as [mono0 sound0].
        eapply mono0 in grow as [P0 P1].
        destruct ((fix sem_repeat_none (n : nat) (x : X) {struct n} : MonSem X :=
            match n with
            | 0%nat => λ _ : span, NoFuel
            | S n0 =>
                λ s : span,
                  match
                    match run fuel (c x) data s with
                    | Res (s0, x1) => sem_repeat_none n0 x1 s0
                    | NoRes => NoRes
                    | NoFuel => NoFuel
                    end
                  with
                  | Res (s0, v) => Res (s0, v)
                  | NoRes => Res (s, x)
                  | NoFuel => NoFuel
                  end
            end) fuel0 x s0) eqn:?. destruct x0.
        * destruct (IHfuel0 X _ x data fuel H).
          epose (grow := Heqr0). eapply mono1 in grow as [P2 P3]. clear mono0 mono1.
          inversion H0. subst. iIntros. iNorm. iDestruct "HE" as "#HE".
          unfold injectSL. rewrite (inject_union (pos s0)). 2-3 : lia.
          iDestruct (big_sepS_union with "HG") as "[HB HA]". eapply inject_disjoint.
          iDestruct (sound0 with "[HC] HB") as ">HB". eapply Heqr.
          iDestruct ("HE" with "HC") as "HA". iApply (wp_consequence with "HA").
          iIntros (v0) "HA". iApply "HA".
          iApply (sound1 with "[HF HB] HA"). eauto. simpl. iExists x0.
          iFrame. iApply "HE".
        * eapply no_NoRes in Heqr0. contradiction.
        * inversion H0.
      + inversion H0. subst. iIntros. iNorm.
        iClear "HE". iApply "HF". iDestruct (injectSL_emp with "HG") as "HA". lia.
        iApply "HC".
      + inversion H0.
  Qed.

  Lemma repeat_None_soundness : forall fuel0 X (c : X -> NomG X) b data,
      (∀ (res : X) data fuel, Sound (run fuel (c res) data) (c res)) ->
      Sound (run fuel0 (Nom.repeat None c b) data) (Nom.repeat None c b).
  Proof.
    simpl. intros. constructor.
    - eapply bind_mono. eapply Monotone.test. intros. eapply run_mono. intro. eapply ret_mono.
    - simpl. intros. eapply repeat_none_soundness. eapply H.
      unfold_MonSem.
      destruct ((fix sem_repeat_none (n : nat) (x : X) {struct n} : MonSem X :=
       match n with
       | 0%nat => λ _ : span, NoFuel
       | S n0 =>
           λ s0 : span,
             match
               match run fuel0 (c x) data s0 with
               | Res (s1, x1) => sem_repeat_none n0 x1 s1
               | NoRes => NoRes
               | NoFuel => NoFuel
               end
             with
             | Res (s1, v0) => Res (s1, v0)
             | NoRes => Res (s0, x)
             | NoFuel => NoFuel
             end
       end) fuel0 b s) eqn:?. destruct x.
      + erewrite Heqr. auto.
      + inversion H0.
      + inversion H0.
  Qed.

  Lemma soundness : forall X (e : NomG X),
    forall (a : list atom) fuel, Sound (run fuel e a) e.
  Proof.

    Ltac rm_fuel fuel :=
      destruct fuel;
      [ let s := fresh "s" in
        let res := fresh "res" in
        let x := fresh "x" in
        let Q := fresh "Q" in
        let H := fresh "H" in
        constructor; [constructor; intros s res x H; inversion H |
                       intros s res x Q H; inversion H]
      | idtac].

    Ltac IsSound H fuel :=
      rm_fuel fuel; simpl run; eapply bind_soundness; [eapply H; auto; eapply run_mono | eauto].

    eapply (Nom_ind (fun X e => forall a fuel, Sound (run fuel e a) e)); intros.
    - destruct fuel; simpl; eapply ret_soundness.
    - rm_fuel fuel.
      simpl run. constructor. eapply fail_mono. intros. inversion H.
    - eapply bind_soundness. eapply length_soundness. intro. eapply H.
    - eapply bind_soundness. eapply take_soundness. intro. eapply H.
    - eapply bind_soundness. eapply read_soundness. intro. eapply H.
    - eapply bind_soundness. eapply alt_soundness. eapply H. eapply H0.
      intro. eapply H1.
    - eapply bind_soundness. eapply scope_soundness. eapply H.
      intro. eapply H0.
    - eapply bind_soundness. eapply peek_soundness. eapply H.
      intro. eapply H0.
    - destruct o.
      + constructor. eapply run_monotone. revert b.
        induction n using N.peano_ind; intros.
        * rewrite run_bind_monsem in H1. simpl in *.
          unfold_MonSem. iIntros "HA HB". iNorm.
          destruct (H0 b a fuel). iClear "HE". iApply (sound0 with "[HC HF] HB"). eauto.
          iApply ("HF" with "HC").
        * rewrite repeat_some_next_step in H1. rewrite run_bind_monsem in H1.
          simpl. iIntros "HA HB". iNorm. iDestruct "HE" as "#HE".
          unfold_MonSem.
          destruct (run fuel (c b) a s) eqn:?. destruct x0. 2-3 : inversion H1.
          destruct (H b a fuel).
          pose (grow := Heqr). eapply run_mono in grow as [P0 P1].
          pose (grow := H1). eapply run_mono in grow as [P2 P3].
          unfold injectSL. rewrite (inject_union (pos s0)). 2-3 : lia.
          iDestruct (big_sepS_union with "HB") as "[HB HA]". eapply inject_disjoint.
          iDestruct (sound0 with "[HC] HB") as ">HB". eapply Heqr.
          iDestruct ("HE" with "HC") as "HC". iApply (wp_consequence with "HC").
          iIntros (v0) "HA". iApply "HA".
          iApply (IHn with "[HF HB] HA"); eauto.
          simpl. iExists x. iFrame. iApply "HE".
      + eapply bind_soundness. 2 : intro. 2 : eapply H0.
        eapply repeat_none_soundness. eapply H.
  Qed.


  Lemma soundness_triple : forall X e H (Q : X -> iProp),
    forall (a : list atom) (v : X) s s' fuel,
      run fuel e a s = Res (s', v) ->
      ⊢ (H -∗ wp e (fun v => <absorb> Q v)) -∗
        H ∗ injectSL (pos s) (pos s') -∗ <absorb> Q v.
  Proof.
    intros. iIntros "HA [HB HC]". edestruct soundness.
    iApply (sound0 with "[HA HB] HC"). eauto.
    iApply ("HA" with "HB").
  Qed.

  Theorem soundness' : forall X e H (Q : X -> iProp) fuel,
      {{ H }} e {{ v; <absorb> Q v }} ->
      forall (a : list atom) (v : X) s s',
        run fuel e a s = Res (s', v) ->
        ⊢ H ∗ injectSL (pos s) (pos s') -∗ <absorb> Q v.
  Proof.
    intros X e H Q fuel triple a v s s' RUN.
    iApply soundness_triple. eapply RUN. iApply triple.
  Qed.

  Definition injectPos (start : N) (fin : N) : gset positive :=
    set_map encode (inject start fin).

  Lemma encode_disj : forall (B : gset N) n,
      n ∉ B -> ({[encode n]} : gset positive) ## set_map encode B.
  Proof.
    induction B as [ | n0 set not_in IH] using set_ind_L; simpl; intros.
    - rewrite set_map_empty. eapply disjoint_empty_r.
    - repeat intro. apply elem_of_singleton_1 in H0. subst.
      rewrite set_map_union_L in H1. apply elem_of_union in H1.
      destruct H1.
      + apply H. rewrite set_map_singleton_L in H0. apply elem_of_singleton in H0.
        apply elem_of_union. left. apply elem_of_singleton. apply encode_inj. apply H0.
      + assert (n ∉ set). intro. apply H. apply elem_of_union. right. apply H1.
        apply IH in H1.
        edestruct H1. eapply elem_of_singleton. reflexivity. eapply H0.
  Qed.


  Lemma lemma_final : forall start fin, && injectPos start fin ⊢ injectSL start fin.
  Proof.
    iIntros (start fin).
    unfold injectPos, injectSL.
    induction (inject start fin) as [ | A B C D] using set_ind_L; iIntros "HA".
    - rewrite set_map_empty. iApply big_sepS_empty. auto.
    - rewrite set_map_union_L. iDestruct (heap_ctx_split with "HA") as "[HA HB]".
      rewrite set_map_singleton. eapply encode_disj. eauto.
      iApply big_sepS_union. apply disjoint_singleton_l. auto.
      iSplitL "HA".
      + rewrite set_map_singleton_L. iApply big_sepS_singleton. iFrame.
      + iApply (D with "HB").
  Qed.

  Lemma adequacy : forall X e H (Q : X -> iProp),
      {{ H }} e {{ v; <absorb> Q v }} ->
      forall  (v : X) s' fuel (a : list atom) s,
        run fuel e a s = Res (s', v) ->
        (⊢ H) -> (<absorb> Q v) () (injectPos (pos s) (pos s')).
  Proof.
    intros. apply equivalence. iIntros "HA".
    iApply soundness'. eapply H0. eapply H1.
    iSplitR. iApply H2.
    iApply (lemma_final with "HA").
  Qed.

  Lemma adequacy' : forall X e (Q : X -> iProp) fuel,
      {{ emp }} e {{ v; <absorb> Q v }} ->
      forall (a : list atom) (v : X) s' s,
        run fuel e a s = Res (s', v) ->
        ∃ state, (<absorb> Q v) () state.
  Proof. intros. exists (injectPos (pos s) (pos s')). eapply adequacy; eauto. Qed.

  Corollary adequacy_pure : forall X e (Q : X -> Prop) fuel,
      {{ emp }} e {{ v; ⌜Q v⌝ }} ->
      forall (a : list atom) (v : X) s' s,
        run fuel e a s = Res (s', v) ->
        Q v.
  Proof.
    intros. eapply (consequence_rule e (fun v => <absorb> ⌜Q v⌝) _ emp emp) in H; eauto.
    eapply (adequacy' X e) in H as [state P]; eauto.
    eapply soundness_pure. eapply equivalence in P.
    iIntros "HA". iApply bi.absorbingly_pure. iApply (P with "HA").
  Qed.

  Corollary adequacy_equational_pure : forall X e (Q : X -> Prop),
      {{ emp }} e {{ v; ⌜Q v⌝ }} ->
      forall e', e ⩵ e' ->
      forall fuel (a : list atom) (v : X) s' s,
        run fuel e' a s = Res (s', v) ->
        Q v.
  Proof.
    intros. eapply (consequence_rule e (fun v => <absorb> ⌜Q v⌝) _ emp emp) in H; eauto.
    eapply (adequacy' X e) in H as [state P]; eauto.
    eapply soundness_pure. eapply equivalence in P.
    iIntros "HA". iApply bi.absorbingly_pure. iApply (P with "HA").
    rewrite H0. eauto.
  Qed.

End adequacy.
