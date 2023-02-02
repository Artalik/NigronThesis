From Formalisation Require Import Span Inject ProgramLogic Monotone adequacy FuelMono ZeroCopy.
Require Import Coq.Program.Equality.
From Equations Require Import Equations.

Section Safe.

  Context {atom : Type}.

  Open Scope N_scope.

  Lemma Fresh_Safe_aux `{Foldable X}: forall e s n s_res,
      {{ injectSL n (pos s) }} e {{ res; <absorb> all_disjointMSL res }} ->
      forall (data : list atom) fuel  (res : X span),
        n <= pos s ->
        run fuel e data s = Res (s_res, res) ->
        forall v, v ∈ M_to_list res ->
             set_span v ⊆ inject n (pos s + len s).
  Proof.
    revert X H. fix IH 3. intros X H e.
    dependent destruction e; intros; simpl in *. revert H1 H2. intros LE H1.
    - inversion H1. subst. clear H1.
      revert H0. MonPred.unseal. unfold monpred.monPred_wand_def. simpl.
      unfold monpred.monPred_upclosed. simpl. intro. destruct H0. simpl in *.
      edestruct (monPred_in_entails tt). clear monPred_in_entails.
      instantiate (1 := ∅). MonPred.unseal.
      split. split. inversion_star h P. clear H0.
      red in P1. destruct P1. inversion H1. subst. clear H1. clear P2.
      rewrite union_empty_r_L in P. clear monPred_in_entails. subst.
      edestruct H0.
      + eexists ∅, _. repeat split; auto. 2 : eapply disjoint_empty_l.
        eapply SepSet.soundness. iIntros "HA". iApply big_op_ctx. iApply "HA".
      + destruct H1 as [h [P3 [P1 [P2 P4]]]]. clear H0 P0 P3.
        rewrite union_empty_l_L in P4.
        transitivity (inject n (Span.pos s_res)).
        2 : { eapply inject_mono_r. lia. }
        rewrite P4. transitivity h. 2 : set_solver. clear P2 P4. unfold all_disjointMSL in P1.
        eapply (all_disjointSL_incl _ _ H3 _ P1).
    - destruct n; simpl in *.
      + inversion H2.
      + unfold_MonSem. eapply IH; eauto.
        iIntros "HA". iDestruct (H0 with "HA") as "HB". iApply "HB".
      + unfold_MonSem. destruct (run_read s0 n data s) as [[s_i i]| |] eqn:?.
        eapply run_read_eq_span in Heqr. subst.
        eapply IH; eauto.
        iIntros "HA". iDestruct (H0 with "HA") as "HB". iApply "HB".
        inversion H2. inversion H2.
      + unfold set_span.
        unfold_MonSem. unfold run_take in H2. unfold_MonSem.
        destruct (n <=? len s) eqn:?.
        * pose (mono := H2). eapply run_mono in mono as [P0 P1]. simpl in *.
          eapply N.leb_le in Heqb. assert (pos s + len s = pos s + n + (len s - n)) by lia.
          rewrite H4.
          unfold set_span in IH.
          eapply (IH _ _ _ {| pos := pos s + n; len := len s - n |}); simpl in *; eauto.
          2 : lia.
          iIntros "HA". unfold injectSL. rewrite (inject_add n n1 (pos s)). 2 : lia.
          iDestruct (big_sepS_union with "HA") as "[HA HB]". eapply inject_disjoint.
          iDestruct (inject_IsFresh with "[HB]") as "HB"; eauto.
          unfold injectSL. instantiate (1 := (mk_span (pos s) n)). simpl. iApply "HB".
          iApply (H0 with "HA HB").
        * inversion H2.
      + unfold set_span. unfold_MonSem.
        destruct (run fuel n data s) as [[s_t t]| |] eqn:?.
        * pose (mono_n := Heqr). eapply run_mono in mono_n as [P0 P1].
          transitivity (inject n1 (pos s_t + len s_t)).
          2 : { eapply inject_mono_r. lia. }
          eapply IH. 3 : eapply H2. 2 : lia. 2 : auto.
          iIntros "HA". unfold injectSL.
          rewrite (inject_union (pos s) n1). 2-3 : lia.
          iDestruct (big_sepS_union with "HA") as "[HA HB]". eapply inject_disjoint.
          iDestruct (H0 with "HA") as "[HA _]".
          destruct (soundness X0 n data fuel).
          iDestruct (sound with "[HA] [HB]") as "HA". eapply Heqr.
          iApply (wp_consequence with "HA"). iIntros (v0) "HA". iModIntro. iApply "HA".
          auto. simpl. iApply (wp_absorb_out with "HA").
        * destruct (run fuel n2 data s) as [[s_t t]| |] eqn:?.
          -- pose (mono_n2 := Heqr0). eapply run_mono in mono_n2 as [P0 P1].
             transitivity (inject n1 (pos s_t + len s_t)).
             2 : { eapply inject_mono_r. lia. }
             eapply IH. 3 : eapply H2. 2 : lia. 2 : auto.
             iIntros "HA". unfold injectSL.
             rewrite (inject_union (pos s) n1). 2-3 : lia.
             iDestruct (big_sepS_union with "HA") as "[HA HB]". eapply inject_disjoint.
             iDestruct (H0 with "HA") as "[_ HA]".
             destruct (soundness X0 n2 data fuel).
             iDestruct (sound with "[HA] [HB]") as "HA". eapply Heqr0.
             iApply (wp_consequence with "HA"). iIntros (v0) "HA". iModIntro. iApply "HA".
             auto. simpl. iApply (wp_absorb_out with "HA").
          -- inversion H2.
          -- inversion H2.
        * inversion H2.
      + unfold_MonSem. destruct o.
        * destruct (run fuel n data s0) as [[s_t t]| |]eqn:?.
          -- eapply IH. 2 : lia. 2 : eapply H2. 2 : auto.
             iIntros "HA". iDestruct (H0 with "HA") as "[HA HB]".
             iDestruct (IsFresh_injectSL with "HA") as "HA".
             iApply wp_absorb_out.
             pose (mono_n := Heqr). eapply run_mono in mono_n as [P0 P1].
             unfold injectSL. rewrite (inject_union (pos s_t) (pos s0)).
             iDestruct (big_sepS_union with "HA") as "[HA _]". eapply inject_disjoint.
             destruct (soundness X0 n data fuel).
             iDestruct (sound with "[HB] HA") as "HB"; eauto.
             iApply (wp_consequence with "HB"). auto. auto. lia. lia.
          -- inversion H2.
          -- inversion H2.
        * destruct (run fuel n data s) as [[s_t t]| |]eqn:?.
          -- eapply IH. 2 : lia. 2 : eapply H2. 2 : auto.
             iIntros "HA". iApply (H0 with "HA").
          -- inversion H2.
          -- inversion H2.
      + destruct o; unfold_MonSem.
        * revert x s H0 H1 H2.  induction (N.to_nat n2).
          -- intros. eapply IH. 2 : lia. 2 : eapply H2. 2 : auto.
             iIntros "HA". iDestruct (H0 with "HA") as (Q) "[HA [HB HC]]".
             iApply wp_absorb_out. iClear "HB". iModIntro. iApply ("HC" with "HA").
          -- intros. destruct (run fuel (n x) data s) as [[s_t t]| |] eqn:?.
             ++ pose (mono := Heqr). eapply run_mono in mono as [P0 P1].
                transitivity (inject n1 (pos s_t + len s_t)).
                2 : { eapply inject_mono_r. lia. }
                eapply IHn3 in H2. auto.
                iIntros "HA". unfold injectSL.
                rewrite (inject_union (pos s) n1). 2-3 : lia.
                iDestruct (big_sepS_union with "HA") as "[HA HB]". eapply inject_disjoint.
                iDestruct (H0 with "HA") as (Q) "[HA [#HD HC]]".
                iExists Q. iDestruct ("HD" with "HA") as "HA".
                destruct (soundness X0 (n x) data fuel).
                iDestruct (sound with "[HA] HB") as "HA"; eauto.
                iApply (wp_consequence with "HA"). iIntros (v0) "HA". iApply "HA".
                iDestruct "HA" as ">HA". iFrame. auto. lia.
             ++ inversion H2.
             ++ inversion H2.
        * assert (exists fuel0, fuel0 = fuel). exists fuel. reflexivity.
          destruct H4. rewrite <- H4 in H2 at 1. clear H4. revert x s H0 H1 H2. induction x0.
          -- intros. inversion H2.
          -- intros. destruct (run fuel (n x) data s) as [[s_t t] | | ] eqn:?.
             ++ pose (mono := Heqr). eapply run_mono in mono as [P0 P1].
                transitivity (inject n1 (pos s_t + len s_t)).
                2 : { eapply inject_mono_r. lia. }
                eapply IHx0. instantiate (1 := t).
                iIntros "HA". unfold injectSL.
                rewrite (inject_union (pos s) n1). 2-3 : lia.
                iDestruct (big_sepS_union with "HA") as "[HA HB]". eapply inject_disjoint.
                iDestruct (H0 with "HA") as (Q) "[HA [#HD HC]]".
                iExists Q. iFrame. destruct (soundness X0 (n x) data fuel).
                iDestruct ("HD" with "HA") as "HA".
                iDestruct (sound with "[HA] HB") as "HA"; eauto.
                iApply (wp_consequence with "HA"). iIntros (v0) "HA". iApply "HA".
                iDestruct "HA" as ">HA". iFrame. auto. lia.
                destruct ((fix sem_repeat_none (n2 : nat) (x0 : X0) {struct n2} : MonSem X0 :=
                            match n2 with
                            | 0%nat => λ _ : span, NoFuel
                            | S n3 =>
                                λ s0 : span,
                                  match
                                    match run fuel (n x0) data s0 with
                                    | Res (s1, x2) => sem_repeat_none n3 x2 s1
                                    | NoRes => NoRes
                                    | NoFuel => NoFuel
                                    end
                                  with
                                  | Res (s1, v0) => Res (s1, v0)
                                  | NoRes => Res (s0, x0)
                                  | NoFuel => NoFuel
                                  end
                            end) x0 t s_t) as [[s_b b]| |] eqn:?; auto.
                eapply no_NoRes in Heqr0. contradiction.
             ++ eapply IH. 2 : auto. 2 : apply H2. 2 : auto.
                iIntros "HA". iDestruct (H0 with "HA") as (Q) "[HA [HB HC]]".
                iApply wp_absorb_out. iClear "HB". iModIntro. iApply ("HC" with "HA").
             ++ inversion H2.
  Qed.

  Lemma Fresh_Safe `{Foldable X} e :
      {{ emp }} e {{ res; <absorb> all_disjointMSL res }} ->
      forall (data : list atom) fuel (res : X span) s s_res,
        run fuel e data s = Res (s_res, res) ->
        Result_in res s.
  Proof.
    unfold Result_in. intros. eapply Fresh_Safe_aux. iIntros "HA". iApply H0.
    iApply (injectSL_emp with "HA"). lia. lia. eauto. auto.
  Qed.

  Definition Res_to_option {X Y} (r: Result (X * Y)) : option Y :=
    match r with
    | Res (_, r) => Some r
    | _ => None
    end.

  Lemma Fresh_is_Safe `{fold:Foldable M} (e : @NomG atom (M span)) :
    {{ emp }} e {{ res; <absorb> all_disjointMSL res }} ->
    forall data fuel, WeakZC (fun s => Res_to_option (run fuel e data s)).
  Proof.
    unfold WeakZC. intros TRIPLE data fuel s res PARSE v IN.
    destruct (run fuel) as [[x r]| |] eqn:?. inversion PARSE. subst.
    eapply Fresh_Safe. eapply TRIPLE. eapply Heqm. eapply IN.
    inversion PARSE. inversion PARSE.
  Qed.

  Definition parse_Safe `{Foldable M} (e : @NomG atom (M span)) := forall fuel data res,
      parse e fuel data = Some res ->
      Result_in res (mk_span 0 (lengthN data)).

  Lemma parse_is_Safe `{Foldable M} (e : @NomG atom (M span)) :
    {{ emp }} e {{ res; <absorb> all_disjointMSL res }} ->
    parse_Safe e.
  Proof.
    unfold parse_Safe. intros TRIPLE fuel data res PARSE v IN.
    eapply Fresh_is_Safe. eapply TRIPLE. eapply PARSE. eapply IN.
  Qed.

  Close Scope N_scope.

End Safe.

Print Assumptions parse_Safe.
