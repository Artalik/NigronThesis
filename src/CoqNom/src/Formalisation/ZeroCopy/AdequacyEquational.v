From FreeMonad Require Import Nom ProgramLogic.

Section wp_law.

  Context {atom : Type}.

  Local Definition NomG := @NomG atom.

  Notation "e ⟛ e'" := (forall Q, wp e Q ⊣⊢ wp e' Q)(at level 95).

  (* Monad laws *)
  Lemma ret_id X (v: X) Y (f : X -> NomG Y) :
      let! v := ret v in f v ⟛ f v.
  Proof. reflexivity. Qed.

  Lemma id_ret X (e: NomG X):
    let! v := e in ret v ⟛ e.
  Proof.
    revert X e. fix IH 2. destruct e.
    - simpl. reflexivity.
    - destruct n; simpl.
      + trivial.
      + intro. iSplit; iIntros "HA" (v); iApply IH; iApply "HA".
      + intro. iSplit; iIntros "HA" (v); iApply IH; iApply "HA".
      + intro. iSplit; iIntros "HA" (v) "HB"; iApply IH; iApply ("HA" with "HB").
      + intro. iSplit; iIntros "HA"; iSplit.
        * iDestruct "HA" as "[HA _]". iApply (wp_consequence with "HA").
          iIntros (v) "HA". iApply IH. iApply "HA".
        * iDestruct "HA" as "[_ HA]". iApply (wp_consequence with "HA").
          iIntros (v) "HA". iApply IH. iApply "HA".
        * iDestruct "HA" as "[HA _]". iApply (wp_consequence with "HA").
          iIntros (v) "HA". iApply IH. iApply "HA".
        * iDestruct "HA" as "[_ HA]". iApply (wp_consequence with "HA").
          iIntros (v) "HA". iApply IH. iApply "HA".
      + destruct o.
        * intro.
          iSplit; iIntros "[HA HB]"; iFrame; iApply (wp_consequence with "HB");
            iIntros (v) "HA"; iApply IH; iApply "HA".
        * intro. iSplit; iIntros "HA" (v); iApply IH; iApply "HA".
      + intro.
        iSplit; iIntros "HA"; iNorm; iExists x0; iFrame; iIntros (res) "HA";
          iDestruct ("HE" with "HA") as "HA"; iApply IH; iApply "HA".
  Qed.


  Lemma id_ret X (e: NomG X):
    let! v := e in ret v ⟛ e.
  Proof.
    revert X e. fix IH 2. destruct e.
    - simpl. reflexivity.
    - destruct n; simpl.
      + trivial.
      + intro. iSplit; iIntros "HA" (v); iApply IH; iApply "HA".
      + intro. iSplit; iIntros "HA" (v); iApply IH; iApply "HA".
      + intro. iSplit; iIntros "HA" (v) "HB"; iApply IH; iApply ("HA" with "HB").
      + intro. iSplit; iIntros "HA"; iSplit.
        * iDestruct "HA" as "[HA _]". iApply (wp_consequence with "HA").
          iIntros (v) "HA". iApply IH. iApply "HA".
        * iDestruct "HA" as "[_ HA]". iApply (wp_consequence with "HA").
          iIntros (v) "HA". iApply IH. iApply "HA".
        * iDestruct "HA" as "[HA _]". iApply (wp_consequence with "HA").
          iIntros (v) "HA". iApply IH. iApply "HA".
        * iDestruct "HA" as "[_ HA]". iApply (wp_consequence with "HA").
          iIntros (v) "HA". iApply IH. iApply "HA".
      + destruct o.
        * intro.
          iSplit; iIntros "[HA HB]"; iFrame; iApply (wp_consequence with "HB");
            iIntros (v) "HA"; iApply IH; iApply "HA".
        * intro. iSplit; iIntros "HA" (v); iApply IH; iApply "HA".
      + intro.
        iSplit; iIntros "HA"; iNorm; iExists x0; iFrame; iIntros (res) "HA";
          iDestruct ("HE" with "HA") as "HA"; iApply IH; iApply "HA".
  Qed.



  Lemma bind_assoc : forall X Y Z (e : NomG X) f (g : Y -> NomG Z),
    (let! v := e in
    let! v' := f v in
    g v') ⩵
      let! v' :=
        let! v := e in
        f v in
      g v'.
  Proof.
    intros. repeat rewrite run_bind_monsem. unfold_MonSem.
    rewrite run_bind_monsem. unfold_MonSem. destruct (run fuel e data s); auto.
    destruct x. rewrite run_bind_monsem. reflexivity.
  Qed.


  (* Error Laws *)
  Lemma fail_absorb_left X Y (f : X -> NomG Y) :
    let! v := fail in f v ⩵ fail.
  Proof. reflexivity. Qed.

  Lemma id_fail X (e : NomG X) :
    alt fail e ⩵ e.
  Proof.
    intros. unfold run. simpl. rewrite ret_neutral_right.
    unfold run_alt. unfold_MonSem. simpl. reflexivity.
  Qed.

  Lemma fail_id X (e : NomG X) :
    alt e fail ⩵ e.
  Proof.
    intros. unfold run. simpl. rewrite ret_neutral_right.
    unfold run_alt. unfold_MonSem. simpl. rewrite ret_neutral_right.
    unfold_MonSem. fold (NomG_to_sem fuel e).
    destruct (run_sem (NomG_to_sem fuel e) data s); try reflexivity.
    destruct x. reflexivity.
  Qed.

  Lemma alt_assoc X (e m k : NomG X) :
    alt e (alt m k) ⩵ alt (alt e m) k.
  Proof.
    intros. unfold run. simpl. fold (NomG_to_sem fuel e).
    fold (NomG_to_sem fuel k). fold (NomG_to_sem fuel m).
    unfold run_alt. simpl. unfold run_alt. unfold_MonSem.
    destruct (run_sem (NomG_to_sem fuel e) data s) as [[e0 e1] | |];
      destruct (run_sem (NomG_to_sem fuel m) data s) as [[m0 m1] | |];
      destruct (run_sem (NomG_to_sem fuel k) data s) as [[k0 k1] | |];auto.
  Qed.

  (* Length laws *)

  Lemma length_length X (k : N -> N -> NomG X) :
    (let! len := length in
    let! len0 := length in
    k len len0) ⩵
      let! len := length in
      k len len.
  Proof. reflexivity. Qed.

  Lemma read_read X s n (k : atom -> atom -> NomG X) :
    (let! v := read s n in
    let! v0 := read s n in
    k v v0) ⩵
      let! v := read s n in
      k v v.
  Proof.
    intros. unfold run. simpl.
    unfold run_read. unfold_MonSem.
    destruct (n <? len s); auto.
    destruct (lookupN data (pos s + n) s0) as [[v0 v1]| |]eqn:?; auto.
    fold (NomG_to_sem fuel (k v1 v1)).
    eapply lookupN_eq_span in Heqr as P0. subst. rewrite Heqr.
    fold (NomG_to_sem fuel (k v1 v1)). reflexivity.
  Qed.

  Lemma absorb_length (e : NomG N) :
    alt length e ⩵ length.
  Proof. reflexivity. Qed.

  Lemma read_commutatif X s t n m (k : atom -> atom -> NomG X) :
    (let! v := read s n in
    let! v0 := read t m in
    k v v0) ⩵
      (let! v0 := read t m in
       let! v := read s n in
       k v v0).
  Proof.
    intros. unfold run. simpl.
    unfold run_read. unfold_MonSem.
    destruct (n <? len s); auto.
    destruct (lookupN data (pos s + n) s0) as [[v0 v1]| |]eqn:?; auto.
    destruct (m <? len t); auto.
    destruct (lookupN data (pos t + m) v0) as [[v2 v3]| |]eqn:?; auto.
    eapply lookupN_eq_span in Heqr as P0.
    eapply lookupN_eq_span in Heqr0 as P1. subst.
    rewrite Heqr0 Heqr. reflexivity.
    eapply lookupN_eq_span in Heqr as P0. subst. rewrite Heqr0. reflexivity.
    eapply lookupN_eq_span in Heqr as P0. subst. rewrite Heqr0. reflexivity.
    destruct (m <? len t); auto.
    destruct (lookupN data (pos t + m) s0) as [[v2 v3]| |]eqn:?; auto.
    eapply lookupN_eq_span in Heqr0 as P0. subst. rewrite Heqr. reflexivity.
    exfalso. eapply lookupN_NoFuel. eapply Heqr0.
    exfalso. eapply lookupN_NoFuel. eapply Heqr.
    destruct (m <? len t); auto.
    destruct (lookupN data (pos t + m) s0) as [[v0 v1] | |] eqn:?; auto.
    exfalso. eapply lookupN_NoFuel. eapply Heqr.
  Qed.

  Lemma length_read_commutatif X s n (k : atom -> N -> NomG X) :
    (let! v := read s n in
    let! len := length in
    k v len) ⩵
      (let! len := length in
       let! v := read s n in
       k v len).
  Proof.
    intros. unfold run. simpl.
    unfold run_read, run_length. unfold_MonSem.
    destruct (n <? len s); auto.
    destruct (lookupN data (pos s + n) s0) as [[v0 v1]| |]eqn:?; auto.
    eapply lookupN_eq_span in Heqr as P0. subst. reflexivity.
  Qed.

  Lemma read_take_commutatif X s n m (k : atom -> span -> NomG X) :
    (let! v := read s n in
    let! r := take m in
    k v r) ⩵
      (let! r := take m in
       let! v := read s n in
       k v r).
  Proof.
    intros. unfold run. simpl.
    unfold run_read, run_take. unfold_MonSem.
    destruct (n <? len s); auto.
    destruct (lookupN data (pos s + n) s0) as [[v0 v1]| |]eqn:?; auto.
    eapply lookupN_eq_span in Heqr as P0. subst.
    destruct (m <=? len v0) eqn:?.
    erewrite lookupN_indep_state_res; eauto. reflexivity.
    destruct (m <=? len s0) eqn:?.
    erewrite lookupN_indep_state_NoRes; eauto. reflexivity.
    exfalso. eapply lookupN_NoFuel; eauto.
    destruct (m <=? len s0) eqn:?; reflexivity.
  Qed.

  Lemma test m s n :
    (let! r := take m in
     let! v := read s n in
     ret v : NomG atom) ⩵
      (let! v := read s n in
       let! r := take m in
       ret v).
  Proof. Rewrite read_take_commutatif. reflexivity. Qed.


  Lemma test2 m s n :
    (let! r := take m in
     let! v := read s n in
     let! _ := read s n in
     ret v : NomG atom) ⩵
      (let! v := read s n in
       let! r := take m in
       let! _ := read s n in
       ret v).
  Proof. Rewrite read_take_commutatif. reflexivity. Qed.


  (* take-length laws *)

  Lemma length_take_comm_add n X (k : N -> span -> NomG X) :
    (let! len := length in
     let! s := take n in
     k len s) ⩵
      let! s := take n in
      let! len := length in
      k (len + n) s.
  Proof.
    intros. unfold run. simpl.
    unfold run_length, run_take. unfold_MonSem.
    destruct (n <=? len s0) eqn:?; auto. simpl. rewrite N.sub_add. reflexivity.
    eapply N.leb_le. auto.
  Qed.

  Lemma length_take_comm_sub n X (k : N -> span -> NomG X) :
    (let! s := take n in
     let! len := length in
     k len s) ⩵
      let! len := length in
      let! s := take n in
      k (len - n) s.
  Proof.
    intros. unfold run. simpl.
    unfold run_length, run_take. unfold_MonSem.
    destruct (n <=? len s0) eqn:?; auto.
  Qed.

  Lemma bind_eq : forall X Y (e e': NomG X) (k k' : X -> NomG Y),
        e ⩵ e' ->
        (forall v, k v ⩵ k' v) ->
        let! v := e in k v ⩵ let! v := e' in k' v.
  Proof.
    intros. repeat rewrite run_bind_monsem.
    unfold_MonSem. rewrite H. destruct run as [[a b]| | ]; try reflexivity.
    rewrite H0. reflexivity.
  Qed.

  Lemma bind_eq_2 : forall X Y (e : NomG X) (k k' k'': X -> NomG Y),
      (forall v, k v ⩵ k'' v) ->
      (let! v := e in k'' v ⩵ let! v := e in k' v) ->
      let! v := e in k v ⩵ let! v := e in k' v.
  Proof.
    intros.
    pose (H0 fuel data s).
    repeat erewrite run_bind_monsem in e0.
    unfold_MonSem.
    destruct run as [[a b]| |] eqn:?; repeat erewrite run_bind_monsem;
      unfold_MonSem; rewrite Heqm; try reflexivity.
    rewrite H. rewrite e0. reflexivity.
  Qed.

  Lemma refl X (e : NomG X) : e ⩵ e. Proof. reflexivity. Qed.

  Ltac Step :=
    eapply bind_eq; [ reflexivity| intro].

  Ltac Intern :=
    eapply bind_eq_2; [ intro | idtac ].

  Lemma length_take_length n X (k : N -> span -> N -> NomG X) :
    (let! len := length in
     let! s := take n in
     let! len0 := length in
     k len s len0) ⩵
      let! len := length in
      let! s := take n in
      k len s (len - n).
  Proof.
    Rewrite length_take_comm_add.
    Rewrite length_take_comm_add.
    Step. Rewrite length_length.
    Step. rewrite N.add_sub. reflexivity.
  Qed.

  Lemma length_take_0 X (k : N -> span -> N -> NomG X) :
    (let! len := length in
    let! s := take len in
    let! len0 := length in
    k len s len0) ⩵
      let! len := length in
      let! s := take len in
      k len s 0.
  Proof.
    Intern. Rewrite length_take_comm_sub. reflexivity.
    cbv beta. Rewrite length_length.
    Step. Step. rewrite N.sub_diag. reflexivity.
  Qed.

  (* Laws Scope *)

  Lemma Scope_ret X v o :
    Scope o (ret v : NomG X) ⩵ ret v.
  Proof. destruct o; reflexivity. Qed.

  Lemma Scope_fail X o :
    Scope o (fail: NomG X) ⩵ fail.
  Proof. destruct o; reflexivity. Qed.

  Lemma Scope_length :
    Scope None (length: NomG N) ⩵ length.
  Proof. reflexivity. Qed.

  Lemma Scope_read o s n:
    Scope o (read s n : NomG atom) ⩵ read s n.
  Proof.
    destruct o; unfold run; intros; simpl; repeat rewrite ret_neutral_right.
    + unfold run_scope. simpl. unfold run_read. unfold_MonSem.
      destruct (n <? len s); try reflexivity.
      destruct (lookupN data (pos s + n)) as [[a b] | |] eqn:?.
      erewrite lookupN_indep_state_res; eauto.
      erewrite lookupN_indep_state_NoRes; eauto.
      exfalso. eapply lookupN_NoFuel. eauto.
    + unfold run_peek. simpl. unfold run_read. unfold_MonSem.
      destruct (n <? len s); try reflexivity.
      destruct (lookupN data (pos s + n)) as [[a b] | |] eqn:?; try reflexivity.
      erewrite <- lookupN_indep_state_res; eauto.
  Qed.

  Lemma Scope_scope X (e : NomG X) o s2:
    Scope o (Scope (Some s2) e) ⩵ scope s2 e.
  Proof.
    unfold run; intros; simpl; fold (NomG_to_sem fuel e). repeat rewrite ret_neutral_right.
    destruct o; unfold run_scope, run_peek; simpl; unfold run_scope; unfold_MonSem;
    destruct (run_sem (NomG_to_sem fuel e) data s2) as [[a b]| |]; reflexivity.
  Qed.

  Lemma Scope_peek X (e : NomG X) o:
    Scope o (Scope None e) ⩵ Scope o e.
  Proof.
    unfold run; intros; simpl; fold (NomG_to_sem fuel e). repeat rewrite ret_neutral_right.
    destruct o; unfold run_scope, run_peek; simpl; unfold run_peek; unfold_MonSem.
    destruct (run_sem (NomG_to_sem fuel e) data s0) as [[a b]| |]; reflexivity.
    destruct (run_sem (NomG_to_sem fuel e) data s) as [[a b]| |]; reflexivity.
  Qed.

  Lemma Scope_alt_distrib X o (e1 e2 : NomG X):
     Scope o (alt e1 e2) ⩵ alt (Scope o e1) (Scope o e2).
  Proof.
    destruct o; unfold run; intros; simpl;
      fold (NomG_to_sem fuel e1); fold (NomG_to_sem fuel e2).
    + repeat rewrite ret_neutral_right. unfold run_scope, run_alt.
      simpl. unfold run_alt, run_scope. unfold_MonSem.
      destruct (run_sem (NomG_to_sem fuel e1) data s) as [[a b]| |]; try reflexivity.
      destruct (run_sem (NomG_to_sem fuel e2) data s) as [[a b]| |]; try reflexivity.
    + repeat rewrite ret_neutral_right. unfold run_peek, run_alt.
      simpl. unfold run_alt, run_peek. unfold_MonSem.
      destruct (run_sem (NomG_to_sem fuel e1) data s) as [[a b]| |]; try reflexivity.
      destruct (run_sem (NomG_to_sem fuel e2) data s) as [[a b]| |]; try reflexivity.
  Qed.

  Lemma repeat_0 X (e: X -> NomG X) v:
      repeat (Some 0) e v ⩵ ret v.
  Proof. reflexivity. Qed.

  Lemma repeat_n_ret n X v :
      repeat (Some n) (ret : X -> NomG X) v ⩵ ret v.
  Proof.
    induction n using N.peano_ind.
    - Rewrite repeat_0. reflexivity.
    - unfold run. intros. simpl. unfold_MonSem.
      rewrite <- N.succ_pos_spec. rewrite REPEAT_to_sem_equation_2.
      rewrite N.succ_pos_spec. rewrite N.pred_succ.
      simpl. rewrite ret_neutral_left. unfold run in IHn.
      simpl in IHn. unfold_MonSem. rewrite IHn; auto.
  Qed.

  Lemma unfold_repeat_n n X (e : X -> NomG X) b :
    repeat (Some (N.succ n)) e b ⩵
      let! v := e b in repeat (Some n) e v.
  Proof.
    intros. rewrite run_bind_monsem. unfold run.
    rewrite <- N.succ_pos_spec. simpl. rewrite REPEAT_to_sem_equation_2.
    rewrite N.succ_pos_spec. rewrite N.pred_succ.
    repeat rewrite ret_neutral_right. simpl.
    fold (NomG_to_sem fuel (e b)). eapply run_bind_eq. reflexivity.
    intros. rewrite ret_neutral_right. reflexivity.
  Qed.

  (* Laws not respected *)

  Lemma repeat_fail X v : repeat None (fun _ => fail : NomG X) v ⩵ ret v.

  Lemma repeat_fail X (e : X -> NomG X ) b :
    repeat None e b ⩵ alt (let! v := e b in repeat None e v) (ret b).

End wp_law.
