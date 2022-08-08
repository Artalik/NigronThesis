From Formalisation Require Import Nom FuelMono.

Notation "e ⩵ e'" := (forall fuel data s res1 res2,
                         run fuel e data s = res1 ->
                         run fuel e' data s = res2 ->
                         res1 <> NoFuel ->
                         res2 <> NoFuel ->
                         res1 = res2) (at level 95).

Section laws.

  Context {atom : Type}.

  Local Definition NomG := @NomG atom.

  (* Monad laws *)
  Lemma ret_id X (v: X) Y (f : X -> NomG Y) :
      let! v := ret v in f v ⩵ f v.
  Proof. intros. rewrite -H0 H //. Qed.

  Lemma id_ret X (e: NomG X):
    let! v := e in ret v ⩵ e.
  Proof.
    intros. rewrite -H0 -H (@run_bind_monsem atom) ret_neutral_right //.
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
    intros. rewrite -H0 -H. repeat rewrite run_bind_monsem. unfold_MonSem.
    rewrite run_bind_monsem. unfold_MonSem. destruct (run fuel e data s); auto.
    destruct x. repeat rewrite run_bind_monsem. unfold_MonSem.
    reflexivity.
  Qed.


  (* Error Laws *)
  Lemma fail_absorb_left X Y (f : X -> NomG Y) :
    let! v := fail in f v ⩵ fail.
  Proof. intros. rewrite -H0 -H //. Qed.

  Lemma id_fail X (e : NomG X) :
    alt fail e ⩵ e.
  Proof.
    intros. rewrite -H0 -H. unfold run. simpl. rewrite ret_neutral_right. reflexivity.
  Qed.

  Lemma fail_id X (e : NomG X) :
    alt e fail ⩵ e.
  Proof.
    intros. rewrite -H0 -H. simpl. rewrite ret_neutral_right.
    unfold run_alt. unfold_MonSem. simpl. rewrite ret_neutral_right.
    unfold_MonSem. destruct (run fuel e) as [[a b]| |]; auto.
  Qed.

  Lemma alt_assoc X (e m k : NomG X) :
    alt e (alt m k) ⩵ alt (alt e m) k.
  Proof.
    intros. rewrite -H0 -H. simpl. unfold run_alt. simpl. unfold run_alt. unfold_MonSem.
    destruct (run fuel e data s) as [[e0 e1] | |];
      destruct (run fuel m data s) as [[m0 m1] | |];
      destruct (run fuel k data s) as [[k0 k1] | |]; auto.
  Qed.

  Lemma alt_ret {X} (e : NomG X) v:
    alt (ret v) e ⩵ ret v.
  Proof. intros. rewrite -H0 -H //. Qed.

  Lemma alt_length (e : NomG N) :
    alt length e ⩵ length.
  Proof. intros. rewrite -H0 -H //. Qed.


  (* Length laws *)

  Lemma length_length X (k : N -> N -> NomG X) :
    (let! len := length in
    let! len0 := length in
    k len len0) ⩵
      let! len := length in
      k len len.
  Proof. intros. rewrite -H0 -H //. Qed.

  Lemma read_read X s n (k : atom -> atom -> NomG X) :
    (let! v := read s n in
    let! v0 := read s n in
    k v v0) ⩵
      let! v := read s n in
      k v v.
  Proof.
    intros. rewrite -H0 -H. simpl. unfold run_read. unfold_MonSem.
    destruct (n <? len s); auto.
    destruct (lookupN data (pos s + n) s0) as [[v0 v1]| |]eqn:?; auto.
    eapply lookupN_eq_span in Heqr as P0. subst. rewrite Heqr. reflexivity.
  Qed.

  Lemma read_commutatif X s t n m (k : atom -> atom -> NomG X) :
    (let! v := read s n in
    let! v0 := read t m in
    k v v0) ⩵
      (let! v0 := read t m in
       let! v := read s n in
       k v v0).
  Proof.
    intros. rewrite -H0 -H. simpl. unfold run_read. unfold_MonSem.
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
    intros. rewrite -H0 -H. simpl.
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
    intros. rewrite -H0 -H. simpl. unfold run_read, run_take. unfold_MonSem.
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

  (* take-length laws *)

  Lemma length_take_comm_add n X (k : N -> span -> NomG X) :
    (let! len := length in
     let! s := take n in
     k len s) ⩵
      let! s := take n in
      let! len := length in
      k (len + n) s.
  Proof.
    intros. rewrite -H0 -H. simpl. unfold run_length, run_take. unfold_MonSem.
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
    intros. rewrite -H0 -H. simpl. unfold run_length, run_take. unfold_MonSem.
    destruct (n <=? len s0) eqn:?; auto.
  Qed.

  (* Local Laws *)

  Lemma local_ret X v o :
    local o (ret v : NomG X) ⩵ ret v.
  Proof. destruct o; intros; rewrite -H0 -H //. Qed.

  Lemma local_fail X o :
    local o (fail: NomG X) ⩵ fail.
  Proof. destruct o; intros; rewrite -H0 -H //. Qed.

  Lemma local_read o s n:
    local o (read s n : NomG atom) ⩵ read s n.
  Proof.
    intros. rewrite -H0 -H.
    destruct o; unfold run; intros; simpl; repeat rewrite ret_neutral_right.
    + unfold run_local. simpl. unfold run_read. unfold_MonSem.
      destruct (n <? len s); try reflexivity.
      destruct (lookupN data (pos s + n)) as [[a b] | |] eqn:?.
      erewrite lookupN_indep_state_res; eauto.
      erewrite lookupN_indep_state_NoRes; eauto.
      exfalso. eapply lookupN_NoFuel. eauto.
    + unfold run_local. simpl. unfold run_read. unfold_MonSem.
      destruct (n <? len s); try reflexivity.
      destruct (lookupN data (pos s + n)) as [[a b] | |] eqn:?; try reflexivity.
      erewrite <- lookupN_indep_state_res; eauto.
  Qed.

  Lemma peek_length :
    local None (length: NomG N) ⩵ length.
  Proof. intros. rewrite -H0 -H //. Qed.


  Lemma local_scope X (e : NomG X) o s2:
    local o (local (Some s2) e) ⩵ scope s2 e.
  Proof.
    intros. rewrite -H0 -H. simpl. repeat rewrite ret_neutral_right.
    destruct o; unfold run_local; simpl; unfold run_local; unfold_MonSem;
    destruct (run fuel e data s2) as [[a b]| |]; reflexivity.
  Qed.

  Lemma local_peek X (e : NomG X) o:
    local o (local None e) ⩵ local o e.
  Proof.
    intros. rewrite -H0 -H. simpl. repeat rewrite ret_neutral_right.
    destruct o; unfold run_local; simpl; unfold_MonSem.
    destruct (run fuel e data s0) as [[a b]| |]; reflexivity.
    destruct (run fuel e data s) as [[a b]| |]; reflexivity.
  Qed.

  Lemma local_alt_distrib X o (e1 e2 : NomG X):
     local o (alt e1 e2) ⩵ alt (local o e1) (local o e2).
  Proof.
    destruct o; intros; rewrite -H0 -H; simpl.
    + repeat rewrite ret_neutral_right. unfold run_local, run_alt.
      simpl. unfold run_alt, run_local. unfold_MonSem.
      destruct (run fuel e1 data s) as [[a b]| |]; try reflexivity.
      destruct (run fuel e2 data s) as [[a b]| |]; try reflexivity.
    + repeat rewrite ret_neutral_right. unfold run_local, run_alt.
      simpl. unfold run_alt, run_local. unfold_MonSem.
      destruct (run fuel e1 data s) as [[a b]| |]; try reflexivity.
      destruct (run fuel e2 data s) as [[a b]| |]; try reflexivity.
  Qed.

  Lemma repeat_0 X (e: X -> NomG X) v:
      repeat (Some 0) e v ⩵ ret v.
  Proof. intros. rewrite -H0 -H //. Qed.

  Lemma repeat_n_ret n X v :
      repeat (Some n) (ret : X -> NomG X) v ⩵ ret v.
  Proof.
    induction n using N.peano_ind.
    - eapply repeat_0.
    - intros. simpl in *. unfold_MonSem.
      rewrite N2Nat.inj_succ in H.
      eapply IHn; eauto.
  Qed.

  Lemma unfold_repeat_n n X (e : X -> NomG X) b :
    repeat (Some (N.succ n)) e b ⩵
      let! v := e b in repeat (Some n) e v.
  Proof.
    intros. rewrite -H0 -H. rewrite run_bind_monsem. simpl.
    rewrite N2Nat.inj_succ. rewrite ret_neutral_right. eapply run_bind_eq. reflexivity.
    intros. rewrite ret_neutral_right. reflexivity.
  Qed.

  (* Laws not respected *)

  Lemma repeat_fail_ret X v : repeat None (fun _ => fail : NomG X) v ⩵ ret v.
  Proof.
    intros. rewrite -H0 -H. simpl. destruct fuel.
    - simpl in *. unfold_MonSem. subst. contradiction.
    - simpl in *. unfold_MonSem. reflexivity.
  Qed.

  Lemma repeat_step X (e : X -> NomG X ) b :
    repeat None e b ⩵ alt (let! v := e b in repeat None e v) (ret b).
  Proof.
    intros. rewrite -H0 -H. simpl.
    destruct fuel; simpl in *.
    - unfold_MonSem. subst. contradiction.
    - unfold_MonSem. repeat rewrite run_bind_monsem.
      unfold_MonSem. rewrite run_bind_monsem in H0.
      unfold_MonSem.
      destruct (run (S fuel) (e b) data s) as [[x v]| |].
      + simpl in *. unfold_MonSem.
        destruct ((fix sem_repeat_none (n : nat) (x : X) {struct n} : MonSem X :=
             match n with
             | 0%nat => λ _ : span, NoFuel
             | S n0 =>
                 λ s : span,
                   match
                     match run (S fuel) (e x) data s with
                     | Res (s0, x1) => sem_repeat_none n0 x1 s0
                     | NoRes => NoRes
                     | NoFuel => NoFuel
                     end
                   with
                   | Res (s0, v) => Res (s0, v)
                   | NoRes => Res (s, x)
                   | NoFuel => NoFuel
                   end
             end) fuel v x) as [[s0 v0] | | ] eqn:? ; simpl in *.
        * destruct (run (S fuel) (e v) data x) as [[s1 v1] | |] eqn:?; simpl in *.
          -- eapply (repeat_none_fuel_mono fuel (S fuel)) in Heqr.
             unfold_MonSem. erewrite Heqr0 in Heqr. rewrite Heqr. reflexivity.
             intros. eapply run_fuel_mono; eauto. lia. lia. auto.
          -- eapply (repeat_none_fuel_mono fuel (S fuel)) in Heqr.
             unfold_MonSem. erewrite Heqr0 in Heqr. rewrite Heqr. reflexivity.
             intros. eapply run_fuel_mono; eauto. lia. lia. auto.
          -- subst. contradiction.
        * eapply (repeat_none_fuel_mono fuel (S fuel)) in Heqr.
          unfold_MonSem. erewrite Heqr in H0. rewrite Heqr. reflexivity.
          intros. eapply run_fuel_mono; eauto. lia. lia. auto.
        * subst. contradiction.
      + reflexivity.
      + reflexivity.
  Qed.

End laws.
