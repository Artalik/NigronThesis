From stdpp Require Import numbers.
From Formalisation Require Import Axioms.
Open Scope N_scope.

Record natN (len : N) : Set := mk_natN { val : N ; len_correct : val < 2 ^ len}.

Arguments val [len].

Definition nat8 : Set := natN 8.
Definition nat16 : Set := natN 16.
Definition nat32 : Set := natN 32.
Definition nat64 : Set := natN 64.
Definition nat128 : Set := natN 128.

Definition eq_dec {p : N} (x y : natN p) : {x = y} + {x <> y}.
Proof.
  destruct x, y. destruct (N.eq_dec val0 val1) as [eq|neq].
  - left. subst. f_equal. eapply proof_irr.
  - right. intro eq. inversion eq. eapply neq. auto.
Defined.

Definition eqb {p1 p2 : N} (x : natN p1) (y : natN p2) : bool :=
  N.eqb (val x) (val y).

Notation "'_8' n" := (mk_natN 8 n _) (at level 30).
Notation "'_16' n" := (mk_natN 16 n _) (at level 30).
Notation "'_32' n" := (mk_natN 32 n _) (at level 30).
Notation "'_64' n" := (mk_natN 64 n _) (at level 30).
Notation "'_128' n" := (mk_natN 128 n _) (at level 30).

Lemma mult_pow : forall p (n m : natN p), val n * 2 ^ p + val m < 2 ^ (2 * p).
Proof.
  intros. destruct n as [n Pn], m as [m Pm]. simpl. eapply N.le_lt_trans.
  - instantiate (1 := ((2 ^ (2 * p)) - 1)). simpl.
    destruct p.
    + rewrite N.lt_1_r in Pn. rewrite N.lt_1_r in Pm. subst. lia.
    + transitivity (n * 2 ^ (N.pos p) + (2 ^ (N.pos p) - 1)).
      * apply N.add_le_mono_l. lia.
      * rewrite N.add_sub_assoc. 2 : lia.
        eapply N.sub_le_mono_r.
        assert (N.pos (2 * p) = N.pos p + N.pos p) by lia.
        rewrite H. rewrite N.pow_add_r. rewrite <- N.mul_succ_l.
        eapply N.mul_le_mono; auto. lia.
  - destruct p.
    + rewrite N.lt_1_r in Pn. rewrite N.lt_1_r in Pm. subst. simpl. lia.
    + apply N.sub_lt. 2 : lia. assert (1 = 2 ^ 0). constructor.
      rewrite H. apply N.pow_le_mono_r; lia.
Qed.


Program Definition natp_to_nat2p {p} (n : natN p) (m : natN p) : natN (2 * p) :=
  mk_natN (2 * p) ((val n) * (2 ^ p) + val m) _.
Next Obligation. intros. apply mult_pow. Qed.

Notation "n ↑ m" := (natp_to_nat2p n m)(at level 50).

Ltac NSize := try constructor; try (simpl; lia); auto.

Close Scope N_scope.
