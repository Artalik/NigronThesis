From stdpp Require Import numbers.

Open Scope N_scope.

(* =span= *)
Record span := mk_span {pos : N; len : N}.
(* =end= *)

Definition eq_dec (s0 s1 : span) : {s0 = s1} + {s0 <> s1}.
  destruct s0 as [pos0 len0]. destruct s1 as [pos1 len1].
  destruct (N.eq_dec pos0 pos1).
  destruct (N.eq_dec len0 len1).
  subst. left. f_equal.
  right. intro.  eapply n. inversion H. auto.
  right. intro.  eapply n. inversion H. auto.
Defined.
