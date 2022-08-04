Require Import freefresh.

Section Eval.
Variable X: Type.

Fixpoint eval (m: Free Fresh X): nat -> X * nat :=
  match m with
  | ret v => fun n => (v, n)
  | op (gensymOp _) k => fun n => eval (k n) (1 + n)
  end.

Definition run (m: Free Fresh X): X := fst (eval m 0).

End Eval.

Arguments eval [_] m.
Arguments run [_] m.

Require Import tree.

Section Relabel.

Variable X: Type.

Definition relabel (t: Tree X): Tree nat := run (label t).

End Relabel.

Arguments relabel [_] t.
