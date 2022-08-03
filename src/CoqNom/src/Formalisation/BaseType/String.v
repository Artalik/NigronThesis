Require Export String.
From stdpp Require Import numbers.
From Equations Require Import Equations.
From Formalisation Require Import SizeNat.

Definition ascii_to_nat8 (a : Ascii.ascii) : nat8 :=
  mk_natN 8 (Ascii.N_of_ascii a) (Ascii.N_ascii_bounded a).

Equations string_get (n : N) (s : string) : option nat8 by wf (N.to_nat n) lt :=
  string_get n EmptyString := None;
  string_get 0 (String a _) := Some (ascii_to_nat8 a);
  string_get pos (String _ s) := string_get (N.pred pos) s.
Next Obligation.
  intros. lia.
Defined.

Fixpoint string_length (s : string) : N :=
  match s with
  | EmptyString => 0
  | String _ s => N.succ (string_length s)
  end.
