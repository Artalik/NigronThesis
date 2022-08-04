From FreeMonad Require Export FreeMonad.

Inductive Fresh : Type -> Type :=
| gensymOp : unit -> Fresh nat.

Definition gensym (tt: unit): Free Fresh nat := syntax_effect (gensymOp tt).

Require Import tree.

Fixpoint label {X} (t : Tree X) : Free Fresh (Tree nat):=
  match t with
  | Leaf _ =>
    do n <- gensym tt;
    ret (Leaf n)
  | Node l r =>
    do l <- label l;
    do r <- label r;
    ret (Node l r)
  end.
