Implicit Type X: Type.

Inductive Free (SIG : Type -> Type) X :=
| ret : X -> Free SIG X
| op : forall Y, SIG Y -> (Y -> Free SIG X) -> Free SIG X.

Arguments ret [SIG X] _.
Arguments op [SIG X Y].

Section Bind.
  Variable X Y : Type.
  Variable SIG : Type -> Type.
  (* =bind= *)
  Fixpoint bind (m: Free SIG X)(f: X -> Free SIG Y): Free SIG Y :=
  match m with
  | ret v => f v
  | op e k => op e (fun n => bind (k n) f)
  end.
(* =end= *)
End Bind.

Arguments bind [_][_] [_] m f.

(* =FreeFresh= *)
Inductive Fresh : Type -> Type :=
| gensymOp : unit -> Fresh nat.
(* =end= *)

(* =fresh= *)
Definition gensym (tt: unit): Free Fresh nat := op (gensymOp tt) (@ret Fresh nat).
(* =end= *)

Notation "'do' x '<-' e1 ';' e2" :=
  (bind e1 (fun x => e2)) (x name, at level 50).

Require Import tree.

(* =label= *)
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
(* =end= *)
