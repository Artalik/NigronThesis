Require Import FunctionalExtensionality.

(* =Free= *)
Inductive Free (SIG : Type -> Type) (X : Type) : Type :=
| ret : X -> Free SIG X
| op : forall Y, SIG Y -> (Y -> Free SIG X) -> Free SIG X.
(* =end= *)

Arguments ret [SIG X] _.
Arguments op [SIG X Y].

Section bind.

  Context {SIG : Type -> Type}.
  Context {X Y : Type}.

(* =bind= *)
Fixpoint bind (m : Free SIG X) (f : X -> Free SIG Y) : Free SIG Y :=
  match m with
  | ret v => f v
  | op e k => op e (fun v => bind (k v) f)
  end.
(* =end= *)
End bind.

Arguments bind [_][_] [_] m f.

Section syntax_effect.

  Context {SIG : Type -> Type}.
  Context {X : Type}.

(* =syntax_effect= *)
Definition gen (m : SIG X) : Free SIG X := op m (@ret SIG X).
(* =end= *)

End syntax_effect.

Definition bind2 {SIG} {A B C: Type} (x: Free SIG (A * B)) (f: A -> B -> Free SIG C) : Free SIG C :=
  bind x (fun p => f (fst p) (snd p)).

Declare Scope free_monad_scope.

Notation "'ret!' v" := (ret v) (at level 50) : free_monad_scope.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X name, A at level 100, B at level 200) : free_monad_scope.

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X name, Y name, A at level 100, B at level 200) : free_monad_scope.

(* =notation_bind= *)
Notation "'let!' x ':=' m 'in' k" := (bind m (fun x => k))
(* =end= *)
                                         (x name, at level 50) : free_monad_scope.

Notation "'let!' ( X , Y ) ':=' A 'in' B" := (bind2 A (fun X Y => B))
     (at level 50, X name, Y name): free_monad_scope.

Lemma lid : forall SIG X Y (a : X) (f : X -> Free SIG Y), bind (ret a) f = f a.
Proof. auto. Qed.

Lemma rid : forall SIG X (m : Free SIG X), bind m (@ret SIG X) = m.
Proof.
  fix IH 3.
  destruct m.
  reflexivity.
  simpl. do 2 f_equal.
  apply functional_extensionality. intro. apply IH.
Qed.

Lemma assoc_bind : forall SIG X Y Z (m : Free SIG X) f (g : Y -> Free SIG Z),
    bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
  fix IH 5.
  destruct m; intros.
  reflexivity.
  simpl. do 2 f_equal. apply functional_extensionality. intro. apply IH.
Qed.
