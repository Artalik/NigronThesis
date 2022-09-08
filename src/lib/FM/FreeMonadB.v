Inductive Free {SIG : Type -> Type}: Type -> Type :=
| ret {X}: X -> Free X
| gen {X}: SIG X -> Free X
| bind {X Y}: Free X -> (X -> Free Y) -> Free Y.

Arguments Free: clear implicits.

Definition bind2 {SIG} {A B C: Type} (x: Free SIG (A * B)) (f: A -> B -> Free SIG C) : Free SIG C :=
  bind x (fun p => f (fst p) (snd p)).

Declare Scope free_monad_scope.

Notation "'ret!' v" := (ret v) (at level 50) : free_monad_scope.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X name, A at level 100, B at level 200) : free_monad_scope.

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X name, Y name, A at level 100, B at level 200) : free_monad_scope.

Notation "'let!' x ':=' e1 'in' e2" :=
  (bind e1 (fun x => e2)) (x name, at level 50) : free_monad_scope.

Notation "'let!' ( X , Y ) ':=' A 'in' B" := (bind2 A (fun X Y => B))
     (at level 50, X name, Y name): free_monad_scope.
