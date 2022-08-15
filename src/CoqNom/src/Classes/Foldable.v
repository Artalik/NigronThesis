From Classes Require Import Monoid.

Class Foldable (t : Type -> Type) :=
  { foldMap : forall M `{_ : Monoid M} A, (A -> M) -> t A -> M; }.
