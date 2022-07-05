From Classes Require Import Monoid.

Class Foldable (t : Type -> Type) :=
  {
  foldr : forall A B, (A -> B -> B) -> B -> t A -> B;
  foldMap: forall M `{_ : Monoid M} A, (A -> M) -> t A -> M
  }.
