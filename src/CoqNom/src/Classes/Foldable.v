Class Foldable (t : Type -> Type) :=
  { foldr : forall A B, (A -> B -> B) -> B -> t A -> B; }.
