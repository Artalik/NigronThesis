Class Semigroup X :=
  {
  f : X -> X -> X;
  assoc : forall x y z,  f x (f y z) = f (f x y) z;
  }.

Class Monoid (X : Type) {sg : Semigroup X} :=
  {
  mempty : X;
  right_id : forall x, f x mempty = x;
  left_id : forall x, f mempty x = x;
  }.

Require Import List.

Global Instance List_Semigroup {X : Type} : Semigroup (list X) :=
  Monoid.Build_Semigroup _ (@app X) (@app_assoc X).

Global Instance List_Monoid {X} : Monoid.Monoid (@list X).
esplit. instantiate (1 := nil).
all : intros; simpl; simpl_list; eauto.
Defined.
