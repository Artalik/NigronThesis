From Classes Require Import Monoid.
(* =Foldable= *)
Class Foldable (t : Type -> Type) :=
  { foldMap : forall M `{_ : Monoid M} A, (A -> M) -> t A -> M; }.
(* =end= *)
Global Instance Id_Foldable : Foldable (fun S => S)%type.
econstructor.
intros M sg m A f v. eapply (f v).
Defined.

Global Instance Pair_Foldable X (fx : Foldable X) Y (fy : Foldable Y) : Foldable (fun S => X S * Y S)%type.
econstructor.
intros M sg m A f [vx vy].
eapply Monoid.f. eapply (@foldMap). eapply fx. eapply m. eapply f. eapply vx.
eapply (@foldMap). eapply fy. eapply m. eapply f. eapply vy.
Defined.
