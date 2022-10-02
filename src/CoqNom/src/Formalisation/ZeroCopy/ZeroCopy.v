From stdpp Require Import numbers countable.
From Formalisation Require Import Span SizeNat Inject IsFresh.
From Classes Require Import Foldable.
Require Import Vector.
From Equations Require Import Equations.
Import disjoint.

Section ZeroCopy.

  Context {M : Type -> Type}.
  Context {foldable : Foldable M}.

  Open Scope N_scope.

  Definition set_span (s : span) := inject (pos s) (pos s + len s).

  Definition scope_in (s t : span) := set_span s ⊆ set_span t.

  Definition Result_in (r : M span) (s : span):=
    forall v, v ∈ M_to_list r -> scope_in v s.

  Definition WeakZC (decode : span -> option (M span)) :=
    forall s (res : M span),
      decode s = Some res ->
      Result_in res s.

  Close Scope N_scope.

End ZeroCopy.
