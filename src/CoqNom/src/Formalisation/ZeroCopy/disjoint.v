From Formalisation Require Import Inject Span.

Definition disjoint (s t : span) :=
  inject (pos s) (pos s + len s) ## inject (pos t) (pos t + len t).


Lemma disjoint_sym : forall s t, disjoint s t -> disjoint t s.
Proof. unfold disjoint. intros. apply disjoint_sym. auto. Qed.

Definition all_disjoint (l : list span) := forall s t,
    s <> t ->
    s ∈ l ->
    t ∈ l ->
    disjoint s t.
