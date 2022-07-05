From Formalisation Require Import Inject Span.

Definition disjoint (s0 s1 : span) :=
  inject (pos s0) (pos s0 + len s0) ## inject (pos s1) (pos s1 + len s1).


Lemma disjoint_sym : forall s0 s1, disjoint s0 s1 -> disjoint s1 s0.
Proof. unfold disjoint. intros. apply disjoint_sym. auto. Qed.

Definition all_disjoint (l : list span) := forall s0 s1,
    s0 <> s1 ->
    s0 ∈ l ->
    s1 ∈ l ->
    disjoint s0 s1.
