From Formalisation Require Import Inject Span.


(* =set_span= *)
Definition set_span (s : span) := inject (pos s) (pos s + len s).
(* =end= *)

(* =disjoint= *)
Definition disjoint (s t : span) : Prop := set_span s ## set_span t.
(* =end= *)

Lemma disjoint_sym : forall s t, disjoint s t -> disjoint t s.
Proof. unfold disjoint. intros. apply disjoint_sym. auto. Qed.

(* =all_disjoint= *)
Definition all_disjoint (l : list span) := forall s t,
    s <> t ->
    s ∈ l ->
    t ∈ l ->
    disjoint s t.
(* =end= *)
