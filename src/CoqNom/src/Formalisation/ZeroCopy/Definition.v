From stdpp Require Import numbers countable.
From Formalisation Require Import Span SizeNat Inject IsFresh.
From Classes Require Import Foldable.
Require Import Vector.
From Equations Require Import Equations.
Import disjoint.

(* =Bit= *)
Definition Bit := bool.
(* =end= *)

(* =ValuesFormat= *)
Class ValuesFormat (X : Type) :=
  mk_values {
      size : nat;
      encode : X -> Vector.t Bit size;
      decode : Vector.t Bit size -> option X;
      spec : forall (x : X), decode (encode x) = Some x; }.
(* =end= *)


Local Instance ValuesBool : ValuesFormat bool.
refine (mk_values bool 1
          (fun b => cons b nil)
          (fun v => match v with
                 | cons b _ => Some b
                 | _ => None
                 end) _).
intros. reflexivity.
Defined.

(* =Etiquette= *)
Class Etiquette `{Countable etiquette} :=
  mk_etiquette {
      set_etiquette : gset etiquette;
      set_etiquette_spec: forall (e : etiquette), e ∈ set_etiquette; }.
(* =end= *)

(* =Result= *)
Inductive Result :=
| Value : forall `{ValuesFormat X}, X -> Result
| Span : span -> Result
| Struct : forall `{Etiquette etiquette}, (etiquette -> Result) -> Result.
(* =end= *)

Arguments Value [X _].
Arguments Struct [etiquette _ _ _].

Definition list_etiquette {X} `{Etiquette X} := elements set_etiquette.

Fixpoint Result_to_list (t: Result) : list span :=
  match t with
  | Value _ => []
  | Span s => [s]
  | Struct st =>
      list.foldr (fun eti r => Result_to_list (st eti) ++ r) [] list_etiquette
  end.

(* =Decodeur= *)
Definition Decodeur := span -> option Result.
(* =end= *)

Open Scope N_scope.

(* =scope_in= *)
Definition scope_in (s t : span) := set_span s ⊆ set_span t.
(* =end= *)

(* =ResultWeakZC= *)
Fixpoint ResultWeakZC (s : span) (r : Result) : Prop :=
  match r with
  | Value _ => True
  | Span v => scope_in v s
  | Struct ft => forall e, ResultWeakZC s (ft e)
  end.
(* =end= *)

(* =DecodeurWeakZC= *)
Definition DecodeurWeakZC (d: Decodeur) := forall s ft,
    d s = Some ft -> ResultWeakZC s ft.
(* =end= *)

(* =ResultZC= *)
Fixpoint ResultZC (s : span) (r : Result) : Prop :=
  match r with
  | Value _ => False
  | Span v => scope_in v s
  | Struct ft => forall e, ResultZC s (ft e)
  end.
(* =end= *)

(* =DecodeurZC= *)
Definition DecodeurZC (d : Decodeur) := forall s ft,
    d s = Some ft -> ResultZC s ft.
(* =end= *)

(** Version tous les spans de la structures sont disjointes deux à deux **)

(* =Result_safe= *)
Definition Result_safe (r : Result) : Prop := forall s t,
    s <> t ->
    s ∈ Result_to_list r ->
    t ∈ Result_to_list r ->
    disjoint s t.
(* =end= *)

(** Version SL **)

(* =Result_safeSL= *)
Definition Result_safeSL (r : Result) : iProp :=
  [∗ list] v ∈ Result_to_list r, IsFresh v.
(* =end= *)

(* =safe_bridge= *)
Theorem safe_bridge : forall (r : Result), Result_safeSL r ⊢ ⌜ Result_safe r ⌝.
(* =end= *)
Proof.
  unfold Result_safe. induction r; simpl; intros.
  - iIntros "HA". iPureIntro. intros s t NEQ F. inversion F.
  - iIntros "HA". iPureIntro. intros t0 t1 NEQ INt0 INt1.
    eapply elem_of_list_singleton in INt0. eapply elem_of_list_singleton in INt1.
    subst. contradiction.
  - iIntros "HA" (s t NEQ INs INt).
    unfold Result_safeSL. simpl.
    eapply elem_of_list_lookup_1 in INs as [Is Ps].
    eapply elem_of_list_lookup_1 in INt as [It Pt].
    iDestruct (big_sepL_delete with "HA") as "[Hs HA]". eapply Ps.
    iDestruct (big_sepL_delete with "HA") as "[Ht HA]". eapply Pt.
    destruct (decide (It = Is)).
    + subst. rewrite Ps in Pt. injection Pt. intro. contradiction.
    + iClear "HA". iApply (IsFresh_spec with "Hs Ht").
Qed.

(* =DecodeurZC_safe= *)
Definition DecodeurZC_safe (d : Decodeur) :=
  forall s ft, d s = Some ft -> Result_safe ft.
