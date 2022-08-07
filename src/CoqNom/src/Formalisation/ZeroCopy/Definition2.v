From stdpp Require Import numbers countable.
From Formalisation Require Import Span SizeNat Inject IsFresh.
From Classes Require Import Foldable.
Require Import Vector.
From Equations Require Import Equations.

Definition Bit := bool.

Class ValuesFormat (X : Type) :=
  mk_values {
      size : nat;
      encode : X -> Vector.t Bit size;
      decode : Vector.t Bit size -> option X;
      spec : forall (x : X), decode (encode x) = Some x; }.

Local Instance ValuesBool : ValuesFormat bool.
refine (mk_values bool 1
          (fun b => cons b nil)
          (fun v => match v with
                 | cons b _ => Some b
                 | _ => None
                 end) _).
intros. reflexivity.
Defined.

Class Etiquette (etiquette : Type) `{Countable etiquette} :=
  mk_etiquette {
      set_etiquette : gset etiquette;
      set_etiquette_spec: forall (e : etiquette), e ∈ set_etiquette; }.


Inductive Result :=
| Value : forall `{ValuesFormat X}, X -> Result
| Span : span -> Result
| Struct : forall `{Etiquette etiquette}, (etiquette -> Result) -> Result.

Arguments Value [X _].
Arguments Struct [etiquette _ _ _].

Definition list_etiquette {X} `{Etiquette X} := elements set_etiquette.

Fixpoint Result_to_list (t: Result) : list span :=
  match t with
  | Value _ => []
  | Span s => [s]
  | Struct st =>
      (fix foldr l :=
         match l with
         | [] => []
         | h :: t => Result_to_list (st h) ++ foldr t
         end) list_etiquette
  end.

Definition Decodeur := span -> option Result.

Open Scope N_scope.

Definition set_span (s : span) := inject (pos s) (pos s + len s).

Definition scope_in (s t : span) := set_span s ⊆ set_span t.

Fixpoint ResultWeakZC (s : span) (r : Result) : Prop :=
  match r with
  | Value _ => True
  | Span v => scope_in v s
  | Struct ft => forall e, ResultWeakZC s (ft e)
  end.

Definition DecodeurWeakZC (d: Decodeur) :=
  forall s ft,
    d s = Some ft ->
    ResultWeakZC s ft.

Fixpoint ResultZC (s : span) (f : Result) : Prop :=
  match f with
  | Value _ => False
  | Span v => scope_in v s
  | Struct ft => forall e, ResultZC s (ft e)
  end.

Definition DecodeurZC (d : Decodeur) :=
  forall s ft,
    d s = Some ft ->
    ResultZC s ft.

(** Version tous les champs sont disjoints **)

(** Version tous les spans de la structures sont disjointes deux à deux **)

Definition Result_safe (f : Result) : Prop :=
  forall s t, s <> t -> s ∈ Result_to_list f -> t ∈ Result_to_list f -> disjoint.disjoint s t.


(** Version SL **)

Fixpoint Result_safeSL (f : Result) : iProp :=
  match f with
  | Value _ => emp
  | Span t => IsFresh t
  | Struct ft => [∗ list] e ∈ list_etiquette, Result_safeSL (ft e)
  end.

(** SL -> disjonction de structures  **)
(** SL -> In  **)

Lemma tree_to_list_aux_in :
  forall X (l : list X) s ft,
    s ∈ (fix foldr (l : list X) : list span :=
           match l with
           | [] => []
           | h :: t => Result_to_list (ft h) ++ foldr t
           end) l -> exists e, e ∈ l /\ s ∈ Result_to_list (ft e).
Proof.
 induction l; simpl; intros.
 - inversion H.
 - eapply elem_of_app in H as [P0 | P0].
   + exists a. split; auto. constructor.
   + eapply IHl in P0 as [v [P0 P1]].
     exists v. split; auto. constructor. auto.
Qed.

Lemma IsFresh_champSL : forall c s, s ∈ Result_to_list c -> Result_safeSL c ⊢ <absorb> IsFresh s.
Proof.
  induction c; simpl; intros.
  - inversion H0.
  - eapply elem_of_list_singleton in H. subst. auto.
  - destruct H0. unfold list_etiquette in *. simpl in *. clear set_etiquette_spec0.
    induction set_etiquette0 as [| y Y not_in IH] using set_ind_L.
    + inversion H2.
    + assert ({[y]} ## Y) by (eapply disjoint_singleton_l; auto).
      rewrite elements_disj_union; auto.
      rewrite elements_disj_union in H2; auto. iIntros "[HA HB]".
      rewrite elements_singleton. rewrite elements_singleton in H2.
      eapply elem_of_app in H2 as [P0 | P0].
      * iClear "HB". simpl. iApply H1; eauto. iDestruct "HA" as "[$ _]".
      * iClear "HA". iApply IH; eauto.
Qed.

Lemma all_champ_safe `{Etiquette etiquette}: forall ft,
    (∀ (x : etiquette) (s t : span),
        s ≠ t →
        s ∈ Result_to_list (ft x) →
        t ∈ Result_to_list (ft x) →
        (Result_safeSL (ft x) -∗ ⌜disjoint.disjoint s t⌝)%stdpp) ->
    ∀ s t : span,
      s ≠ t →
      s ∈ Result_to_list (Struct ft) →
      t ∈ Result_to_list (Struct ft) →
      (Result_safeSL (Struct ft) -∗ ⌜disjoint.disjoint s t⌝)%stdpp.
Proof.
  simpl. destruct H0. intros ft IH s t NEQ INs INt. iIntros "HA".
  eapply tree_to_list_aux_in in INs as [es [_ INs]].
  eapply tree_to_list_aux_in in INt as [et [_ INt]].
  pose (IN := set_etiquette_spec0 es).
  eapply elem_of_elements in IN.
  eapply elem_of_list_lookup_1 in IN as [i0 P0].
  iDestruct (big_sepL_delete with "HA") as "[HA HB]"; eauto.
  pose (IN := set_etiquette_spec0 et).
  eapply elem_of_elements in IN.
  eapply elem_of_list_lookup_1 in IN as [i1 P1].
  iDestruct (big_sepL_delete with "HB") as "[HB _]"; eauto.
  destruct (decide (i1 = i0)).
  - subst. rewrite P0 in P1. inversion P1. subst. iApply IH; eauto.
  - iDestruct (IsFresh_champSL with "HA") as ">HA"; eauto.
    iDestruct (IsFresh_champSL with "HB") as ">HB"; eauto.
    iApply (IsFresh_spec with "HA HB").
Qed.

Lemma in_champ : forall X (l : list X) r s es,
    es ∈ l ->
    s ∈ Result_to_list (r es) ->
    s ∈ (fix foldr (l : list X) : list span :=
           match l with
           | [] => []
           | h :: t => Result_to_list (r h) ++ foldr t
           end) l.
Proof.
  induction l; simpl; intros.
  - inversion H.
  - inversion H.
    + subst. eapply elem_of_app. left. auto.
    + subst. eapply elem_of_app. right. eapply IHl; eauto.
Qed.

Theorem disjoint_In_Prop : forall (ft : Result),
    Result_safeSL ft ⊢ ⌜ Result_safe ft ⌝.
Proof.
  unfold Result_safe. induction ft; simpl; intros.
  - iIntros "HA". iPureIntro. intros s t NEQ F. inversion F.
  - iIntros "HA". iPureIntro. intros t0 t1 NEQ INt0 INt1.
    eapply elem_of_list_singleton in INt0. eapply elem_of_list_singleton in INt1.
    subst. contradiction.
  - iIntros "HA" (s t NEQ INs INt).
    eapply tree_to_list_aux_in in INs as [es [_ INs]].
    eapply tree_to_list_aux_in in INt as [et [_ INt]].
    iApply all_champ_safe; eauto.
    intros. iIntros "HA".
    iDestruct (H1 with "HA") as "%".
    iPureIntro. eapply H5; eauto.
    simpl. eapply in_champ; eauto. unfold list_etiquette.
    destruct H0. simpl. eapply elem_of_elements. eauto.
    simpl. eapply in_champ; eauto. unfold list_etiquette.
    destruct H0. simpl. eapply elem_of_elements. eauto.
Qed.

Definition DecodeurZC_safe (d : Decodeur) :=
  forall s ft, d s = Some ft -> Result_safe ft.
