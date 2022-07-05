From stdpp Require Import numbers countable.
From FreeMonad Require Import Span SizeNat Inject IsFresh.
From Classes Require Import Foldable.
Require Import Vector.
From Equations Require Import Equations.

Definition Bit := bool.

Class ValuesFormat (X : Type) := mk_values
  {
    size : nat;
    encode : X -> Vector.t Bit size;
    decode : Vector.t Bit size -> option X;
    spec : forall (x : X), decode (encode x) = Some x;
  }.

Local Instance ValuesBool : ValuesFormat bool.
refine (mk_values bool 1
          (fun b => cons b nil)
          (fun v => match v with
                 | cons b _ => Some b
                 | _ => None
                 end) _).
intros. reflexivity.
Defined.

Class etiquetteOK (etiquette : Type) :=
  mk_etiquette
    {
      eq_dec_etiquette : EqDecision etiquette;
      count_etiquette : @Countable etiquette eq_dec_etiquette;
      list_etiquette : list etiquette;
      list_etiquette_spec: forall (e : etiquette), e ∈ list_etiquette;
    }.

(* Parameter etiquette : Type. *)
(* Parameter eq_dec_etiquette : EqDecision etiquette. *)
(* Parameter count_etiquette : @Countable etiquette eq_dec_etiquette. *)
(* Parameter list_etiquette : list etiquette. *)
(* Parameter list_etiquette_spec: forall (e : etiquette), List.In e list_etiquette. *)

Inductive Result :=
| Value : forall X, ValuesFormat X -> X -> Result
| Span : span -> Result
| Struct : forall X, etiquetteOK X -> (X -> Result) -> Result.

Arguments Value [X _].
Arguments Struct [X _].

Definition ResTree `{etiquetteOK X} := X -> Result.

Fixpoint Tree_to_list_aux (t: Result) : list span :=
  match t with
  | Value _ => []
  | Span s => [s]
  | Struct st =>
      (fix foldr l := match l with
                     | [] => []
                     | h :: t => Tree_to_list_aux (st h) ++ foldr t
                      end) list_etiquette
        end.

Definition Tree_to_list `{etiquetteOK X} (st: ResTree) : list span :=
  (fix foldr l := match l with
                  | [] => []
                  | h :: t => Tree_to_list_aux (st h) ++ foldr t
                  end) list_etiquette.

Definition Decodeur `{etiquetteOK X} := span -> option ResTree.

Open Scope N_scope.

Definition set_span (s : span) := inject (pos s) (pos s + len s).

Definition scope_in (s t : span) := set_span s ⊂ set_span t.

Fixpoint WZCChamp (s : span) (f : Result) : Prop :=
  match f with
  | Value _ => True
  | Span v => scope_in v s
  | Struct ft => forall e, WZCChamp s (ft e)
  end.

Definition WZCStruc `{etiquetteOK X} (ft : ResTree) (s : span) : Prop :=
  WZCChamp s (Struct ft). (* forall e, WZCChamp s (ft e). *)

Definition DecodeurWZC `{etiquetteOK X} :=
  forall (d : Decodeur) s ft,
    d s = Some ft ->
    WZCStruc ft s.

Fixpoint ZCChamp (s : span) (f : Result) : Prop :=
  match f with
  | Value _ => False
  | Span v => scope_in v s
  | Struct ft => forall e, ZCChamp s (ft e)
  end.

Definition ZCStruc `{etiquetteOK X} (ft : ResTree) (s : span) : Prop :=
  ZCChamp s (Struct ft). (* forall e, ZCChamp s (ft e). *)

Definition DecodeurZC `{etiquetteOK X} :=
  forall (d : Decodeur) s ft,
    d s = Some ft ->
    ZCStruc ft s.

(* Definition disjoint (s t : span) := set_span s ## set_span t. *)

(** Version tous les champs sont disjoints **)

Fixpoint disjoint_champ (s : span) (f : Result) :=
  match f with
  | Value _ => True%type
  | Span t => disjoint.disjoint s t
  | Struct ft => forall e, disjoint_champ s (ft e)
  end.

Fixpoint disjoint_champs (f0 f1 : Result) : Prop :=
  match f0, f1 with
  | Value _, _ | _, Value _ => True
  | Span s, f | f, Span s => disjoint_champ s f
  | Struct f0, Struct f1 => forall e e', disjoint_champs (f0 e) (f1 e')
  end.

Definition Struct_disjoint `{etiquetteOK X} (ft : ResTree) : Prop :=
  forall e e', e <> e' -> disjoint_champs (ft e) (ft e').

(** Version tous les spans de la structures sont disjointes deux à deux **)

Definition Tree_safe `{etiquetteOK X} (f : ResTree) : Prop :=
  forall s t, s <> t -> s ∈ Tree_to_list f -> t ∈ Tree_to_list f -> disjoint.disjoint s t.


(** Version SL **)

Fixpoint champ_safe (f : Result) : iProp :=
  match f with
  | Value _ => emp
  | Span t => IsFresh t
  | Struct ft => [∗ list] e ∈ list_etiquette, champ_safe (ft e)
  end.

Definition Struct_safe `{etiquetteOK X} (ft : ResTree) : iProp :=
  champ_safe (Struct ft). (* [∗ list] e ∈ list_etiquette, champ_safe (ft e). *)

(** SL -> disjonction de structures  **)

Lemma champSL_disjoint : forall s c,
    champ_safe c ∗ IsFresh s ⊢ ⌜disjoint_champ s c⌝.
Proof.
  induction c; simpl; auto.
  - iIntros "[HA HB]". iApply (IsFresh_spec with "HB HA").
  - iIntros "[HA HB]" (x).
    pose (IN := list_etiquette_spec x).
    eapply elem_of_list_lookup_1 in IN as [i P0].
    iDestruct (big_sepL_delete with "HA") as "[HA _]"; eauto.
    iApply H. iFrame.
Qed.

Lemma champsSL_disjoint : forall c0 c1,
    champ_safe c0 ∗ champ_safe c1 ⊢ ⌜disjoint_champs c0 c1⌝.
Proof.
  induction c0; simpl; auto.
  - induction c1; simpl; auto.
    + iIntros "[HA HB]". iApply (IsFresh_spec with "HA HB").
    + iIntros "[HA HB]" (x).
      pose (IN := list_etiquette_spec x).
      eapply elem_of_list_lookup_1 in IN as [i P0].
      iDestruct (big_sepL_delete with "HB") as "[HB _]"; eauto.
      iApply champSL_disjoint. iFrame.
  - induction c1; simpl; auto.
    + iIntros "[HB HA]" (x).
      pose (IN := list_etiquette_spec x).
      eapply elem_of_list_lookup_1 in IN as [i P0].
      iDestruct (big_sepL_delete with "HB") as "[HB _]"; eauto.
      iApply champSL_disjoint. iFrame.
    + iIntros "[HA HB]" (x0 x1).
      pose (IN := list_etiquette_spec x1).
      eapply elem_of_list_lookup_1 in IN as [i P0].
      iDestruct (big_sepL_delete with "HB") as "[HB _]"; eauto.
      iDestruct (H0 with "[HA HB]") as "%P". iFrame.
      pose (IN := list_etiquette_spec x0).
      eapply elem_of_list_lookup_1 in IN as [i0 P1].
      iDestruct (big_sepL_delete with "HA") as "[HA _]"; eauto.
      iDestruct (H with "[HA HB]") as "%P2". iFrame.
      auto.
Qed.


Theorem disjoint_to_Prop `{etiquetteOK X}: forall (ft : ResTree),
    Struct_safe ft ⊢ ⌜ Struct_disjoint ft ⌝.
Proof.
  iIntros (ft) "HA".
  unfold Struct_safe. unfold Struct_disjoint. iIntros (e e' NEQ).
  pose (IN := list_etiquette_spec e).
  eapply elem_of_list_lookup_1 in IN as [i P0].
  iDestruct (big_sepL_delete with "HA") as "[HA HB]"; eauto.
  pose (IN := list_etiquette_spec e').
  eapply elem_of_list_lookup_1 in IN as [i0 P1].
  iDestruct (big_sepL_delete with "HB") as "[HB _]"; eauto.
  destruct (decide (i0 = i)). subst. rewrite P0 in P1. inversion P1. subst. contradiction.
  iApply champsSL_disjoint. iFrame.
Qed.


(** SL -> In  **)

Lemma tree_to_list_aux_in :
  forall X (l : list X) s ft,
    s ∈ (fix foldr (l : list X) : list span :=
           match l with
           | [] => []
           | h :: t => Tree_to_list_aux (ft h) ++ foldr t
           end) l -> exists e, e ∈ l /\ s ∈ Tree_to_list_aux (ft e).
Proof.
 induction l; simpl; intros.
 - inversion H.
 - eapply elem_of_app in H as [P0 | P0].
   + exists a. split; auto. constructor.
   + eapply IHl in P0 as [v [P0 P1]].
     exists v. split; auto. constructor. auto.
Qed.

Lemma IsFresh_champSL : forall c s, s ∈ Tree_to_list_aux c -> champ_safe c ⊢ <absorb> IsFresh s.
Proof.
  induction c; simpl; intros.
  - inversion H.
  - eapply elem_of_list_singleton in H. subst. auto.
  - destruct e. simpl in *. clear list_etiquette_spec0. induction list_etiquette0.
    + inversion H0.
    + iIntros "[HA HB]". eapply elem_of_app in H0 as [P0 | P0].
      * iClear "HB". iApply H; eauto.
      * iClear "HA". iApply IHlist_etiquette0; eauto.
Qed.



Lemma test `{etiquetteOK X}: forall ft,
    (∀ (x : X) (s t : span),
        s ≠ t
         → s ∈ Tree_to_list_aux (ft x)
         → t ∈ Tree_to_list_aux (ft x) → (champ_safe (ft x) -∗ ⌜disjoint.disjoint s t⌝)%stdpp) ->
    ∀ s t : span,
      s ≠ t
      → s ∈ Tree_to_list_aux (Struct ft)
      → t ∈ Tree_to_list_aux (Struct ft)
      → (champ_safe (Struct ft) -∗ ⌜disjoint.disjoint s t⌝)%stdpp.
Proof.
  simpl. destruct H. intros ft IH s t NEQ INs INt. iIntros "HA".
  eapply tree_to_list_aux_in in INs as [es [_ INs]].
  eapply tree_to_list_aux_in in INt as [et [_ INt]].
  pose (IN := list_etiquette_spec0 es).
  eapply elem_of_list_lookup_1 in IN as [i P0].
  iDestruct (big_sepL_delete with "HA") as "[HA HB]"; eauto.
  pose (IN := list_etiquette_spec0 et).
  eapply elem_of_list_lookup_1 in IN as [i0 P1].
  iDestruct (big_sepL_delete with "HB") as "[HB _]"; eauto.
  destruct (decide (i0 = i)).
  - subst. rewrite P0 in P1. inversion P1. subst. iApply IH; eauto.
  - iDestruct (IsFresh_champSL with "HA") as ">HA"; eauto.
    iDestruct (IsFresh_champSL with "HB") as ">HB"; eauto.
    iApply (IsFresh_spec with "HA HB").
Qed.

Lemma test0 : forall X (l : list X) r s es,
    es ∈ l ->
    s ∈ Tree_to_list_aux (r es) ->
    s ∈ (fix foldr (l : list X) : list span :=
           match l with
           | [] => []
           | h :: t => Tree_to_list_aux (r h) ++ foldr t
           end) l.
Proof.
  induction l; simpl; intros.
  - inversion H.
  - inversion H.
    + subst. eapply elem_of_app. left. auto.
    + subst. eapply elem_of_app. right. eapply IHl; eauto.
Qed.

Theorem disjoint_In_Prop `{etiquetteOK X}: forall (ft : ResTree),
    Struct_safe ft ⊢ ⌜ Tree_safe ft ⌝.
Proof.
  iIntros (ft) "HA".
  unfold Struct_safe. unfold Tree_safe.
  iIntros (s t NEQ INs INt).
  eapply tree_to_list_aux_in in INs as [es [_ INs]].
  eapply tree_to_list_aux_in in INt as [et [_ INt]].
  pose (IN := list_etiquette_spec es).
  eapply elem_of_list_lookup_1 in IN as [i P0].
  iDestruct (big_sepL_delete with "HA") as "[HA HB]"; eauto.
  pose (IN := list_etiquette_spec et).
  eapply elem_of_list_lookup_1 in IN as [i0 P1].
  iDestruct (big_sepL_delete with "HB") as "[HB _]"; eauto.
  - destruct (decide (i0 = i)).
    + iClear "HB". iStopProof. subst. rewrite P0 in P1. inversion P1. subst.
      clear P0 P1 i. revert s t NEQ INs INt.
      induction (ft et); simpl; intros.
      * inversion INs.
      * eapply elem_of_list_singleton in INs. eapply elem_of_list_singleton in INt.
        subst. contradiction.
      * iIntros "HA".
        eapply tree_to_list_aux_in in INs as [es [_ IHs]]. clear X H ft et.
        eapply tree_to_list_aux_in in INt as [et [_ IHt]].
        iApply test; eauto; eapply test0; eauto; eapply e.
    + iDestruct (IsFresh_champSL with "HA") as ">HA"; eauto.
      iDestruct (IsFresh_champSL with "HB") as ">HB"; eauto.
      iApply (IsFresh_spec with "HA HB").
Qed.

Definition DecodeurZC_safe `{etiquetteOK X} := forall (d : Decodeur) s ft,
    d s = Some ft -> Tree_safe ft.
