From SepLogic Require Import SepSet.

(****************************************************************)

Require Import tree.

(****************************************************************)

Require Import freefresh.

(****************************************************************)

Require Import fresh.

(****************************************************************)

Definition ident := nat.

(****************************************************************)
(* Raisonnement pour gensym avec la SL sur liste minimaliste *)

Section WP.

Variable (X: Type).

(* =wp= *)
Fixpoint wp (m: Free Fresh X)(Q: X -> iProp): iProp :=
  match m with
  | ret v => Q v
  | op (gensymOp _) k => ∀ (v: nat), & v -∗ wp (k v) Q
  end.
(* =end= *)

End WP.

Arguments wp [_] m Q.

Local Open Scope free_monad_scope.

Lemma wp_bind {X Y} (e : Free Fresh X) (f :  X → Free Fresh Y) (Q : Y -> iProp) (Q' : X -> iProp) :
  wp e Q' ⊢
  (∀ v,  Q' v -∗ wp (f v) Q ) -∗
  wp (do v <- e; f v) Q %I.
Proof.
iIntros "HA HB". revert e. fix e 1.
destruct e0.
- iApply "HB". iApply "HA".
- destruct f0; simpl.
  iIntros (l) "HC".
  iDestruct ("HA" with "HC") as "HA".
  iPoseProof "HB" as "HB".
  apply e.
Qed.

Lemma wp_consequence {X} (P Q : X -> iProp) (f : Free Fresh X) :
  ⊢ wp f P -∗
    (∀ x, P x -∗ Q x) -∗
    wp f Q.
Proof.
induction f as [v | Y [] k]; simpl; intros; auto.
- iIntros "HA HB". iApply ("HB" with "HA").
- iIntros "HA HB * HC". iDestruct ("HA" with "HC") as "HA".
  iApply (H with "HA HB").
Qed.

(* =triple= *)
Notation "{{ P }} m {{ v ; Q }}" := (P ⊢ wp m (fun v => Q))
(* =end= *)
                                      (at level 20,
                                        format "'[hv' {{  P  }}  '/  ' m  '/'  {{  v ;  Q  }} ']'").

Lemma ret_spec {X} (v : X) H (Q : X -> iProp) :
  (H ⊢ Q v) -> {{ H }} (ret v : Free Fresh X) {{ v'; Q v' }}.
Proof. simpl; iIntros. iApply H0; auto. Qed.

Lemma bind_spec {X Y} (e : Free Fresh X) (f : X -> Free Fresh Y) Q Q' (H : iProp) :
  ({{ H }} e {{ v; Q' v }}) ->
  (∀ v, {{ Q' v }} f v {{ v'; Q v' }}) ->
  {{ H }} do v <- e; f v {{ v; Q v}}.
Proof.
  intros. iIntros "HA".
  iApply (wp_bind e f _ Q' with "[HA]").
  - iApply (H0 with "[HA]"); auto.
  - iIntros (v) "HC". iApply (H1 with "[HC]"); auto.
Qed.

Section Rules.

Variable X: Type.
Implicit Type P: iProp.
Implicit Type Q: X -> iProp.

(* =rule_consequence= *)
Lemma rule_consequence: forall P P' Q Q' m,
  ({{ P' }} m {{ v; Q' v }}) ->
  (P ⊢ P') ->
  (forall v, Q' v ⊢ Q v) ->
 (*-----------------------*)
  {{ P }} m {{ v; Q v }}.
(* =end= *)
Proof.
  intros. iIntros "HA". iDestruct (H0 with "HA") as "HA".
  iDestruct (H with "HA") as "HA". iApply (wp_consequence with "HA").
  iIntros "*". iApply H1.
Qed.


Lemma frame_bind : forall (P : iProp), ⊢ P -∗ emp ∗ P.
Proof. iIntros "* $". Qed.

(* =rule_frame= *)
Lemma rule_frame: forall P Q R m,
  ({{ P }} m {{ v; Q v }}) ->
  (*----------------------------*)
  {{ P ∗ R }} m {{ v; Q v ∗ R }}.
(* =end= *)
Proof.
  intros. iIntros "[HA HC]". iApply (wp_consequence with "[HA]").
  iApply H; auto. iIntros; iFrame.
Qed.

End Rules.

Lemma intro_true_r {X} (H : iProp) Q (e : Free Fresh X) :
  ({{ emp ∗ H }} e {{ v; Q v }}) ->
  {{ H }} e {{ v; Q v }}.
Proof.
  intro P. iIntros "HA". iApply (P with "[HA]"). iFrame.
Qed.

(* =rule_fresh= *)
Lemma rule_gensym: {{ emp }} gensym tt {{ ident; & ident }}.
(* =end= *)
Proof. simpl.  iIntros "H" (v) "H2". iFrame. Qed.



Ltac Frame := eapply intro_true_r; eapply frame.
Ltac iRet := eapply ret_spec; auto.
Ltac iBind := eapply bind_spec; [idtac | intro; idtac].


(****************************************************************)
(* =inject= *)
Fixpoint inject (n : nat) : gset positive :=
  match n with
  | 0 => ∅
  | S m => {[ encode m ]} ∪ (inject m)
  end.
(* =end= *)

(* =ord_disjoint= *)
Lemma ord_disjoint : forall n v, v >= n -> encode v ∉ inject n.
(* =end= *)
Proof.
  induction n; simpl.
  - intros. intro P. inversion P.
  - intros. destruct (Nat.eq_dec v n). subst. lia.
    intro P. apply elem_of_union in P. destruct P as [P | P].
    + inversion P. rewrite lookup_singleton_ne in H1; auto. inversion H1.
      intro. eapply encode_inj in H0. subst. auto.
    + eapply IHn. 2 : eauto. lia.
Qed.

Lemma next_disjoint : forall n, inject n ## {[ encode n ]}.
Proof.
  intro. apply disjoint_singleton_r. apply ord_disjoint. auto.
Qed.

(* =soundness= *)
Lemma soundness {X} : forall (e : Free Fresh X) (Q : X -> iProp) n n' v,
    {{ && (inject n) }} e {{ v; Q v }} ->
    eval e n = (v, n') ->
    && (inject n') ⊢ Q v .
(* =end= *)
Proof.
  fix e 1.
  destruct e0 as [v | Y [] k]; intros.
  - inversion H0; subst. iApply H.
  - simpl in *. eapply e.
    2 : apply H0.
    + iIntros "HA". simpl.
      iDestruct (heap_ctx_split_sing with "HA") as "[HA HB]". apply next_disjoint.
      iDestruct (H with "HA") as "HA".
      iApply ("HA" with "HB").
Qed.

(* =adequacy= *)
Lemma adequacy : forall {X} {m: Free Fresh X} {Q},
    {{ emp }} m {{ v; ⌜Q v⌝ }} ->
    Q (run m).
(* =end= *)
Proof.
intros. unfold run.
apply (soundness_pure (inject (eval m 0).2)).
eapply (soundness m (fun v => ⌜Q v⌝) 0).
iIntros "_"; iApply H; auto.
apply surjective_pairing.
Qed.

(****************************************************************)

Fixpoint flatten {X} (t: Tree X) : list X :=
  match t with
  | Leaf v => cons v nil
  | Node l r => flatten l ++ flatten r
  end.

Fixpoint sameShape {X Y} (t1 : Tree X) (t2 : Tree Y) : Prop :=
  match t1,t2 with
  | Leaf _, Leaf _ => True
  | Node l r, Node l_res r_res  => sameShape l l_res /\ sameShape r r_res
  | _, _ => False
  end.

Section Label_spec_aux.

Variable X: Type.
Implicit Type t: Tree X.

(* =label_spec_aux= *)
Lemma label_spec_aux : forall t,
    {{ emp }}
      label t
    {{ ft; ([∗ list] x ∈ flatten ft, & x) ∗ ⌜sameShape t ft⌝ }}.
(* =end= *)
Proof.
  induction t.
  - iBind. eapply rule_gensym. iRet. simpl; auto.
  - simpl label. iBind. eapply IHt1. iBind. Frame. eapply IHt2. iRet.
    iIntros "[[HA %] [HB %]]". iSplitL; auto.
    simpl. iApply big_sepL_app. iFrame.
Qed.

End Label_spec_aux.

Lemma sep_list_fold : forall (a : nat) l, ⊢ (& a -∗ ([∗ list] x ∈ l, & x) -∗ ⌜a ∉ l⌝ : iProp).
Proof.
  induction l; iIntros "* HA HB".
  - iPureIntro. intro. inversion H.
  - iDestruct "HB" as "[HA' HB]".
    iDestruct (singleton_neq with "HA HA'") as "%".
    iDestruct (IHl with "HA HB") as "%". iPureIntro.
    intro. inversion H1; subst; auto.
Qed.

Lemma fold_nodup :
(* =fold_nodup= *)
  forall idents, ⊢ ([∗ list] i ∈ idents, & (i: ident)) -∗ ⌜NoDup idents⌝.
(* =end= *)
Proof.
  induction idents; simpl; iIntros "HA".
  - iPureIntro. apply NoDup_nil_2.
  - iDestruct "HA" as "[HA HB]". iDestruct (IHidents with "HB") as "%".
    iDestruct (sep_list_fold with "HA HB") as "%".
    iPureIntro. constructor; auto.
Qed.

Section Relabel_spec.

Variable X: Type.
Implicit Type t: Tree X.
Implicit Type ft: Tree nat.

(* =label_spec= *)
Lemma label_spec: forall t,
    {{ emp }} label t {{ ft; ⌜NoDup (flatten ft) /\ sameShape t ft⌝ }}.
(* =end= *)
Proof.
intros.
iApply rule_consequence.
- apply label_spec_aux.
- auto.
- iIntros (v) "H".
  iDestruct "H" as "[H1 H2]".
  iDestruct (fold_nodup with "H1") as "H1".
  iSplit; auto.
Qed.

(* =relabel_spec= *)
Lemma relabel_spec : forall t ft,
    relabel t = ft -> NoDup (flatten ft) /\ sameShape t ft.
(* =end= *)
Proof.
  intros. unfold relabel in H. subst.
  eapply (adequacy (label_spec _)).
Qed.

End Relabel_spec.

Print Assumptions relabel_spec.
