From Equations Require Import Equations.
Require Import Ascii String.
Require Import FunctionalExtensionality.
From stdpp Require Import numbers.
Import N.

From Formalisation Require Export Span.
From FreeMonad Require Import FreeMonad.
From SepLogic Require Import SepSet.
From Formalisation Require Import IsFresh Inject.
From Classes Require Import Foldable.
From Examples Require Import example2.

Open Scope N_scope.

Definition octet := N.
Definition data := list octet.

(* =DECODE= *)
Inductive DECODE : Type -> Type :=
| TakeOp : N -> DECODE span
| ReadOp : span -> N -> DECODE octet
| FailOp : forall {X}, DECODE X.
(* =end= *)

(* =Decodeur= *)
Definition Decodeur := Free DECODE.
(* =end= *)

(* =take= *)
Definition take (n : N) : Decodeur span := gen (TakeOp n).
(* =end= *)

(* =read= *)
Definition read (s : span) (pos : N): Decodeur N := gen (ReadOp s pos).
(* =end= *)

(* =fail= *)
Definition fail {X} : Decodeur X := gen FailOp.
(* =end= *)

(* =wp= *)
Fixpoint wp {X} (m: Decodeur X) (Q : X -> iProp) : iProp :=
  match m with
  | ret v => Q v
  | op (TakeOp n) k => ∀ v, IsFresh v -∗ wp (k v) Q
  | op (ReadOp s n) k => ∀ v , wp (k v) Q
  | op FailOp _ => True
  end.
(* =end= *)

Local Open Scope free_monad_scope.

Lemma wp_bind {X Y} (e : Decodeur X) (f :  X → Decodeur Y) (Q : Y -> iProp) (Q' : X -> iProp) :
  wp e Q' ⊢
    (∀ v,  Q' v -∗ wp (f v) Q ) -∗
    wp (let! v := e in f v) Q %I.
Proof.
  iIntros "HA HB". revert e. fix e 1.
  destruct e0 as [v | Z []]; simpl; auto.
  - iApply ("HB" with "HA").
  - iIntros (v) "HC". iDestruct ("HA" with "HC") as "HA".
    iPoseProof "HB" as "HB". apply e.
  - iIntros (v). iDestruct ("HA" $! v) as "HA".
    iPoseProof "HB" as "HB". apply e.
Qed.

Lemma wp_consequence {X} (P Q : X -> iProp) (f : Decodeur X) :
  ⊢ wp f P -∗
    (∀ x, P x -∗ Q x) -∗
    wp f Q.
Proof.
  induction f as [v | Y [] k]; simpl; intros; auto.
  - iIntros "HA HB". iApply ("HB" with "HA").
  - iIntros "HA HB * HC". iDestruct ("HA" with "HC") as "HA".
    iApply (H with "HA HB").
  - iIntros "HA HB" (v). iApply (H with "HA HB").
Qed.


Notation "{{ P }} m {{ v ; Q }}" := (P ⊢ wp m (fun v => Q))
                                      (at level 20,
                                        format "'[hv' {{  P  }}  '/  ' m  '/'  {{  v ;  Q  }} ']'").

Lemma rule_ret {X} (v : X) H (Q : X -> iProp) :
  (H ⊢ Q v) -> {{ H }} (ret v : Decodeur X) {{ v'; Q v' }}.
Proof. simpl; iIntros. iApply H0; auto. Qed.

Lemma rule_bind {X Y} (e : Decodeur X) (f : X -> Decodeur Y) Q Q' (H : iProp) :
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

  Lemma rule_consequence: forall P P' Q Q' m,

      ({{ P' }} m {{ v; Q' v }}) ->
      (P ⊢ P') ->
      (forall v, Q' v ⊢ Q v) ->
      (*-----------------------*)
      {{ P }} m {{ v; Q v }}.
  Proof.
    intros. iIntros "HA". iDestruct (H0 with "HA") as "HA".
    iDestruct (H with "HA") as "HA". iApply (wp_consequence with "HA").
    iIntros "*". iApply H1.
  Qed.


  Lemma frame_bind : forall (P : iProp), ⊢ P -∗ emp ∗ P.
  Proof. iIntros "* $". Qed.

  Lemma rule_frame: forall P Q P' m,

      ({{ P }} m {{ v; Q v }}) ->
      (*----------------------------*)
      {{ P ∗ P' }} m {{ v; Q v ∗ P' }}.
  Proof.
    intros. iIntros "[HA HC]". iApply (wp_consequence with "[HA]").
    iApply H; auto. iIntros; iFrame.
  Qed.

(* =rule_fail= *)
Lemma rule_fail H Q : {{ H }} fail {{ v; Q v }}.
(* =end= *)
Proof. auto. Qed.

(* =rule_read= *)
Lemma rule_read s res : {{ emp }} read s res {{ _; emp }}.
(* =end= *)
Proof. eauto. Qed.

(* =rule_take= *)
Lemma rule_take n : {{ emp }} take n {{ v; IsFresh v }}.
(* =end= *)
Proof. simpl. eauto. Qed.

End Rules.

(* =packet_SSHS= *)
Record packet_SSHS (S : Type) :=
  mk_ssh {
      packet_length : N;
      padding_length : N;
      payload : S;
      mac : S; }.
(* =end= *)

Arguments mk_ssh [S].
Arguments packet_length [S].
Arguments padding_length [S].
Arguments payload [S].
Arguments mac [S].

(* =packet_SSH= *)
Definition packet_SSH := packet_SSHS span.
(* =end= *)


Import Monoid.

Section foldr.

(* =foldr= *)
Definition foldMap `{Monoid M} {A} (m : A -> M) (p : packet_SSHS A) : M :=
  Monoid.f (m (payload p)) (m (mac p)).
(* =end= *)

End foldr.

Local Instance Foldable_SSH : Foldable packet_SSHS :=
  Build_Foldable _ (@foldMap).

(* =decode_next= *)
Definition decode_next : Decodeur N :=
  let! s := take 1 in
  read s 0.
(* =end= *)

(* =rule_next= *)
Lemma rule_next : {{ emp }} decode_next {{ _; True }}.
(* =end= *)
Proof.
  eapply rule_bind.
  eapply rule_take.
  intro. eapply rule_consequence. eapply rule_frame. eapply rule_read.
  iIntros "HA". iSplitR; eauto. iApply "HA".
  eauto.
Qed.

(* =decode_u32= *)
Definition decode_u32 :=
  let! a := decode_next in
  let! b := decode_next in
  let! c := decode_next in
  let! d := decode_next in
  ret (to_u32 a b c d).
(* =end= *)

(* =rule_u32= *)
Lemma rule_u32 : {{ emp }} decode_u32 {{ _; True }}.
(* =end= *)
Proof.
  eapply rule_bind.
  eapply rule_next.
  intro. eapply rule_bind.
  eapply rule_consequence. eapply rule_frame. eapply rule_next.
  iIntros "HA". iSplitR; eauto. iApply "HA". eauto.
  intro. eapply rule_bind.
  eapply rule_consequence. eapply rule_frame. eapply rule_next.
  iIntros "HA". iSplitR; eauto. iApply "HA". eauto.
  intro. eapply rule_bind.
  eapply rule_consequence. eapply rule_frame. eapply rule_next.
  iIntros "HA". iSplitR; eauto. iApply "HA". eauto.
  eauto.
Qed.

(* =decode_packet_SSH= *)
Definition decode_packet_SSH : Decodeur packet_SSH :=
  let! packet_length := decode_u32 in
  let! padding_length := decode_next in
  if padding_length + 1 <=? packet_length
  then
    let! payload := take (packet_length - padding_length - 1) in
    let! padding := take padding_length in
    let! mac := take 20 in
    ret (mk_ssh packet_length padding_length payload mac)
  else
    fail.
(* =end= *)

(* =rule_decode_packet_SSH= *)
Lemma rule_decode_packet_SSH :
  {{ emp }} decode_packet_SSH {{ v; <absorb> all_disjointMSL v }}.
(* =end= *)
Proof.
  eapply rule_bind.
  eapply rule_u32.
  intro. eapply rule_bind.
  eapply rule_consequence. eapply rule_frame. eapply rule_next.
  iIntros "HA". iSplitR; eauto. iApply "HA". eauto.
  intro. destruct (v0 + 1 <=? v).
  - eapply rule_bind.
    eapply rule_consequence. eapply rule_frame. eapply rule_take.
    iIntros "HA". iSplitR; eauto. iApply "HA". eauto.
    intro. eapply rule_bind.
    eapply rule_consequence. eapply rule_frame. eapply rule_take.
    iIntros "HA". iSplitR; eauto. iApply "HA". eauto.
    intros. eapply rule_bind.
    eapply rule_consequence. eapply rule_frame. eapply rule_take.
    iIntros "HA". iSplitR; eauto. iApply "HA". eauto.
    intros. eapply rule_ret. iIntros. iNorm.
    unfold all_disjointMSL, all_disjointSL. simpl. iFrame.
  - eapply rule_fail.
Qed.

Close Scope free_monad_scope.

Section eval.

  Context {X : Type}.

(* =eval= *)
Fixpoint eval (m : Decodeur X) : DecodeurM X :=
  match m with
  | ret v => ret! v
  | op (TakeOp n) k =>
      let! v := takeM n in
      eval (k v)
  | op (ReadOp s pos) k =>
      let! v := readM s pos in
      eval (k v)
  | op FailOp _ =>
      failM
  end.
(* =end= *)

End eval.

Section decode.

  Context {X : Type}.

(* =decode= *)
Definition decode (d : Decodeur X) (data : data) : option X :=
  match eval d data (mk_span 0 (length data)) with
  | Some (v, _) => Some v
  | _ => None
  end.
(* =end= *)

End decode.

Lemma eval_monotone : forall X (e : Decodeur X) s1 s2 a v,
    eval e a s1 = Some (v, s2) ->
    (pos s1 <= pos s2)%N /\ (pos s2 + len s2 <= pos s1 + len s1)%N.
Proof.
  fix IH 2.
  destruct e as [v  | Y []]; simpl; intros.
  - inversion H. split; lia.
  - unfold eval in H. fold (@eval X) in H. unfold bind in H. unfold takeM in H.
    destruct ((n <=? len s1)%N) eqn:?. 2 : inversion H.
    eapply IH in H as [P0 P1]. eapply N.leb_le in Heqb. simpl in *. lia.
  - unfold eval in H. fold (@eval X) in H. unfold bind in H. unfold readM in H.
    destruct ((n <? len s)%N) eqn:?. 2 : inversion H.
    destruct (lookup (pos s + n) a). 2 : inversion H.
    eapply IH in H as [P0 P1]. eapply N.ltb_lt in Heqb. lia.
  - inversion H.
Qed.

(* =soundness= *)
Lemma soundness : forall X d H (Q : X -> iProp),
    {{ H }} d {{v ; Q v }} ->
    forall data s (v : X) s',
      eval d data s = Some (v, s') ->
      H ∗ injectSL (pos s) (pos s') ⊢ Q v.
(* =end= *)
Proof.
  fix IH 2.
  destruct d as [v | Y []]; simpl; intros.
  (* ret *)
  - iIntros "[HA HB]". inversion H1. subst.
    iDestruct (injectSL_emp with "HB") as "_". lia.
    iApply (H0 with "HA").
  (* take *)
  - unfold eval in H1. fold (@eval X) in H1. unfold bind in H1. unfold takeM in H1.
    destruct ((n <=? len s)%N) eqn:?.
    2 : inversion H1.
    epose H1 as grow.
    eapply eval_monotone in grow as [P0 P1]. simpl in *.
    iIntros "[HA HB]". iApply IH; eauto. simpl.
    unfold injectSL. rewrite (inject_union (pos s + n)). 2-3 : lia.
    iDestruct (big_sepS_union with "HB") as "[HC HB]". apply inject_disjoint.
    iSplitR "HB"; eauto.
    iApply (H0 with "HA [HC]").
    iApply (inject_IsFresh with "HC"); simpl; lia.
  (* read *)
  - unfold eval in H1. fold (@eval X) in H1. unfold bind in H1. unfold readM in H1.
    destruct ((n <? len s)%N) eqn:?. 2 : inversion H1.
    destruct (lookup (pos s + n) data0). 2 : inversion H1.
    iIntros "[HA HB]". iApply IH; eauto. iFrame. iApply (H0 with "HA").
  (* fail *)
  - inversion H1.
Qed.

Definition injectPos (start : N) (fin : N) : gset positive :=
  set_map encode (inject start fin).

Lemma encode_disj : forall (B : gset N) n,
    n ∉ B -> ({[encode n]} : gset positive) ## set_map encode B.
Proof.
  induction B as [ | n0 set not_in IH] using set_ind_L; simpl; intros.
  - rewrite set_map_empty. eapply disjoint_empty_r.
  - repeat intro. apply elem_of_singleton_1 in H0. subst.
    rewrite set_map_union_L in H1. apply elem_of_union in H1.
    destruct H1.
    + apply H. rewrite set_map_singleton_L in H0. apply elem_of_singleton in H0.
      apply elem_of_union. left. apply elem_of_singleton. apply encode_inj. apply H0.
    + assert (n ∉ set). intro. apply H. apply elem_of_union. right. apply H1.
      apply IH in H1.
      edestruct H1. eapply elem_of_singleton. reflexivity. eapply H0.
Qed.


Lemma lemma_final : forall start fin, && injectPos start fin ⊢ injectSL start fin.
Proof.
  iIntros (start fin).
  unfold injectPos, injectSL.
  induction (inject start fin) as [ | A B C D] using set_ind_L; iIntros "HA".
  - rewrite set_map_empty. iApply big_sepS_empty. auto.
  - rewrite set_map_union_L. iDestruct (heap_ctx_split with "HA") as "[HA HB]".
    rewrite set_map_singleton. eapply encode_disj. eauto.
    iApply big_sepS_union. apply disjoint_singleton_l. auto.
    iSplitL "HA".
    + rewrite set_map_singleton_L. iApply big_sepS_singleton. iFrame.
    + iApply (D with "HB").
Qed.

Section adequacy.

  Context {X : Type}.

(* =adequacy= *)
Theorem adequacy : forall d (Q : X -> Prop),
    {{ emp }} d {{ v; ⌜Q v⌝ }} ->
    forall data v,
      decode d data = Some v ->
      Q v.
(* =end= *)
Proof.
  intros. unfold decode in H0.
  destruct (eval d data0) as  [[r s]| ] eqn:?. 2 : inversion H0.
  injection H0. intro. subst. eapply soundness_pure.
  iIntros "HA". iApply (soundness _ d emp (fun v => ⌜ Q v ⌝)); eauto.
  iSplitR; auto. simpl. iApply lemma_final; eauto.
Qed.

End adequacy.
