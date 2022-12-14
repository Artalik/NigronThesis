From Equations Require Import Equations.
Require Import Ascii String.
Require Import FunctionalExtensionality.
From stdpp Require Import numbers.
Import N.

From Formalisation Require Export Span.
From FreeMonad Require Import FreeMonad.
From SepLogic Require Import SepSet.
From Formalisation Require Import IsFresh Inject ZeroCopy.
From Classes Require Import Foldable.
From Examples Require Import example2.

Require Import Coq.Program.Equality.

Open Scope N_scope.

Definition octet := N.

Definition data := list octet.

Inductive DECODE : Type -> Type :=
| TakeOp : N -> DECODE span
| ReadOp : span -> N -> DECODE octet
| FailOp : forall {X}, DECODE X.

Definition Decodeur := Free DECODE.

Definition take (n : N) : Decodeur span := gen (TakeOp n).

Definition read (s : span) (pos : N): Decodeur N := gen (ReadOp s pos).

Definition fail {X} : Decodeur X := gen FailOp.

Fixpoint wp {X} (m: Decodeur X) (Q : X -> iProp) : iProp :=
  match m with
  | ret v => Q v
  | op (TakeOp n) k => ∀ v, IsFresh v -∗ wp (k v) Q
  | op (ReadOp s n) k => ∀ v , wp (k v) Q
  | op FailOp _ => True
  end.

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


Notation "{{ P }} m {{ v ; Q }}" := (⊢ P -∗ wp m (fun v => Q))
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

  Lemma rule_fail H Q : {{ H }} fail {{ v; Q v }}.
  Proof. auto. Qed.

  Lemma rule_read s res : {{ emp }} read s res {{ _; emp }}.
  Proof. eauto. Qed.

  Lemma rule_take n : {{ emp }} take n {{ v; IsFresh v }}.
  Proof. simpl. eauto. Qed.

End Rules.

Record packet_SSHS (S : Type) :=
  mk_ssh {
      packet_length : N;
      padding_length : N;
      payload : S;
      mac : S; }.

Arguments mk_ssh [S].
Arguments packet_length [S].
Arguments padding_length [S].
Arguments payload [S].
Arguments mac [S].

Definition packet_SSH := packet_SSHS span.

Definition foldMap M (sg : Monoid.Semigroup M) (m : Monoid.Monoid M)
  {A} (fold : A -> M) (p : packet_SSHS A) : M :=
  Monoid.f (fold (payload p)) (fold (mac p)).

Local Instance Foldable_SSH : Foldable packet_SSHS :=
  Build_Foldable _ (@foldMap).

Definition decode_next : Decodeur N :=
  let! s := take 1 in
  read s 0.

Lemma rule_next : {{ emp }} decode_next {{ _; True }}.
Proof.
  eapply rule_bind.
  eapply rule_take.
  intro. eapply rule_consequence. eapply rule_frame. eapply rule_read.
  iIntros "HA". iSplitR; eauto. iApply "HA".
  eauto.
Qed.

Definition decode_u32 :=
  let! a := decode_next in
  let! b := decode_next in
  let! c := decode_next in
  let! d := decode_next in
  ret (to_u32 a b c d).

Lemma rule_u32 : {{ emp }} decode_u32 {{ _; True }}.
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

Lemma rule_decode_packet_SSH : {{ emp }} decode_packet_SSH {{ v; <absorb> all_disjointMSL v }}.
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

Fixpoint eval {X} (m : Decodeur X) : DecodeurM X :=
  match m with
  | ret v => ret! v
  | op (TakeOp n) k =>
      let! v := takeM n in
      eval (k v)
  | op (ReadOp s pos) k =>
      let! v := readM s pos in
      eval (k v)
  | op FailOp _ => failM
  end.

Definition decode {X} (d : Decodeur X) (data : data) : option X :=
  match eval d data (mk_span 0 (length data)) with
  | Some (v, _) => Some v
  | _ => None
  end.

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

Lemma soundness : forall X d H (Q : X -> iProp),
    {{ H }} d {{v ; Q v }} ->
    forall data s (v : X) s',
      eval d data s = Some (v, s') ->
      H ∗ injectSL (pos s) (pos s') ⊢ Q v.
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

Theorem adequacy : forall X d (Q : X -> Prop),
    {{ emp }} d {{ v; ⌜Q v⌝ }} ->
    forall data v,
      decode d data = Some v ->
      Q v.
Proof.
  intros. unfold decode in H0.
  destruct (eval d data0) as  [[r s]| ] eqn:?. 2 : inversion H0.
  injection H0. intro. subst. eapply soundness_pure.
  iIntros "HA". iApply (soundness _ d emp (fun v => ⌜ Q v ⌝)); eauto.
  iSplitR; auto. simpl. iApply big_op_ctx. eauto.
Qed.

Lemma Fresh_ZC_aux `{Foldable M}: forall e s n s_res,
    {{ injectSL n (pos s) }} e {{ res; <absorb> all_disjointMSL res }} ->
    forall (data : data) (res : M span),
      n <= pos s ->
      eval e data s = Some (res, s_res) ->
      forall v, v ∈ M_to_list res ->
           set_span v ⊆ inject n (pos s + len s).
Proof.
  revert M H. fix IH 3. intros M H e.
  dependent destruction e; intros; simpl in *. revert H1 H2. intros LE H1.
  - inversion H1. subst. clear H1.
    revert H0. MonPred.unseal. unfold monpred.monPred_wand_def. simpl.
    unfold monpred.monPred_upclosed. simpl. intro. destruct H0. simpl in *.
    edestruct (monPred_in_entails tt). clear monPred_in_entails.
    instantiate (1 := ∅). MonPred.unseal.
    split. split. inversion_star h P. clear H0.
    red in P1. destruct P1. inversion H1. subst. clear H1. clear P2.
    rewrite union_empty_r_L in P. clear monPred_in_entails. subst.
    edestruct H0.
    + eexists ∅, _. repeat split; auto. 2 : eapply disjoint_empty_l.
      eapply SepSet.soundness. iIntros "HA". iApply big_op_ctx. iApply "HA".
    + destruct H1 as [h [P3 [P1 [P2 P4]]]]. clear H0 P0 P3.
      rewrite union_empty_l_L in P4.
      transitivity (inject n (Span.pos s_res)).
      2 : { eapply inject_mono_r. lia. }
      rewrite P4. transitivity h. 2 : set_solver. clear P2 P4. unfold all_disjointMSL in P1.
      eapply (all_disjointSL_incl _ _ H3 _ P1).
  - destruct d; simpl in *.
    + unfold set_span.
      unfold bind, takeM in H2.
      destruct (n0 <=? len s) eqn:?.
      * pose (mono := H2). eapply eval_monotone in mono as [P0 P1]. simpl in *.
        eapply N.leb_le in Heqb. assert (pos s + len s = pos s + n0 + (len s - n0)) by lia.
        rewrite H4.
        unfold set_span in IH.
        eapply (IH _ _ _ {| pos := pos s + n0; len := len s - n0 |}); simpl in *; eauto.
        2 : lia.
        iIntros "HA". unfold injectSL. rewrite (inject_add n0 n (pos s)). 2 : lia.
        iDestruct (big_sepS_union with "HA") as "[HA HB]". eapply inject_disjoint.
        iDestruct (inject_IsFresh with "[HB]") as "HB"; eauto.
        unfold injectSL. instantiate (1 := (mk_span (pos s) n0)). simpl. iApply "HB".
        iApply (H0 with "HA HB").
      * inversion H2.
    + unfold bind, readM in H2.
      destruct (n0 <? len s0) eqn:?.
      destruct (lookup (pos s0 + n0) data0) eqn:?.
      eapply IH; eauto.
      iIntros "HA". iDestruct (H0 with "HA") as "HB". iApply "HB".
      inversion H2. inversion H2.
    + inversion H2.
Qed.


Lemma eval_ZC `{Foldable M}: forall e,
    {{ emp }} e {{ res; <absorb> all_disjointMSL res }} ->
    forall (data : data) (res : M span) s s_res,
      eval e data s = Some (res, s_res) ->
      Result_in res s.
Proof.
  unfold Result_in. intros. eapply Fresh_ZC_aux.
   iIntros "HA". iApply H0.
   iApply (injectSL_emp with "HA"). lia. lia. eauto. auto.
Qed.

Definition decode_zerocopy `{Foldable M} (e : Decodeur (M span)) := forall data res,
      decode e data = Some res ->
      Result_in res (mk_span 0 (length data)).

Lemma decode_ZC `{Foldable M}: forall e,
    {{ emp }} e {{ res; <absorb> all_disjointMSL res }} ->
    decode_zerocopy e.
Proof.
  unfold decode_zerocopy, decode. intros.
  destruct eval as [[v s_v]|] eqn:?; inversion H1. subst.
  eapply eval_ZC; eauto.
Qed.
