From Equations Require Import Equations.
Require Import Ascii String.
Require Import FunctionalExtensionality.
From stdpp Require Import numbers.
Import N.

Open Scope N_scope.

Definition octet := N.

Definition data := list octet.

Definition Decodeur X := data -> option (X * data).

Definition decode {X} (d : Decodeur X) (l : data) : option X :=
  match d l with
  | None => None
  | Some (v, _) => Some v
  end.

Definition decode_pair : Decodeur (octet * octet) :=
  fun d =>
    match d with
    | [_] | [] => None
    | e0 :: e1 :: t => Some ((e0, e1), t)
    end.

Definition fmap {X Y} (f : X -> Y) (e : Decodeur X) : Decodeur Y :=
  fun d => match e d with
           | None => None
           | Some (v, s) => Some (f v, s)
           end.

Definition decode_add : Decodeur N :=
  fmap (fun v => fst v + snd v) decode_pair.

Definition decode_mult : Decodeur N :=
  fmap (fun v => fst v * snd v) decode_pair.

Reset decode_pair.


Definition fmap {X Y} (f : X -> Y) (e : Decodeur X) : Decodeur Y :=
  fun d => match e d with
           | None => None
           | Some (v, s) => Some (f v, s)
           end.


Lemma fmap_id : forall X (d : Decodeur X), fmap id d = d.
Proof.
  intros. unfold fmap. eapply FunctionalExtensionality.functional_extensionality.
  intros. destruct (d x) as [[v s]|]; reflexivity.
Qed.

Lemma fmap_comp : forall X Y Z (f: X -> Y) (g : Y -> Z), fmap (g ∘ f) = fmap g ∘ fmap f.
Proof.
  unfold fmap. unfold compose.
  intros. eapply FunctionalExtensionality.functional_extensionality.
  intros. eapply FunctionalExtensionality.functional_extensionality.
  intros. destruct (x x0) as [[v s]|]; reflexivity.
Qed.

Definition app {X Y} (f : Decodeur (X -> Y)) (x : Decodeur X) : Decodeur Y :=
  fun s => match f s with
           | None => None
           | Some (f,s) => fmap f x s
           end.

Notation " f '<*>' g" := (app f g)(at level 50).

Definition pure {X} : X -> Decodeur X := fun x s => Some (x,s).


Lemma app_id : forall X (v : Decodeur X), pure id <*> v = v.
Proof. intros. unfold app, pure. eapply fmap_id. Qed.

Lemma app_homo : forall X Y (f : X -> Y) x, pure f <*> pure x = pure (f x).
Proof.
  intros. unfold pure, app. eapply FunctionalExtensionality.functional_extensionality.
  intros. reflexivity.
Qed.

Lemma app_interchance : forall X Y (u : Decodeur (X -> Y)) y, u <*> pure y = pure (fun f => f y) <*> u.
Proof.
  intros. unfold app, pure, fmap. eapply FunctionalExtensionality.functional_extensionality.
  intros. reflexivity.
Qed.

Lemma app_composition : forall X Y Z (u : Decodeur (Y -> Z)) (v : Decodeur (X -> Y)) (w : Decodeur X),
    (pure (fun f g => f ∘ g)) <*> u <*> v <*> w = u <*> (v <*> w).
Proof.
  intros. unfold app, pure, fmap. eapply FunctionalExtensionality.functional_extensionality.
  intros. destruct (u x) as [[v0 s0]|]; auto. destruct (v s0) as [[v1 s1]|]; auto.
  destruct (w s1) as [[v2 s2]|]; auto.
Qed.

Definition decode_next : Decodeur octet :=
  fun d =>
    match d with
    | [] => None
    | h :: t => Some (h, t)
    end.

Definition decode_pair : Decodeur (octet * octet) :=
  pure (fun a b => (a,b)) <*> decode_next <*> decode_next.

Definition bind {X Y} (d : Decodeur X) (f : X -> Decodeur Y) : Decodeur Y :=
  fun s => match d s with
           | None => None
           | Some (v,s) => f v s
           end.

Notation "'let!' v ':=' f 'in' g" := (bind f (fun v => g))(at level 50).
Notation "'ret!' v" := (pure v)(at level 50).

Definition ret_bind : forall X Y v (f : X -> Decodeur Y), bind (ret! v) f = f v.
Proof.
  intros. unfold bind, pure. eapply FunctionalExtensionality.functional_extensionality.
  intros. reflexivity.
Qed.

Definition bind_ret : forall X (v : Decodeur X), bind v pure = v.
Proof.
  intros. unfold bind, pure. eapply FunctionalExtensionality.functional_extensionality.
  intros. destruct (v x) as [[v0 s]|]; reflexivity.
Qed.

Definition bind_assoc : forall X Y Z (v : Decodeur X) f (g : Y -> Decodeur Z),
    bind (bind v f) g = bind v (fun x => bind (f x) g).
Proof.
  intros. unfold bind, pure. eapply FunctionalExtensionality.functional_extensionality.
  intros. destruct (v x) as [[v0 s]|]; reflexivity.
Qed.

Definition to_u32 (a0 a1 a2 a3 : octet) : N :=
  a0 * (N.pow 2 32) + a1 * (N.pow 2 16) + a2  * (N.pow 2 8) + a3.

Definition decode_packet_length : Decodeur N :=
  pure to_u32 <*> decode_next <*> decode_next <*> decode_next <*> decode_next.

Equations take (n : N) (l : list N): option (list octet * list N) by wf (N.to_nat n) Nat.lt :=
  take 0 l := (ret! []) l;
  take n l :=
    match decode_next l with
    | None => None
    | Some (v, l) =>
        match take (N.pred n) l with
        | None => None
        | Some (vs, l) => Some (v :: vs, l)
        end
    end.
Next Obligation.
  lia.
Defined.

Equations take (n : N) : Decodeur data by wf (N.to_nat n) Nat.lt :=
  take 0 := ret! [];
  take n :=
    let! v := decode_next in
    let! vs := take (pred n) in
    ret! (v :: vs).
Next Obligation.
Abort.

Definition fail {X} : Decodeur X := fun _ => None.

Definition decode_payload_SSH : Decodeur data :=
  let! packet_length := decode_packet_length in
  let! padding_length := decode_next in
  if padding_length + 1 <=? packet_length
  then
    let! payload := take (packet_length - padding_length - 1) in
    let! padding := take padding_length in
    ret! payload
  else
    fail.

Definition test := [0;0;0;5;1;0;1;2;15].

Compute (decode decode_payload_SSH test).

Reset Decodeur.

From Formalisation Require Export Span.
From FreeMonad Require Import FreeMonad.
From SepLogic Require Import SepSet.
From Formalisation Require Import IsFresh Inject.


Definition DecodeurM (X : Type) := data -> span -> option (X * span).

Equations length (l: data) : N :=
  length nil := 0;
  length (_ :: t) := N.succ (length t).

Definition decodeM {X} (d : DecodeurM X) (l : data) : option X :=
  match d l (mk_span 0 (length l)) with
  | None => None
  | Some (v, _) => Some v
  end.

Definition pure {X} (v : X) : DecodeurM X := fun data l => Some (v,l).

Definition bind {X Y} (d : DecodeurM X) (k : X -> DecodeurM Y) : DecodeurM Y :=
  fun data l =>
    match d data l with
    | None => None
    | Some (v, s) => k v data s
    end.

Notation "'let!' v ':=' f 'in' g" := (bind f (fun v => g)) (v name, at level 50).
Notation "'ret!' v" := (pure v) (at level 50).

Definition app {X Y} (a : DecodeurM (X -> Y)) (d : DecodeurM X) : DecodeurM Y :=
  let! f := a in
  let! x := d in
  ret! (f x).

Notation " f '<*>' g" := (app f g)(at level 50).

Definition takeM (n : N) : DecodeurM span :=
  fun _ s =>
    if n <=? len s
    then
      let res := mk_span (pos s) n in
      let sres := mk_span (pos s + n) (len s - n) in
      Some (res, sres)
    else
      None.

Equations lookup (n : N) (l : data) : option N by wf (N.to_nat n) Nat.lt :=
  lookup n [] := None;
  lookup 0 (h :: t) := Some h;
  lookup pos (h :: t) := lookup (N.pred pos) t.
Next Obligation.
  lia.
Defined.

Definition readM (s : span) (n : N) : DecodeurM N :=
  fun d t =>
    if n <? len s
    then
      match lookup (pos s + n) d with
      | None => None
      | Some v => Some (v,t)
      end
    else
      None.

Definition decode_nextM : DecodeurM N :=
  let! s := takeM 1 in
  readM s 0.

Definition failM {X} : DecodeurM X := fun _ _ => None.

Definition to_u32 (a0 a1 a2 a3 : octet) : N :=
  a0 * (N.pow 2 32) + a1 * (N.pow 2 16) + a2  * (N.pow 2 8) + a3.

Definition decode_packet_length : DecodeurM N :=
  pure to_u32 <*> decode_nextM <*> decode_nextM <*> decode_nextM <*> decode_nextM.

Definition decode_payload_SSH : DecodeurM span :=
  let! packet_length := decode_packet_length in
  let! padding_length := decode_nextM in
  let! payload := takeM (packet_length - padding_length - 1) in
  let! padding := takeM padding_length in
  ret! payload.

Definition test := [0;0;0;5;1;0;1;2;15].

Compute (decodeM decode_payload_SSH test).


Inductive DECODE : Type -> Type :=
| TakeOp : N -> DECODE span
| ReadOp : span -> N -> DECODE octet
| FailOp : forall {X}, DECODE X.

Definition Decodeur := Free DECODE.

Definition take (n : N) : Decodeur span := syntax_effect (TakeOp n).

Definition read (s : span) (pos : N): Decodeur N := syntax_effect (ReadOp s pos).

Definition fail {X} : Decodeur X := syntax_effect FailOp.

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

Definition fold_r {A B} (f : A -> B -> B) (b : B) (p : packet_SSHS A) : B :=
  f (payload p) (f (mac p) b).

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
  iSplitR; auto. simpl. iApply lemma_final; eauto.
Qed.
