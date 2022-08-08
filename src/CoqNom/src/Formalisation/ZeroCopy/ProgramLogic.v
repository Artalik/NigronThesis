From SepLogic Require Export SepBasicCore SepSet.
From Formalisation Require Export IsFresh Nom.

Section wp.

  Context {atom : Type}.

Fail
(* =wp= *)
Fixpoint wp {X} (m: @NomG atom X) (Q : X -> iProp) : iProp :=
  match m with
  | ret v => Q v
  | op FAIL _ => True
  | op (LOCAL None _) c | op (READ _ _) c | op LENGTH c => ∀ v, wp (c v) Q
  | op (TAKE n) c => ∀ v, IsFresh v -∗ wp (c v) Q
  | op (ALT c1 c2) c => wp c1 (fun v => wp (c v) Q) ∧ wp c2 (fun v => wp (c v) Q)
  | op (LOCAL (Some range) e) c =>
      IsFresh range ∗ wp e (fun v => wp (c v) Q)
  | op (REPEAT _ e b) c => ∃ Q',
    Q' b ∗
      (<pers> ∀ res, Q' res -∗ wp (e res) Q') ∗
      (∀ res, Q' res -∗ wp (c res) Q)
  end.
(* =end= *)

Fixpoint wp {X} (m: @NomG atom X) (Q : X -> iProp) : iProp :=
  match m in (NomG T) return ((T -> iProp) -> iProp) with
  | ret v => fun Q => Q v
  | op FAIL _ => fun _ => True
  | op (LOCAL None _) c | op (READ _ _) c | op LENGTH c => fun Q => ∀ v, wp (c v) Q
  | op (TAKE n) c => fun Q => ∀ v, IsFresh v -∗ wp (c v) Q
  | op (ALT c1 c2) c => fun Q => wp c1 (fun v => wp (c v) Q) ∧ wp c2 (fun v => wp (c v) Q)
  | op (LOCAL (Some range) e) c =>
      fun Q => IsFresh range ∗ wp e (fun v => wp (c v) Q)
  | op (REPEAT _ e b) c =>
      fun Q => ∃ Q',
          Q' b ∗
            (<pers> ∀ res, Q' res -∗ wp (e res) Q') ∗
            (∀ res, Q' res -∗ wp (c res) Q)
  end Q.

  Lemma wp_consequence : forall {X} (e : NomG X) (P Q : X -> iProp),
      ⊢ wp e P -∗
        (∀ v, P v -∗ Q v) -∗
        wp e Q.
  Proof.
    fix IH 2; destruct e; simpl; intros.
    - iIntros "HA HB". iApply ("HB" with "HA").
    - destruct n; iIntros "HA HB"; auto.
      + iIntros (v). iApply (IH with "HA HB").
      + iIntros (v). iApply (IH with "HA HB").
      + iIntros (v) "HC". iApply (IH with "[HA HC] HB"). iApply ("HA" with "HC").
      + iSplit.
        * iDestruct "HA" as "[HA _]". iApply (IH with "HA").
          iIntros (v) "HA". iApply (IH with "HA HB").
        * iDestruct "HA" as "[_ HA]". iApply (IH with "HA").
          iIntros (v) "HA". iApply (IH with "HA HB").
      + destruct o.
        * iNorm. iFrame. iApply (IH with "HD"). iIntros (v) "HA". iApply (IH with "HA HB").
        * iIntros (v). iApply (IH with "HA HB").
      + iNorm. iExists x0. iSplitL "HC"; auto.
        iSplitL "HE"; auto.
        iIntros (res) "HE". iDestruct ("HF" with "HE") as "HA".
        iApply (IH with "HA HB").
  Qed.

  Lemma wp_bind : forall {X} (e : NomG X) {Y} (f : X → NomG Y) (Q : Y -> iProp),
      ⊢ wp e (fun v => wp (f v) Q) -∗ wp (let! v := e in f v) Q.
  Proof.
    intros X e.
    eapply (Nom_ind (fun X e => forall Y (f : X → NomG Y) Q,
                         ⊢ wp e (λ v : X, wp (f v) Q) -∗ wp (let! v := e in f v) Q));
      intros; iIntros "HA"; simpl; auto.
    - iIntros (v). iApply (H with "HA").
    - iIntros (v) "HC". iApply H. iApply ("HA" with "HC").
    - iIntros (v). iApply (H with "HA").
    - iSplit.
      + iDestruct "HA" as "[HA _]". iApply (wp_consequence with "HA").
        iIntros (v) "HA". iApply (H1 with "HA").
      + iDestruct "HA" as "[_ HA]". iApply (wp_consequence with "HA").
        iIntros (v) "HA". iApply (H1 with "HA").
    - iNorm. iFrame. iApply (wp_consequence with "HC").
      iIntros (v) "HA". iApply (H0 with "HA").
    - iIntros. iApply (H0 with "HA").
    - iNorm. iExists x. iSplitL "HB"; auto. iSplitL "HD"; auto.
      iIntros. iApply H0. iApply "HE". iFrame.
  Qed.



  (* Lemma wp_bind {X Y} (e : NomG X) (f : X → NomG Y) (Q : Y -> iProp) (Q' : X -> iProp) : *)
  (*   wp e Q' ⊢ (∀ v,  Q' v -∗ wp (f v) Q) -∗ wp (let! v := e in f v) Q. *)
  (* Proof. *)
  (*   induction e; simpl; iIntros "HA HB". *)
  (*   - iApply ("HB" with "HA"). *)
  (*   - destruct n; eauto; iIntros; iNorm; try iApply (H with "HA HB"). *)
  (*     + iApply (H with "[HA HC] HB"). iApply ("HA" with "HC"). *)
  (*     + iExists x. iFrame. iIntros (v) "HA". *)
  (*       iDestruct ("HD" with "HA") as "HA". iApply (H with "HA HB"). *)
  (*     + destruct o. iNorm. *)
  (*       iFrame. iExists x. iFrame. iIntros (v) "HA". *)
  (*       iDestruct ("HF" with "HA") as "HA". iApply (H with "HA HB"). *)
  (*       iIntros (v). iApply (H with "HA HB"). *)
  (*     + iExists x0. iFrame. iIntros (res) "HE". *)
  (*       iDestruct ("HF" with "HE") as "HA". iApply (H with "HA HB"). *)
  (* Qed. *)

  Lemma bind_wp : forall X Y (e : NomG X) (k : X -> NomG Y) Q,
      wp (let! v := e in k v) Q ⊢
        wp e (fun v => wp (k v) Q).
  Proof.
    fix IH 3. destruct e; simpl; intros; iIntros "HA".
    - iApply "HA".
    - destruct n.
      + iApply "HA".
      + iIntros (v). iApply (IH with "HA").
      + iIntros (v). iApply (IH with "HA").
      + iIntros (v) "HB". iApply IH. iApply ("HA" with "HB").
      + iSplit.
        * iDestruct "HA" as "[HA _]". iApply (wp_consequence with "HA").
          iIntros. iApply IH. iFrame.
        * iDestruct "HA" as "[_ HA]". iApply (wp_consequence with "HA").
          iIntros. iApply IH. iFrame.
      + destruct o.
        iNorm. iFrame. iApply (wp_consequence with "HC").
        iIntros. iApply IH. iFrame.
        iIntros (v). iApply (IH with "HA").
      + iNorm. iExists x0. iSplitL "HB"; auto. iSplitL "HD"; auto.
        iIntros (v) "HA". iApply IH. iApply ("HE" with "HA").
  Qed.

  Notation "'{{' P } } e {{ v ; Q } }" := (⊢  P -∗ wp e (fun v => Q) )
                                            (at level 20, format "'[hv' {{  P  } }  '/  ' e  '/'  {{ v ;  Q  } } ']'").


  Lemma consequence_rule {X} (e : NomG X) Q Q' H H':
    {{ H' }} e {{ v; Q' v }} ->
    (H ⊢ H') ->
    (∀ v, Q' v ⊢ Q v) ->
    {{ H }} e {{ v; Q v }}.
  Proof.
    intros. iIntros "HA". iApply (wp_consequence with "[HA]").
    iApply H0. iApply (H1 with "HA"). simpl. iIntros (v). iApply H2.
  Qed.


  Lemma bind_rule {X Y} (e : NomG X) (f : X -> NomG Y) Q Q' H :
    {{ H }} e {{ v; Q' v }} ->
    (∀ v, {{ Q' v }} f v {{ v'; Q v' }}) ->
    {{ H }} let! v := e in f v {{ v; Q v }}.
  Proof.
    iIntros; iNorm. iApply (wp_bind with "[HB]"). iApply (wp_consequence with "[HB]").
    iApply (H0 with "HB"). simpl. iIntros (v). iApply H1.
  Qed.

  Lemma frame_rule {X} H R Q (e : NomG X) :
    ({{ H }} e {{ v; Q v }}) ->
    {{ H ∗ R }} e {{ v; Q v ∗ R }}.
  Proof.
    iIntros; iNorm. iApply (wp_consequence with "[HB]").
    iApply (H0 with "HB"). iIntros. iFrame.
  Qed.

  Lemma frame_emp : forall X H (Q : X -> iProp) m,
      {{ emp ∗ H }} m {{ v; Q v }} ->
      {{ H }} m {{ v; Q v }}.
  Proof. intros. eapply consequence_rule. eapply H0. auto. auto. Qed.

  Lemma ret_rule : forall X H Q (v : X),
      (⊢ H -∗ Q v) -> {{ H }} ret v {{ v'; Q v' }}.
  Proof. intros; simpl; auto. Qed.

  Lemma fail_rule : forall X H Q,
      {{ H }} (fail : NomG X) {{ v; Q v }}.
  Proof. simpl; auto. Qed.

  Lemma length_rule :
    {{ emp }} length  {{ _; emp }}.
  Proof. simpl; auto. Qed.

  Lemma read_rule : forall s res,
      {{ emp }} read s res {{ _; emp }}.
  Proof. simpl; auto. Qed.

  Lemma take_rule : forall n,
      {{ emp }} take n {{ v; IsFresh v }}.
  Proof. simpl; auto. Qed.

  Lemma alt_rule : forall X e1 e2 H (Q : X -> iProp),
      {{ H }} e1 {{ v; Q v }} ->
      {{ H }} e2 {{ v; Q v }} ->
      {{ H }} alt e1 e2 {{ v; Q v }}.
  Proof.
    iIntros (X e1 e2 H Q He1 He2) "HA"; simpl; iNorm.
    iSplit.
    - iApply (He1 with "HA").
    - iApply (He2 with "HA").
  Qed.

  Lemma peek_rule : forall X (e : NomG X),
      {{ emp }} peek e {{ _; emp }}.
  Proof. simpl. auto. Qed.

  Lemma scope_rule : forall X e (Q : X -> iProp) s H,
      {{ H }} e {{ v; Q v }} ->
      {{ IsFresh s ∗ H }} scope s e {{ v; Q v }}.
  Proof.
    intros. iIntros "[HA HB]". simpl. iFrame. iApply (H0 with "HB").
  Qed.

  Lemma repeat_rule : forall X e (Q : X -> iProp),
      (forall res, {{ Q res }} e res {{ v ; Q v }}) ->
      forall n b, {{ Q b }} repeat n e b {{ v ; Q v }}.
  Proof.
    iIntros (X e Q Hrec n b) "HA". simpl. iExists Q. iSplitL; auto.
    iSplitL; auto. iModIntro. iIntros (res) "HA *". iApply Hrec. iApply "HA".
  Qed.

End wp.

Notation "'{{' P } } e {{ v ; Q } }" := (⊢  P -∗ wp e (fun v => Q) )
                                          (at level 20, format "'[hv' {{  P  } }  '/  ' e  '/'  {{ v ;  Q  } } ']'").

Ltac iBind := eapply bind_rule; [idtac | intro; idtac].
Ltac iRet := eapply ret_rule; eauto.


Ltac Frame := eapply frame_emp; eapply frame_rule.
Ltac Frame_emp rule :=
  eapply consequence_rule;
  [eapply frame_rule; eapply rule |
    iIntros "HA"; iSplitR "HA"; [eauto | iApply "HA"]  |
    eauto].

Ltac Frame_with rule :=
  eapply consequence_rule;
  [eapply frame_rule; apply rule | idtac | eauto].
