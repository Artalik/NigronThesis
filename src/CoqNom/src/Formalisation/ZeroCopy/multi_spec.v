From Formalisation Require Export ProgramLogic multi.

Section multi_spec.

  Context {atom : Type}.

  Definition NomG := @NomG atom.

  Lemma many0_rule X (e : NomG X) (Q : X -> iProp) :
    {{ emp }} e {{ v; Q v }} ->
    {{ emp }} many0 e {{ res; [∗ list] v ∈ []↓ res, Q v.2 }}.
  Proof.
    iIntros (He). unfold many0. eapply consequence_rule.
    eapply repeat_rule. 3 : eauto. intros.
    iBind. Frame. eapply length_rule.
    iBind. Frame. eapply He.
    iBind. Frame. eapply length_rule.
    destruct (v =? v1)%N.
    - eapply fail_rule.
    - iRet. iIntros. iNorm. edestruct add_vector_list.
      erewrite H. iFrame. auto.
    - auto.
  Qed.

  Lemma many1_rule X (e : NomG X) (Q : X -> iProp) :
    {{ emp }} e {{ v; Q v }} ->
    {{ emp }} many1 e {{ res; [∗ list] v ∈ []↓ res, Q v.2 }}.
  Proof.
    iIntros (He).
    iBind. Frame. eapply length_rule.
    iBind. Frame. eapply He.
    iBind. Frame. eapply length_rule.
    destruct (v =? v1)%N.
    - eapply fail_rule.
    - eapply consequence_rule. 3 : eauto. eapply repeat_rule. intros.
      iBind. Frame. eapply length_rule.
      iBind. Frame. eapply He.
      iBind. Frame. eapply length_rule.
      destruct (v2 =? v4)%N.
      + eapply fail_rule.
      + iRet. iIntros. iNorm. edestruct add_vector_list.
        erewrite H. iFrame. auto.
      + iIntros. iNorm. edestruct add_vector_list.
        erewrite H. iFrame. auto.
  Qed.

  Lemma many1_rule' X (e : NomG X) (Q : X -> iProp) : forall (Qres : VECTOR X -> iProp),
      {{ emp }} e {{ v; Q v }} ->
      (forall arr, ⊢ ([∗ list] v ∈ []↓arr, Q v.2) ∗-∗ Qres arr) ->
      {{ emp }} many1 e {{ res; Qres res }}.
  Proof.
    intros. iApply consequence_rule. iApply many1_rule. iApply H. auto.
    iIntros (v) "HA". iApply H0. iFrame.
  Qed.

  Lemma count_rule X (e : NomG X) (Q : X -> iProp) : forall n Qres,
      {{ emp }} e {{ v; Q v }} ->
      (forall arr, Qres arr ⊣⊢ [∗ list] v ∈ []↓arr, Q v.2) ->
      {{ emp }} count n e {{ v; Qres v }}.
  Proof.
    iIntros (n Qres He IH). unfold count. eapply consequence_rule.
    eapply repeat_rule. 3 : eauto. intros res. iBind. Frame. exact He. iRet.
    iIntros "[HA HB]". iApply IH. destruct res as [tab P].
    edestruct (add_vector_list X v) as [x EQ].
    erewrite EQ. iApply big_sepL_app. simpl. iFrame. iApply (IH with "HB").
    iIntros. iApply IH. auto.
  Qed.

  Lemma length_data_rule (e : NomG N) Q :
    {{ emp }} e {{ v; Q v }} ->
    {{ emp }} length_data e {{ v; <absorb> IsFresh v }}.
  Proof.
    intro. unfold length_data.
    iBind. eapply H. eapply consequence_rule. eapply frame_rule. eapply take_rule.
    iIntros "HA". iSplitR; eauto. iApply "HA".
    intros. iIntros. iNorm.
  Qed.

End multi_spec.
