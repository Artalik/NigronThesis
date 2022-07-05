From Formalisation Require Export ProgramLogic combinator.

Section combinator_spec.

  Context {atom : Type}.


  Definition NomG := @NomG atom.

  Variable X : Type.
  Variable e : NomG X.

  Lemma recognize_rule : {{ emp }} recognize e {{ s; IsFresh s }}.
  Proof.
    intros. iBind. eapply length_rule. iBind. eapply peek_rule. eapply take_rule.
  Qed.

  Lemma consumed_rule : {{ emp }} consumed e {{ s; IsFresh s.1 }}.
  Proof.
    intros. iBind. eapply length_rule.
    iBind. eapply peek_rule.
    iBind. eapply take_rule.
    iRet.
  Qed.

  Lemma rest_rule : {{ emp }} (rest : NomG span) {{ v; IsFresh v }}.
  Proof. iBind. eapply length_rule. eapply take_rule. Qed.

  Lemma map_parser_rule : forall (es : NomG span) H (Q : X -> iProp) R,
      {{ H }} es {{ v; IsFresh v ∗ R }} ->
      {{ R }} e {{ v; Q v }} ->
      {{ H }} map_parser es e {{ v; Q v }}.
  Proof.
    intros. iBind. eapply H0. iIntros "[HA HB]".
    iApply scope_rule. eapply H1. iFrame.
  Qed.

  Lemma verify_rule : forall cond H (Q : X -> iProp),
      {{ H }} e {{ v; Q v }} ->
      {{ H }} verify e cond {{ v; Q v ∗ ⌜Is_true (cond v)⌝ }}.
  Proof.
    intros. iBind.
    eapply H0.
    destruct (cond v) eqn:?.
    - iRet.
    - apply fail_rule.
  Qed.

  Lemma map_rule : forall Y (f : X -> Y) H Q,
      {{ H }} e {{ v; Q (f v) }} ->
      {{ H }} map e f {{ v; Q v }}.
  Proof. intros. iBind. eapply H0. iRet. Qed.

  Lemma cond_rule : forall b (H : iProp) (Q : option X -> iProp),
      {{ H }} e {{ v; Q (Some v) }} ->
      (H ⊢ Q None) ->
      {{ H }} cond b e {{ v; Q v }}.
  Proof.
    intros. destruct b; simpl cond.
    - iBind. eapply H0. eauto.
    - iApply H1.
  Qed.

End combinator_spec.
