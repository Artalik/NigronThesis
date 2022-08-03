From Formalisation Require Export ProgramLogic bin_combinators.

Lemma u8_rule :
  {{ emp }} be_u8 {{ _; True }}.
Proof.
  iBind. apply take_rule. eapply consequence_rule. Frame. eapply read_rule.
  all : eauto.
Qed.

Lemma u16_rule :
  {{ emp }} be_u16 {{ _; <absorb> emp }}.
Proof. iBind. apply u8_rule. iBind. Frame. apply u8_rule. iRet. Qed.

Lemma u32_rule :
  {{ emp }} be_u32 {{ _; <absorb> emp }}.
Proof. iBind. apply u16_rule. iBind. Frame. apply u16_rule. iRet. Qed.

Lemma u64_rule :
  {{ emp }} be_u64 {{ _; <absorb> emp }}.
Proof. iBind. apply u32_rule. iBind. Frame. apply u32_rule. iRet. Qed.

Lemma get_ipv4_rule :
  {{ emp }} get_ipv4 {{ _; <absorb> emp }}.
Proof.
  unfold get_ipv4. repeat (iBind; [Frame; eapply u8_rule | idtac]). iRet.
Qed.

Lemma get_ipv6_rule :
  {{ emp }} get_ipv6 {{ _; <absorb> emp }}.
Proof.
  unfold get_ipv6. repeat (iBind; [Frame; eapply u16_rule | idtac]). iRet.
Qed.
