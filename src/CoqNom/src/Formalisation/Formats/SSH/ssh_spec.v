From Formalisation Require Import ssh.
From Formalisation Require Import ProgramLogic tactics combinator adequacy multi_spec.
From Classes Require Import Foldable.

Lemma rule_parse_string :
  {{ emp }} parse_string  {{v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_string.
  eapply consequence_rule. eapply length_data_rule. WpTac.
  iIntros "HA". instantiate (1 := fun _ => <absorb> emp). iApply "HA". auto.
  iIntros. unfold all_disjointMSL, all_disjointSL. simpl. iNorm.
Qed.

Lemma rule_parse_packet_dh_reply :
  {{ emp }} parse_packet_dh_reply  {{v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_packet_dh_reply.
  WpTac.
  eapply rule_parse_string.
  Frame. eapply rule_parse_string.
  Frame. eapply rule_parse_string.
  iIntros. iNorm. iModIntro. unfold all_disjointMSL, all_disjointSL. simpl. iNorm.
  iFrame.
Qed.

Lemma rule_parse_packet_dh_init :
  {{ emp }} parse_packet_dh_init {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_packet_dh_init.
  WpTac.
  eapply rule_parse_string.
Qed.

Lemma rule_parse_packet_key_exchange :
  {{ emp }} parse_packet_key_exchange {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_packet_key_exchange.
  WpTac.
  1 - 10 : Frame; eapply rule_parse_string.
  iIntros. unfold all_disjointMSL, all_disjointSL. simpl. iNorm. iFrame.
Qed.

Lemma rule_parse_packet_debug :
  {{ emp }} parse_packet_debug {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_packet_debug.
  WpTac.
  1-2 : Frame; eapply rule_parse_string.
  iIntros. unfold all_disjointMSL, all_disjointSL. simpl. iNorm. iFrame.
Qed.

Lemma rule_parse_packet_disconnect :
  {{ emp }} parse_packet_disconnect {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_packet_disconnect.
  WpTac.
  1-2 : Frame; eapply rule_parse_string.
  iIntros. unfold all_disjointMSL, all_disjointSL. simpl. iNorm. iFrame.
Qed.

Lemma rule_parse_ssh_packet :
  {{ emp }} parse_ssh_packet
  {{ v; <absorb> @all_disjointMSL _ (Pair_Foldable _ _ _ _) v }}.
Proof.
  unfold parse_ssh_packet.
  WpTac.
  Frame. eapply rule_parse_packet_dh_reply.
  simpl. iIntros. unfold all_disjointMSL, all_disjointSL. simpl. iNorm.
  Frame. eapply rule_parse_string.
  simpl. iIntros. unfold all_disjointMSL, all_disjointSL. simpl. iNorm.
  Frame. eapply rule_parse_packet_dh_init.
  Frame. eapply rule_parse_string.
  Frame. eapply rule_parse_packet_key_exchange.
  Frame. eapply rule_parse_packet_debug.
  Frame. eapply rule_parse_string.
  Frame. eapply rule_parse_packet_disconnect.
  iIntros. iNorm. iFrame. auto.
Qed.
