From Formalisation Require Import Nom ikev2_notify ikev2 ikev2_parser ikev2_transforms.
From Formalisation Require Import ProgramLogic IsFresh tactics adequacy.

Open Scope N_scope.

Notation "'Some_span' res" := (match res with
                               | Some v => IsFresh v
                               | _ => emp
                               end)(at level 20).

Lemma parse_ikev2_header_rule :
  {{ emp }} parse_ikev2_header {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_header.
  repeat WpTac.
  iIntros. iNorm.
Qed.

Lemma bits_split_1_rule :
  {{ emp }} bits_split_1 {{ v; True }}.
Proof.
  unfold bits_split_1. repeat WpTac. auto.
Qed.

Lemma parse_ikev2_payload_generic_rule :
  {{ emp }} parse_ikev2_payload_generic {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_payload_generic.
  repeat WpTac.
  - Frame_emp bits_split_1_rule.
  - unfold all_disjointMSL, all_disjointSL. iIntros. simpl. iNorm.
Qed.

Lemma parse_ikev2_transform_rule :
  {{ emp }} parse_ikev2_transform {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_transform, all_disjointMSL, all_disjointSL.
  repeat WpTac; iIntros; iNorm; eauto. iFrame. auto.
Qed.

Lemma parse_ikev2_proposal_rule :
  {{ emp }} parse_ikev2_proposal {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_proposal.
  repeat WpTac.
  3 : eapply parse_ikev2_transform_rule.
  all : simpl; iIntros.
  - instantiate (1 := fun v => <absorb> Some_span v). simpl. iNorm.
  - simpl. iNorm.
  - eauto.
  - simpl. unfold all_disjointMSL, all_disjointSL. simpl. iNorm.
    iDestruct (big_sepL_absorb_out with "HB") as ">HB".
    iDestruct (big_sepL_double with "HB") as "HB".
    iModIntro. destruct v7; simpl; iNorm. iFrame.
Qed.

Lemma parse_ikev2_payload_sa_rule : forall len,
    {{ emp }} @parse_ikev2_payload_sa len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intro. unfold parse_ikev2_payload_sa.
  repeat WpTac.
  - eapply parse_ikev2_proposal_rule.
  - iIntros "HA".
    iDestruct (big_sepL_absorb_out with "HA") as ">HA".
    iDestruct (big_sepL_double with "HA") as "HA". simpl.
    iFrame.
Qed.

Lemma parse_ikev2_payload_kex_rule : forall len,
    {{ emp }} parse_ikev2_payload_kex len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intro. unfold parse_ikev2_payload_kex.
  repeat WpTac.
  iIntros. iNorm. iFrame. eauto.
Qed.

Lemma parse_ikev2_payload_ident_init_rule : forall len,
    {{ emp }} parse_ikev2_payload_ident_init len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_ident_init.
  repeat WpTac.
  iIntros. iNorm. iFrame. eauto.
Qed.

Lemma parse_ikev2_payload_ident_resp_rule : forall len,
    {{ emp }} parse_ikev2_payload_ident_resp len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intro. unfold parse_ikev2_payload_ident_resp.
  repeat WpTac.
  iIntros. iNorm. iFrame. eauto.
Qed.

Lemma parse_ikev2_payload_certificate_rule : forall len,
    {{ emp }} parse_ikev2_payload_certificate len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_certificate.
  repeat WpTac.
  iIntros. iNorm. iFrame. eauto.
Qed.

Lemma parse_ikev2_payload_certificate_request_rule : forall len,
    {{ emp }} parse_ikev2_payload_certificate_request len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_certificate_request.
  repeat WpTac.
  iIntros. iNorm. iFrame. auto.
Qed.

Lemma parse_ikev2_payload_authentication_rule : forall len,
    {{ emp }} parse_ikev2_payload_authentication len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_authentication.
  repeat WpTac.
  iIntros. iNorm. iFrame. auto.
Qed.

Lemma parse_ikev2_payload_nonce_rule : forall len,
    {{ emp }} parse_ikev2_payload_nonce len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_nonce.
  repeat WpTac.
  iIntros. iFrame. auto.
Qed.


Lemma parse_ikev2_payload_notify_rule : forall len,
    {{ emp }} parse_ikev2_payload_notify len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_notify. repeat WpTac.
  - instantiate (1 := fun v => <absorb> Some_span v). iIntros. iNorm.
  - eauto.
  - instantiate (1 := fun v => <absorb> Some_span v ∗ Some_span v2). iIntros. iNorm. iFrame.
  - iIntros. iNorm.
  - iIntros. iNorm. iModIntro.
    destruct v2, v3; iFrame; auto. iFrame. auto.
Qed.

Lemma parse_ikev2_payload_vendor_rule : forall len,
    {{ emp }} parse_ikev2_payload_vendor_id len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_vendor_id.
  repeat WpTac.
  iIntros. iFrame. auto.
Qed.

Lemma parse_ikev2_payload_delete_rule : forall len,
    {{ emp }} parse_ikev2_payload_delete len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_delete.
  repeat WpTac.
  iIntros. iNorm. iFrame. auto.
Qed.

Lemma parse_ts_addr_rule : forall t,
    {{ emp }} parse_ts_addr t {{ v; IsFresh v }}.
Proof. intro. unfold parse_ts_addr. repeat WpTac. Qed.

Lemma parse_ikev2_ts_rule :
  {{ emp }} parse_ikev2_ts {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_ts. repeat WpTac.
  - Frame_emp parse_ts_addr_rule.
  - Frame_emp parse_ts_addr_rule.
  - iIntros. iNorm. iFrame. auto.
Qed.

Lemma parse_ikev2_payload_ts_rule : forall len,
    {{ emp }} @parse_ikev2_payload_ts len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intro. unfold parse_ikev2_payload_ts. repeat WpTac.
  - eapply parse_ikev2_ts_rule.
  - iIntros. iNorm.
    iDestruct (big_sepL_absorb_out with "HB") as ">HB".
    iDestruct (big_sepL_double with "HB") as "HB".
    iFrame. auto.
Qed.

Lemma parse_ikev2_payload_ts_init_rule : forall len,
    {{ emp }} @parse_ikev2_payload_ts_init len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_payload_ts_init. intros.
  repeat WpTac. eapply parse_ikev2_payload_ts_rule. auto.
Qed.

Lemma parse_ikev2_payload_ts_resp_rule : forall len,
    {{ emp }} @parse_ikev2_payload_ts_resp len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_payload_ts_resp. intros. repeat WpTac.
  eapply parse_ikev2_payload_ts_rule. auto.
Qed.

Lemma parse_ikev2_payload_encrypted_rule : forall len,
    {{ emp }} parse_ikev2_payload_encrypted len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_payload_encrypted. intro.
  repeat WpTac.
  iIntros. iFrame. auto.
Qed.

Lemma parse_ikev2_payload_unknown_rule : forall len,
    {{ emp }} parse_ikev2_payload_unknown len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_payload_unknown. intros.
  repeat WpTac.
  iIntros. iFrame. auto.
Qed.

Lemma parse_ikev2_payload_with_type_rule : forall len t,
    {{ emp }} @parse_ikev2_payload_with_type len t {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_with_type. repeat WpTac.
  all : try eapply parse_ikev2_payload_unknown_rule.
  - eapply parse_ikev2_payload_authentication_rule.
  - eapply parse_ikev2_payload_vendor_rule.
  - eapply parse_ikev2_payload_ident_init_rule.
  - eapply parse_ikev2_payload_ts_resp_rule.
  - eapply parse_ikev2_payload_certificate_rule.
  - eapply parse_ikev2_payload_notify_rule.
  - eapply parse_ikev2_payload_sa_rule.
  - eapply parse_ikev2_payload_certificate_request_rule.
  - apply parse_ikev2_payload_delete_rule.
  - eapply parse_ikev2_payload_kex_rule.
  - eapply parse_ikev2_payload_ts_init_rule.
  - eapply parse_ikev2_payload_ident_resp_rule.
    Unshelve. all : eauto.
Qed.

Lemma parse_ikev2_payload_list_fold_rule : forall acc p,
    {{ IsFresh (payloadGen p) ∗
       <absorb> all_disjointMSL acc }}
      parse_ikev2_payload_list_fold acc p
      {{ res; <absorb> all_disjointMSL res }}.
Proof.
  intros. rewrite parse_ikev2_payload_list_fold_equation_1.
  repeat WpTac.
  eapply consequence_rule. apply scope_rule. repeat WpTac.
  Frame_emp parse_ikev2_payload_with_type_rule.
  all : eauto. simpl. iIntros. iNorm.
  iModIntro. iApply (all_disjointMSL_vector acc). iFrame.
Qed.


Lemma parse_ikev2_payload_list_rule : forall init,
    {{ emp }}
      parse_ikev2_payload_list init
      {{ res; <absorb> all_disjointMSL res }}.
Proof.
  intros. rewrite parse_ikev2_payload_list_equation_1.
  eapply consequence_rule. eapply repeat_rule.
  intros res. repeat WpTac. Frame_emp parse_ikev2_payload_generic_rule.
  eapply consequence_rule. eapply parse_ikev2_payload_list_fold_rule.
  - iIntros "[>HA [_ HC]]". iSplitL "HA".
    unfold all_disjointMSL, all_disjointSL. simpl. iNorm.
    iApply "HC".
  - iIntros. iFrame.
  - auto.
  - auto.
Qed.

Lemma parse_ikev2_message_rule :
  {{ emp }} parse_ikev2_message {{ res; <absorb> all_disjointMSL res }}.
Proof.
  unfold parse_ikev2_message.
  repeat WpTac. eapply parse_ikev2_header_rule.
  Frame. eapply parse_ikev2_payload_list_rule. simpl.
  iIntros. iNorm.
Qed.

Lemma parse_ikev2_message_rule_pure :
    {{ emp }} parse_ikev2_message {{ res; ⌜ all_disjointM res ⌝}}.
Proof.
  intros.
  eapply consequence_rule.
  - eapply parse_ikev2_message_rule.
  - eauto.
  - iIntros (v) ">HA". iApply (all_disjointM_SL_to_Prop with "HA").
Qed.

Lemma parse_ikev2_specification : forall nb_iter_max a data,
    parse_ikev2 nb_iter_max a = Some data -> all_disjointM data.
Proof.
  intros nb_iter_max a data EQ.
  eapply adequacy_pure.
  eapply parse_ikev2_message_rule_pure.
  eapply EQ.
Qed.

Close Scope N_scope.
