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
  WpTac; simpl; iIntros.
  - instantiate (1 := fun _ => True). eauto.
  - instantiate (1 := fun _ => True). eauto.
  - unfold all_disjointMSL. simpl. iNorm.
Qed.

Lemma parse_ikev2_payload_generic_rule :
  {{ emp }} parse_ikev2_payload_generic {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_payload_generic. iBind. eapply map_rule. instantiate (1 := fun _ => True).
  eapply u8_rule. iBind. Frame. eapply u8_rule. WpTac.
  unfold all_disjointMSL, all_disjointSL. iIntros. simpl. iNorm.
Qed.

Lemma parse_ikev2_transform_rule :
  {{ emp }} parse_ikev2_transform {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_transform, all_disjointMSL, all_disjointSL.
  WpTac; simpl; iIntros; iNorm; simpl; eauto. iFrame.
Qed.

Lemma foldr_cons : forall X l1 l2,
    list.foldr (λ (a : X) (b : list X), a :: b) l1 l2 = l2 ++ l1.
Proof.
  induction l2; simpl; intros; eauto.
  f_equal. rewrite IHl2. reflexivity.
Qed.

Lemma parse_ikev2_proposal_rule :
  {{ emp }} parse_ikev2_proposal {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_proposal.
  WpTac.
  4 : eapply parse_ikev2_transform_rule.
  all : simpl; iIntros.
  - instantiate (1 := fun _ => True). eauto.
  - instantiate (1 := fun v => <absorb> Some_span v). simpl. iNorm.
  - simpl. eauto.
  - auto.
  - simpl. unfold all_disjointMSL, all_disjointSL. simpl. iNorm.
    iDestruct (big_sepL_absorb_out with "HB") as ">HB".
    iDestruct (big_sepL_double with "HB") as "HB".
    iModIntro. destruct v7; simpl; iNorm. iFrame.
Qed.

Lemma parse_ikev2_payload_sa_rule : forall len,
    {{ emp }} @parse_ikev2_payload_sa len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intro. unfold parse_ikev2_payload_sa.
  WpTac.
  - eapply parse_ikev2_proposal_rule.
  - unfold all_disjointMSL, all_disjointSL.
    iIntros (v) "[HA _]".
    iDestruct (big_sepL_absorb_out with "HA") as ">HA".
    iDestruct (big_sepL_double with "HA") as "HA". simpl.
    iFrame.
Qed.

Lemma parse_ikev2_payload_kex_rule : forall len,
    {{ emp }} parse_ikev2_payload_kex len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intro. unfold parse_ikev2_payload_kex. destruct (val len <? 4). WpTac.
  iBind. eapply map_rule. instantiate (1 := fun _ => True). WpTac. WpTac.
  iIntros. iNorm. unfold all_disjointMSL. iFrame. eauto.
Qed.

Lemma parse_ikev2_payload_ident_init_rule : forall len,
    {{ emp }} parse_ikev2_payload_ident_init len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_ident_init. destruct (val len <? 4). WpTac.
  iBind. eapply map_rule. instantiate (1 := fun _ => True). WpTac. WpTac.
  iIntros. iNorm. unfold all_disjointMSL. iFrame. eauto.
Qed.

Lemma parse_ikev2_payload_ident_resp_rule : forall len,
    {{ emp }} parse_ikev2_payload_ident_resp len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intro. unfold parse_ikev2_payload_ident_resp. destruct (val len <? 4). WpTac.
  iBind. eapply map_rule. instantiate (1 := fun _ => True). WpTac. WpTac.
  iIntros. iNorm. unfold all_disjointMSL. iFrame. eauto.
Qed.

Lemma parse_ikev2_payload_certificate_rule : forall len,
    {{ emp }} parse_ikev2_payload_certificate len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_certificate. destruct (val len <? 1). WpTac.
  iBind. eapply map_rule. instantiate (1 := fun _ => True). WpTac. WpTac.
  iIntros. iNorm. unfold all_disjointMSL. iFrame. eauto.
Qed.

Lemma parse_ikev2_payload_certificate_request_rule : forall len,
    {{ emp }} parse_ikev2_payload_certificate_request len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_certificate_request. destruct (val len <? 1). WpTac.
  iBind. eapply map_rule. instantiate (1 := fun _ => True). WpTac. WpTac.
  iIntros. iNorm. unfold all_disjointMSL. iFrame. eauto.
Qed.

Lemma parse_ikev2_payload_authentication_rule : forall len,
    {{ emp }} parse_ikev2_payload_authentication len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_authentication. destruct (val len <? 4). WpTac.
  iBind. eapply map_rule. instantiate (1 := fun _ => True). WpTac. WpTac.
  iIntros. iNorm. unfold all_disjointMSL. iFrame. eauto.
Qed.

Lemma parse_ikev2_payload_nonce_rule : forall len,
    {{ emp }} parse_ikev2_payload_nonce len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_nonce.
  WpTac. iIntros. unfold all_disjointMSL. iFrame. eauto.
Qed.


Lemma parse_ikev2_payload_notify_rule : forall len,
    {{ emp }} parse_ikev2_payload_notify len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_notify.
  iBind. eapply map_rule. instantiate (1 := fun _ => True). WpTac. WpTac.
  - instantiate (1 := fun _ => True). eauto.
  - instantiate (1 := fun v => <absorb> Some_span v). iIntros. iNorm.
  - eauto.
  - instantiate (1 := fun v => <absorb> Some_span v ∗ Some_span v2). iIntros. iNorm. iFrame.
  - iIntros. iNorm.
  - iIntros. iNorm. unfold all_disjointMSL, all_disjointSL. simpl.
    iModIntro. simpl. destruct v2, v3; iFrame; auto.
Qed.

Lemma parse_ikev2_payload_vendor_rule : forall len,
    {{ emp }} parse_ikev2_payload_vendor_id len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_vendor_id.
  WpTac; eauto. unfold all_disjointMSL, all_disjointSL. simpl. iIntros. iNorm.
Qed.

Lemma parse_ikev2_payload_delete_rule : forall len,
    {{ emp }} parse_ikev2_payload_delete len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_delete. destruct (val len <? 8). WpTac.
  iBind. eapply map_rule. instantiate (1 := fun _ => True). WpTac. WpTac.
  iIntros. unfold all_disjointMSL, all_disjointSL. simpl. iNorm.
Qed.

Lemma parse_ts_addr_rule : forall t,
    {{ emp }} parse_ts_addr t {{ v; IsFresh v }}.
Proof. intro. unfold parse_ts_addr. WpTac. Qed.

Lemma parse_ikev2_ts_rule :
  {{ emp }} parse_ikev2_ts {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_ts.
  iBind. eapply map_rule. instantiate (1 := fun _ => True). WpTac. WpTac.
  - Frame. eapply parse_ts_addr_rule.
  - Frame. eapply parse_ts_addr_rule.
  - iIntros. iNorm. iFrame. eauto.
Qed.

Lemma parse_ikev2_payload_ts_rule : forall len,
    {{ emp }} @parse_ikev2_payload_ts len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intro. unfold parse_ikev2_payload_ts. WpTac.
  - eapply parse_ikev2_ts_rule.
  - iIntros. iNorm. unfold all_disjointMSL, all_disjointSL.
    iDestruct (big_sepL_absorb_out with "HB") as ">HB".
    iDestruct (big_sepL_double with "HB") as "HB".
    iFrame. auto.
Qed.

Lemma parse_ikev2_payload_ts_init_rule : forall len,
    {{ emp }} @parse_ikev2_payload_ts_init len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_payload_ts_init. intros.
  WpTac; eauto. eapply parse_ikev2_payload_ts_rule.
Qed.

Lemma parse_ikev2_payload_ts_resp_rule : forall len,
    {{ emp }} @parse_ikev2_payload_ts_resp len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_payload_ts_resp. intros.
  WpTac; eauto.
  eapply parse_ikev2_payload_ts_rule.
Qed.

Lemma parse_ikev2_payload_encrypted_rule : forall len,
    {{ emp }} parse_ikev2_payload_encrypted len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_payload_encrypted. intros.
  WpTac; eauto.
Qed.

Lemma parse_ikev2_payload_unknown_rule : forall len,
    {{ emp }} parse_ikev2_payload_unknown len {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_ikev2_payload_unknown. intros.
  WpTac; eauto.
Qed.

Lemma parse_ikev2_payload_with_type_rule : forall len t,
    {{ emp }} @parse_ikev2_payload_with_type len t {{ v; <absorb> all_disjointMSL v }}.
Proof.
  intros. unfold parse_ikev2_payload_with_type. WpTac.
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

Lemma all_disjointMSL_vector `{Foldable V} : forall (acc : VECTOR (V span)) (v : V span),
    all_disjointMSL v ∗ all_disjointMSL acc ⊢ all_disjointMSL (add acc v).
Proof.
  intros acc. destruct acc as [[cap size] VEC]. revert cap size VEC.
  induction values; simpl; intros.
  - iIntros. iNorm. unfold all_disjointMSL, all_disjointSL.
    simpl. destruct H. simpl. edestruct add_vector_list.
    erewrite H. simpl. iFrame. auto.
  - iIntros. iNorm. unfold all_disjointMSL, all_disjointSL.
    simpl. destruct H. simpl. edestruct add_vector_list.
    erewrite H. simpl. rewrite foldr_app. simpl.
    iDestruct "HC" as "[HC HD]". iFrame. simpl_list.
    iDestruct (IHvalues with "[HB HD]") as "HB". iFrame.
    unfold all_disjointMSL, all_disjointSL. simpl.
    edestruct add_vector_list. erewrite H0. simpl.
    rewrite foldr_app.
    simpl. simpl_list. iApply "HB".
    Unshelve.
    3 : { constructor. simpl. reflexivity.
          simpl. reflexivity. }
Qed.

Lemma parse_ikev2_payload_list_fold_rule : forall acc p,
    {{ IsFresh (payloadGen p) ∗
       <absorb> all_disjointMSL acc }}
      parse_ikev2_payload_list_fold acc p
      {{ res; <absorb> all_disjointMSL res }}.
Proof.
  intros. rewrite parse_ikev2_payload_list_fold_equation_1. WpTac.
  eapply consequence_rule. apply scope_rule. WpTac.
  Frame. eapply parse_ikev2_payload_with_type_rule.
  all : eauto. simpl. iIntros. iNorm.
  iModIntro.
  iApply (all_disjointMSL_vector acc). iFrame.
Qed.


Lemma parse_ikev2_payload_list_rule : forall init,
    {{ emp }}
      parse_ikev2_payload_list init
      {{ res; <absorb> all_disjointMSL res }}.
Proof.
  intros. rewrite parse_ikev2_payload_list_equation_1.
  eapply consequence_rule. eapply repeat_rule.
  intros res. WpTac. Frame. eapply parse_ikev2_payload_generic_rule.
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
  WpTac. eapply parse_ikev2_header_rule.
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
