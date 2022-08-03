From Formalisation Require Import ProgramLogic radius_attr tactics.

Lemma parse_attribute_content_spec : forall n,
    {{ emp }} parse_attribute_content n {{ v; <absorb> all_disjointMSL v }}.
Proof.
  destruct n. unfold parse_attribute_content, all_disjointMSL, all_disjointSL.
  WpTac; iIntros; iNorm; simpl; eauto.
Qed.

Lemma parse_radius_attribute_spec :
    {{ emp }} parse_radius_attribute {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_radius_attribute, all_disjointMSL, all_disjointSL.
  WpTac. Frame_emp parse_attribute_content_spec. iIntros. iNorm.
Qed.
