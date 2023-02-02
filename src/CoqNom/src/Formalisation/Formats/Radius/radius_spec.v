From Formalisation Require Import radius radius_attr radius_attr_spec.
From Formalisation Require Import ProgramLogic tactics combinator adequacy ZeroCopy Nom_ZeroCopy.

Lemma parse_radius_data_spec :
  {{ emp }} parse_radius_data {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_radius_data.
  repeat WpTac; eauto.
  - iIntros "HA". instantiate (1 := (fun _ => True)). iApply "HA".
  - eapply parse_radius_attribute_spec.
  - iIntros. iNorm. iFrame. simpl.
    iDestruct (big_sepL_absorb_out with "HB") as ">HB".
    iModIntro. iFrame.
    unfold all_disjointMSL, all_disjointSL.
    iDestruct (big_sepL_double with "HB") as "HB".
    erewrite foldr_ext. iApply "HB".
    simpl. intros. all : reflexivity.
  - iIntros. iNorm. iFrame. eauto.
Qed.

Lemma parse_radius_data_spec_pure :
  {{ emp }} parse_radius_data {{ v; ⌜all_disjointM v⌝ }}.
Proof.
  eapply consequence_rule. eapply parse_radius_data_spec.
  eauto. iIntros (v) ">HA".
  iApply (all_disjointM_SL_to_Prop with "HA").
Qed.

Lemma parse_radius_specification : forall nb_attrib_max data res,
    parse_radius nb_attrib_max data = Some res -> all_disjointM res.
Proof.
  intros nb_attrib_max data res PARSE.
  eapply adequacy_pure.
  eapply parse_radius_data_spec_pure.
  eapply PARSE.
Qed.

Lemma parse_radius_Safe : parse_Safe parse_radius_data.
Proof.
  eapply parse_is_Safe.
  eapply parse_radius_data_spec.
Qed.
