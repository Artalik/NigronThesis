From Formalisation Require Import radius radius_attr radius_attr_spec.
From Formalisation Require Import ProgramLogic tactics combinator adequacy.

Lemma parse_radius_data_spec :
  {{ emp }} parse_radius_data {{ v; <absorb> all_disjointMSL v }}.
Proof.
  unfold parse_radius_data.
  WpTac; try eapply parse_radius_attribute_spec; eauto.
  - iIntros (v) "HA". instantiate (1 := (fun _ => True)). simpl. eauto.
  - iIntros. iNorm. iFrame. simpl.
    iDestruct (big_sepL_absorb_out with "HB") as ">HB".
    iModIntro. destruct v3. destruct x. unfold Vector.vector_to_list. simpl.
    unfold all_disjointMSL, all_disjointSL.
    iDestruct (big_sepL_double with "HB") as "HB".
    erewrite foldr_ext. iApply "HB".
    simpl. intros. destruct (b.2) eqn:P; rewrite P; reflexivity.
    reflexivity. reflexivity.
  - iIntros. iNorm. iFrame. simpl. eauto.
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
