From Formalisation Require Import SizeNat Nom IpAddr radius_attr_rel_C radius.
From Raffinement Require Import PHOAS RelNomPHOAS.

Definition parse_radius_data_rel :
  {code : PHOAS (Unknown "radius_data") |
    forall data vs, adequate (fun _ _ _ => True%type) parse_radius_data code data vs}.
  eapply exist. intros. unfold parse_radius_data.
  repeat step.
  eapply bind_adequate. eapply be_u8_adequate. intros. be_spec_clean. subst.
  eapply (ret_adequate _ _ _ (Var vres)); repeat econstructor; eauto.
  instantiate (1 := fun _ x y => x = mk_code y). simpl. eauto.
  eapply be_u8_adequate.
  eapply be_u16_adequate.
  unfold sizeu16. step.
  eapply (cond_adequate (EBin ELt (Const (ENat 20)) (EUna EVal (Var vres1))));
    repeat econstructor; eauto; repeat clean_up; be_spec_clean; subst.
  auto.
  intro. eapply map_parser_adequate. eapply consequence_adequate. step.
  intros. repeat clean_up. split; auto.
  intros. eapply many1_adequate.
  intros. eapply parse_radius_attribute_adequate.
  simpl in *. repeat clean_up. subst.
  eapply (cstruct_adequate "radius_data" "create_RadiusData"
            (CONS (Var vres)
               (CONS (Var vres0)
                  (CONS (Var vres1)
                     (CONS (Var vres2)
                        (CONS (Var vres3) NIL)))))).
Defined.

Lemma parse_radius_data_adequate : forall data vs,
    adequate (fun _ _ _ => True%type) parse_radius_data (`parse_radius_data_rel) data vs.
Proof. intros. destruct parse_radius_data_rel. eauto. Qed.

Definition equiv_parse_radius_data_rel {var} :
  {code : @PHOAS var _ | equiv_prog Nil _ (`parse_radius_data_rel) code}.
  eapply exist. simpl. repeat econstructor.
Defined.
