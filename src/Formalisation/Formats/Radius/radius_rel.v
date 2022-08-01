From Formalisation Require Import SizeNat Nom IpAddr radius_attr_rel radius.
From Raffinement Require Import PHOAS RelNomPHOAS.


Definition radius_data : type :=
  Pair (Pair (Pair (Pair (NatN 8) (NatN 8)) (NatN 16)) Span) (Option (Vector attribute)).

Definition radius_data_spec (rad : RadiusData) (r : type_to_Type radius_data) :=
  code rad = mk_code r.1.1.1.1 /\
    identifier rad = r.1.1.1.2 /\
    length rad = r.1.1.2 /\
    authenticator rad = r.1.2 /\
    match attributes rad, r.2 with
    | None, None => True
    | Some vx, Some vy =>
        VECTOR_spec attribute_rel vx vy
    | _,_ => False%type
    end.

Definition parse_radius_data_rel :
  {code | forall data vs, adequate (fun _ => radius_data_spec) parse_radius_data code data vs}.
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
  simpl in *. repeat clean_up. be_spec_clean. subst.
  eapply (ret_adequate _ _ _ (EBin EPair (EBin EPair (EBin EPair (EBin EPair (Var vres) (Var vres0)) (Var vres1)) (Var vres2)) (Var vres3)));
    repeat econstructor; eauto.
  simpl. destruct r3; eauto. destruct (sem_val vres3); eauto.
Defined.

Lemma parse_radius_data_adequate : forall data vs,
    adequate (fun _ => radius_data_spec) parse_radius_data (proj1_sig parse_radius_data_rel) data vs.
Proof. intros. destruct parse_radius_data_rel. eauto. Qed.
