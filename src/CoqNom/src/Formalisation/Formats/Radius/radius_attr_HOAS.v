Require Import Ascii Vector.
From FreeMonad Require Import SizeNat Nom HOAS IpAddr radius_attr.
From Classes Require Import Foldable.
Require Import BinNums.
Import BinNat.
(* https://github.com/rusticata/radius-parser/blob/master/src/radius_attr.rs *)
Open Scope N_scope.


(* Attributes *)

Definition size4u : HOAS N := ret (VNat 4).
Import HOAS.

Definition parse_attribute_content : Expr (nat8 -> RadiusAttribute) :=
  Lam (fun (t : val nat8) => switch (↓ t) >>
         case 1 => let! i := rest in ret (UserName i) in
         case 2 => let! i := rest in ret (UserName i) in
         case 3 => let! len := length in
                  If len << (VNat 2)
                  Then
                    fail
                  Else
                  let! v := get_v (VNat 1) in
                  let! i := rest in
                  ret (ChapPassword (VHD v) i) in
      case 4 => let! v := size4u in
               map_parser (take v) (let! v := get_v (VNat 4) in ret (NasIPAddress v)) in
      case 5 => map be_u32 (fun v => ret (NasPort v)) in
      case 6 => map be_u32 (fun v => let! serv := ret (mk_service v) in
                                 ret (Service serv)) in
      case 7 => map be_u32 (fun v => let! prot := ret (mk_protocol v) in
                                 ret (Protocol prot)) in
      case 8 => let! v := size4u in
               map_parser (take v) (let! v := get_v (VNat 4) in ret (FramedIPAddress v)) in
      case 9 => let! v := size4u in
               map_parser (take v) (let! v := get_v (VNat 4) in ret (FramedIPNetmask v)) in
      case 10 => map be_u32 (fun v => let! rout := ret (mk_routing v) in
                                  ret (Routing rout)) in
      case 11 => let! i := rest in ret (FilterId i) in
      case 12 => map be_u32 (fun v => ret (FramedMTU v)) in
      case 13 => map be_u32 (fun v => let! compr := ret (mk_compression v) in
                                  ret (Compression compr)) in
      case 26 => let! len := length in
                If len << VNat 5
                Then
                  fail
                Else
                let! vendorid := be_u32 in
                let! vendordata := rest in
                ret (VendorSpecific vendorid vendordata) in
      case 30 => let! i := rest in
                ret (CalledStationId i) in
      case 31 => let! i := rest in
                ret (CallingStationId i) in
      default => let! i := rest in
                ret (Unknown t i)).

Definition parse_radius_attribute : HOAS RadiusAttribute :=
  let! t := be_u8 in
  let! l := verify be_u8 (fun n => VNat 2 <<= ↓ n) in
  map_parser (take (↓ l  -! VNat 2)) (App parse_attribute_content (ret t)).

(* From FreeMonad Require Import RelNomHOAS radius_attr. *)

(* Lemma adequate_radius_content: forall n l (env : Env l n) val va, *)
(*     get_val va env val -> *)
(*     adequate (parse_attribute_content val) (radius_attr_HOAS.parse_attribute_content va) env. *)
(* Proof. *)
(*   unfold adequate, parse_attribute_content, radius_attr_HOAS.parse_attribute_content. *)
(*   intros. econstructor. econstructor. econstructor. exact H. *)
(*   pose N.eqb_eq. pose N.eqb_neq. *)
(*   destruct (N.eqb (SizeNat.val val) 1) eqn:?. *)
(*   - apply i in Heqb. rewrite Heqb. econstructor. simpl. *)
(*     destruct (run_take (len s) s a) eqn:?. *)
(*     + destruct p. econstructor. repeat econstructor. unfold get_val. rewrite Nat.sub_diag. *)
(*       econstructor. exact Heqo. admit. *)
(*     + apply SLetInF. repeat econstructor. unfold get_val. rewrite Nat.sub_diag. *)
(*       econstructor. exact Heqo. *)
(*   - apply i0 in Heqb. eapply SLSconsNEq. exact Heqb. *)
(*     destruct (N.eqb (SizeNat.val val) 2) eqn:?. *)
(*     + apply i in Heqb0. rewrite Heqb0. econstructor. simpl. *)
(*       destruct (run_take (len s) s a) eqn:?. *)
(*       * destruct p. econstructor. repeat econstructor. unfold get_val. rewrite Nat.sub_diag. *)
(*         econstructor. exact Heqo. admit. *)
(*       * apply SLetInF. repeat econstructor. unfold get_val. rewrite Nat.sub_diag. *)
(*         econstructor. exact Heqo. *)
(*     + apply i0 in Heqb0. eapply SLSconsNEq. exact Heqb0. *)
(*       destruct (N.eqb (SizeNat.val val) 3) eqn:?. *)
(*       * apply i in Heqb1. rewrite Heqb1. econstructor. simpl. *)
(*         econstructor. repeat econstructor. econstructor. repeat econstructor. *)
(*         econstructor. repeat econstructor. *)
(*         -- unfold get_val. simpl. repeat rewrite <- minus_Sn_m; auto. *)
(*            rewrite Nat.sub_diag. repeat econstructor. *)
(*         -- unfold get_val. rewrite Nat.sub_diag. repeat econstructor. *)
(*         -- destruct (len s <? 2) eqn:?. *)
(*            econstructor. econstructor. *)
(*            ++ unfold get_val. rewrite Nat.sub_diag. repeat econstructor. *)
(*            ++ simpl. repeat econstructor. *)
(*            ++ simpl. econstructor. eapply SIfThenElseF. *)
(*               ** unfold get_val. rewrite Nat.sub_diag. repeat econstructor. *)
(*               ** econstructor. repeat econstructor. *)
(*                  destruct (run_take 1 s a) eqn:?. *)
(*                  --- destruct p. destruct (run_deref a (pos s1) (len s1)) eqn:?. *)
(*                      +++ destruct a0; simpl. *)
(*                          *** destruct (run_take (len s0) s0 a) eqn:?. *)
(*                              ---- destruct p. repeat econstructor. *)
(*                                   unfold get_val. rewrite Nat.sub_diag. repeat econstructor. *)
(*                                   exact Heqo. *)
(*                                   unfold get_val. rewrite Nat.sub_diag. repeat econstructor. *)
(*                                   eapply Heqo0. *)
(*                                   unfold get_val. rewrite Nat.sub_diag. repeat econstructor. *)
(*                                   exact Heqo1. *)
(*                                   unfold get_val. rewrite <- minus_Sn_m; auto. *)
(*                                   rewrite Nat.sub_diag. repeat econstructor. *)
(*                              ---- econstructor. repeat econstructor. *)
(*                                   unfold get_val. rewrite Nat.sub_diag. repeat econstructor. *)
(*                                   exact Heqo. *)
(*                                   unfold get_val. rewrite Nat.sub_diag. repeat econstructor. *)
(*                                   eapply Heqo0. *)
(*                                   eapply SLetInF. repeat econstructor. *)
(*                                   unfold get_val. rewrite Nat.sub_diag. repeat econstructor. *)
(*                                   exact Heqo1. *)
(*                          *** *)

(* Lemma adequate_radius_attr: adequate parse_radius_attribute radius_attr_HOAS.parse_radius_attribute Nil. *)
(* Proof. *)
(*   unfold adequate. unfold parse_radius_attribute. unfold radius_attr_HOAS.parse_radius_attribute. *)
(*   simpl. intros. *)
(*   destruct (run_take 1 s a) eqn:?; simpl. *)
(*   - destruct p. destruct (run_deref a (pos s1) (len s1)) eqn:?; simpl. *)
(*     + destruct a0 eqn:?; simpl. *)
(*       * apply SLetInF. rewrite <- Heqa1 in *. econstructor. econstructor. *)
(*         econstructor. repeat econstructor. exact Heqo. *)
(*         econstructor. econstructor. econstructor. econstructor. exact Heqo0. *)
(*         repeat econstructor. rewrite Heqa1. econstructor. *)
(*       * destruct a1 eqn:?. *)
(*         -- econstructor. *)
(*            ++ econstructor. econstructor. econstructor. *)
(*               econstructor. econstructor. econstructor. exact Heqo. *)
(*               econstructor. econstructor. econstructor. econstructor. *)
(*               exact Heqo0. econstructor. eapply SPatLCons. repeat econstructor. repeat econstructor. *)
(*            ++ simpl. destruct (run_take 1 s0 a) eqn:?. *)
(*               ** destruct p. destruct (run_deref a (pos s3) (len s3)) eqn:?. *)
(*                  destruct a2; simpl. *)
(*                  --- econstructor. repeat econstructor. *)
(*                      apply SLetInF. apply SLetInF. repeat econstructor. *)
(*                      exact Heqo1. exact Heqo2. *)
(*                  --- destruct a2; simpl. *)
(*                      +++ destruct (2 <=? val n0) eqn:?; simpl. *)
(*                          destruct (run_take (val n0 - 2) s2 a) eqn:?. *)
(*                          *** destruct p. econstructor. *)
(*                              econstructor. econstructor. econstructor. econstructor. *)
(*                          econstructor. econstructor. repeat econstructor. exact Heqo1. *)
(*                          econstructor. repeat econstructor. exact Heqo2. *)
(*                          econstructor. eapply SPatLCons. econstructor. repeat econstructor. *)
(*                          repeat econstructor. rewrite Heqb. econstructor. *)
(*                          repeat econstructor. exact Heqo3. econstructor. econstructor. *)
(*                          econstructor. econstructor. econstructor. econstructor. *)
(*                          econstructor. econstructor. econstructor. econstructor. *)
(*                          econstructor. *)

                     (* +++ repeat econstructor. *)
                     (* +++ apply SIfThenElseF. econstructor. econstructor. econstructor *)
                     (* exact Heqo1. *)
