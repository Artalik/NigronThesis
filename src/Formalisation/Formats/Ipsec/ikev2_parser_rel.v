From FreeMonad Require Import Nom HOAS RelNomHOAS optiVal ikev2_transforms ikev2 ikev2_parser.

Lemma test : forall vs s lengt,
    sem_val vs s ->
    sem_val (VLength vs) lengt ->
    lengt = len s.
Proof. intros. next_step H0. sem_val_eq. f_equal. auto. Qed.

Ltac reduce := subst; repeat reduce_val; repeat sem_val_eq; subst.

(* Ltac red_equiv := *)
(*   match goal with *)
(*   | H : equiv _ _ _ |- _ => *)
(*       let p := fresh "p" in *)
(*       let P0 := fresh "P" in *)
(*       let P1 := fresh "P" in *)
(*       destruct H as (p&P0&P1) *)
(*   end. *)

Ltac finish_lia := (* repeat red_equiv;  *)reduce_vals; lia.

Ltac simpl_span := simpl (pos _) in *; simpl (len _) in *.

Definition sig_parse_ikev2_header :
  sig (fun code => forall a vs, adequate parse_ikev2_header code a vs).
  unfold parse_ikev2_header. eapply exist. intros a vs.
  eapply bind_adequate. eapply length_adequate.
  intros. SEMLENGTH H. reduce.
  eapply ite_adequate; intros. eapply fail_adequate. eapply N.ltb_ge in H.
  eapply bind_adequate. eapply be_u64_adequate_2; eauto. lia.
  intros. SEMU64 H0. reduce. apply bind_adequate. eapply be_u64_adequate_2. eauto. finish_lia.
  intros. SEMU64 H0. reduce. eapply bind_adequate. eapply map_adequate; eauto.
  eapply be_u8_adequate_2; eauto. simpl. lia.
  intros. eapply RVmk_payload_type. eauto.
  intros. SEMBIND H0. SEMU8 P. next_step P4. reduce. simpl_span.
  eapply bind_adequate. eapply be_u8_adequate_2; eauto. finish_lia.
  intros. SEMU8 H0. reduce. eapply bind_adequate.
  eapply map_adequate; eauto. eapply be_u8_adequate_2. eauto. finish_lia.
  intros. eapply RVmk_exc. eauto.
  intros. SEMBIND H0. SEMU8 P. next_step P26. reduce.
  eapply bind_adequate. eapply be_u8_adequate_2; eauto. finish_lia.
  intros. SEMU8 H0. reduce. eapply bind_adequate. eapply be_u32_adequate; eauto.
  intros. eapply bind_adequate. eapply be_u32_adequate; eauto.
  intros. eapply ret_adequate. eapply RVmk_header.
  eauto. eauto. eauto. unfold shift_right. eapply RVNatN. eapply RVDiv. eapply RVVal.
  eauto. eapply RVNat. eapply RVNatN. eapply RVMod. eapply RVVal.
  eauto. eapply RVNat. eauto. eauto. eauto. eauto. eapply RVLt; eauto. eapply RVNat.
Defined.

Lemma parse_ikev2_header_adequate : forall a vs,
    adequate parse_ikev2_header (`sig_parse_ikev2_header) a vs.
Proof. destruct sig_parse_ikev2_header. auto. Qed.

Lemma bind_length_adequate : forall X (h : val N -> Expr X) e a vs,
    (forall res vs',
        sem_HOAS a vs HOAS.length (Val res vs') ->
        adequate e (h res) a vs') ->
    adequate e (let! len := HOAS.length in h len) a vs.
Proof.
  intros. intros res0 SEM s VALS. next_step SEM.
  - SEMLENGTH H4. subst. eapply H; eauto. reduce_vals. econstructor. econstructor; eauto.
    reduce_vals. auto.
  - next_step H3. next_step H5.
Qed.


Lemma bind_fail_adequate : forall X Y (f : X -> Nom Y) (e : Nom X) a vs,
    adequate e HOAS.fail a vs \/
    (forall s, sem_val vs s ->
        exists vs' s' res fuel,
          run fuel e s a = Res (s',res) /\
            adequate (f res) fail a vs' /\
            sem_val vs' s') ->
    adequate (bind e f) HOAS.fail a vs.
Proof.
  intros. destruct H.
  - intros res0 SEM s VALS. next_step SEM. next_step H4.
    eapply H in VALS. 2 : econstructor. 2 : econstructor.
    simpl in *. destruct VALS. eapply run_bind_fail in H0. exists x. eauto.
  - intros res0 SEM s VALS. next_step SEM. next_step H4.
    pose (SAVE := VALS). eapply H in SAVE.
    destruct SAVE as [vs' [s' [res [fuel [P1 [P2 P0]]]]]].
    edestruct (P2 (Error vs')). repeat econstructor. eauto.
    eapply run_bind in P1. destruct P1 as [fuel0 [P5 [P3 P4]]].
    exists fuel0. eapply P4. eapply H0. auto.
Qed.

(* Lemma bind_fail_adequate : forall X Y (f : X -> Nom Y) (e : Nom X) a env vs, *)
(*     (forall s, *)
(*         sem_val env vs s -> *)
(*         exists env' vs' s' res fuel, *)
(*           run fuel e s a = Res (s',res) /\ *)
(*             adequate (f res) fail a env' vs' /\ *)
(*             sem_val env' vs' s') \/ *)
(*       (forall s, sem_val env vs s -> exists fuel, run fuel e s a = NoRes) -> *)
(*     adequate (bind e f) HOAS.fail a env vs. *)
(* Proof. *)
(*   intros. destruct H. *)
(*   - intros env'' res0 SEM s VALS. next_step SEM. next_step H5. *)
(*     pose (SAVE := VALS). eapply H in SAVE. *)
(*     destruct SAVE as [env' [vs' [s' [res [fuel [P1 [P2 P0]]]]]]]. *)
(*     edestruct (P2 env' (Error vs')). repeat econstructor. eapply extension_env_refl. eauto. *)
(*     eapply run_bind in P1. destruct P1 as [fuel0 [P5 [P3 P4]]]. *)
(*     exists fuel0. eapply P4. eapply H0. auto. *)
(*   - intros env' res SEM s VALS. next_step SEM. next_step H5. destruct (H s). eauto. *)
(*     eapply run_bind_fail in H0. exists x. eapply H0. *)
(* Qed. *)

(* Inductive N_inf := *)
(* | Val of N *)
(* | Inf. *)

(* Definition add_N_inf (n0 n1 : N_inf):= *)
(*   match n0 with *)
(*   | Val v0 => *)
(*       match n1 with *)
(*       | Val v1 => Val (v0 +v1) *)
(*       | Inf => Inf *)
(*       end *)
(*   | Inf => Inf *)
(*   end. *)



Definition sig_parse_ikev2_payload_generic :
  sig (fun code => forall a env vs, adequate parse_ikev2_payload_generic code a env vs).
  eapply exist. intros a env vs. unfold parse_ikev2_payload_generic.
  eapply bind_length_adequate. intros.
  eapply length_properties in H as [EQ0 [EQ1 EQ2]]. subst.
  instantiate (1 := (fun v => If (VLt v (VNat 4)) Then _ Else _)). simpl ((fun _ => _) _).
  eapply IFE_adequate; intro; reduce.
  - eapply N.ltb_lt in H2. destruct (Array.lt_dec (len s) 1); eapply bind_fail_adequate.
    + left. repeat intro. next_step H. next_step H8. exists (S 110). simpl. sem_val_eq. subst.
      unfold run_take. rewrite N.lt_1_r in l. rewrite l.
      destruct (1 <=? 0) eqn:?. eapply N.leb_le in Heqb. lia. reflexivity.
    + right. intros. sem_val_eq. subst. revert a. induction (pos s) using N.peano_ind; intros.
      * destruct a.
        -- right. intros. exists (S 110). simpl. sem_val_eq. subst.
           unfold run_take. eapply N.leb_le in l. rewrite l. unfold run_read. simpl.
           rewrite lookupN_equation_1. reflexivity.
        -- left. intros. sem_val_eq; subst. repeat eexists.
           ++ instantiate (3 := S 10). simpl.
              unfold run_take. eapply N.leb_le in l. rewrite l. unfold run_read. simpl.
              eapply N.leb_le in l. rewrite N.add_0_r.
              rewrite lookupN_equation_2. reflexivity.
           rewrite <- N.succ_pos_spec. rewrite lookupN_equation_3.
           rewrite N.succ_pos_spec. rewrite N.pred_succ. .
           rewrite <- Heqn0. reflexivity.
           eapply N.leb_le in l. Search lookupN.





  repeat econstructor.
  eapply bind_adequate. eapply map_adequate. eapply be_u8_adequate.
  intros. eapply RVmk_payload_type; eauto.
  intros. eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply verify_adequate. eapply be_u16_adequate.
  intros. eapply RVLe. eapply RVNat. eapply RVVal. eauto.
  intros. apply bind_adequate. eapply take_adequate. eapply RVMinus.
  eapply RVVal. eauto. eapply RVNat. next_step H5. next_step H16. next_step H17.
  next_step H13. next_step H11. next_step H10. repeat sem_val_eq. subst.
  eapply N.leb_le in H9. eauto. next_step H17. next_step H12.
  intros. eapply ret_adequate. eapply RVmk_genericpayload. eapply RVmk_payloadheader.
  eapply sem_val_ext; eauto. do 7 (eapply extension_trans; eauto).
  eapply RVEq. eapply RVVal.
  eapply RVNatN. eapply RVDiv. eapply RVVal.
  eapply sem_val_ext; eauto. do 7 (eapply extension_trans; eauto). eapply RVNat. eapply RVNat.
  eapply RVNatN. eapply RVMod. eapply RVVal.
  eapply sem_val_ext; eauto. do 7 (eapply extension_trans; eauto). eapply RVNat.
  eapply sem_val_ext; eauto. eauto.
Defined.

Lemma parse_ikev2_payload_generic_adequate :
  forall a env vs, adequate parse_ikev2_payload_generic (`sig_parse_ikev2_payload_generic) a env vs.
Proof. destruct sig_parse_ikev2_payload_generic. auto. Qed.

Definition sig_parse_ikev2_transform :
  sig (fun code => forall a env vs, adequate parse_ikev2_transform code a env vs).
  eapply exist. intros a env vs. unfold parse_ikev2_transform.
  eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply be_u16_adequate.
  intros. eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply be_u16_adequate.
  intros. eapply bind_adequate. eapply cond_adequate.
  intros. eapply take_adequate. eapply RVMinus. eapply RVVal.
  eapply sem_val_ext; eauto. do 3 (eapply extension_trans; eauto). eapply RVNat.
  eapply N.ltb_lt in H17. lia. eapply RVLt. eapply RVNat. eapply RVVal.
  eapply sem_val_ext; eauto. do 3 (eapply extension_trans; eauto).
  intros. eapply ret_adequate. eapply RVmk_raw.
  eapply sem_val_ext; eauto. do 5 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. do 5 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. do 5 (eapply extension_trans; eauto).
  eapply RVmk_transform. eapply sem_val_ext; eauto. do 5 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. do 5 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. eauto.
Defined.

Lemma parse_ikev2_transform_adequate :
  forall a env vs, adequate parse_ikev2_transform (`sig_parse_ikev2_transform) a env vs.
Proof. destruct sig_parse_ikev2_transform. auto. Qed.

Definition sig_parse_ikev2_proposal :
  sig (fun code => forall a env vs, adequate parse_ikev2_proposal code a env vs).
  eapply exist. intros a env vs. unfold parse_ikev2_proposal.
  eapply bind_adequate. eapply length_adequate.
  intros. eapply ite_adequate; intros. eapply fail_adequate.
  eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply be_u16_adequate.
  intros. eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply map_adequate. eapply be_u8_adequate.
  intros. eapply RVmk_prot. eauto.
  intros. eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply cond_adequate.
  intro. eapply take_adequate. eapply RVVal.
  eapply sem_val_ext; eauto. eapply RVLt. eapply RVNat. apply RVVal.
  eapply sem_val_ext; eauto.
  intros. eapply ite_adequate; intros. eapply fail_adequate.
  eapply N.ltb_ge in H27.
  eapply bind_adequate. eapply map_parser_adequate. eapply take_adequate.
  eapply RVMinus. eapply RVMinus. eapply RVVal. eapply sem_val_ext; eauto.
  do 5 (eapply extension_trans; eauto). eapply RVNat. lia.
  eapply RVVal. eapply sem_val_ext; eauto. do 5 (eapply extension_trans; eauto). lia.
  intros. eapply (count_adequate "IkeV2RawTransform"). eapply RVVal.
  eapply sem_val_ext; eauto. do 2 (eapply extension_trans; eauto).
  intros. eapply parse_ikev2_transform_adequate.
  intros. eapply ret_adequate. eapply RVmk_proposal.
  eapply sem_val_ext; eauto. do 8 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. do 8 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. do 8 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. do 8 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. do 8 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. do 8 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. do 8 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. eauto.
  eapply RVLt. eapply RVVal. eapply sem_val_ext; eauto. do 8 (eapply extension_trans; eauto).
  eapply RVPlus. eapply RVNat. eapply RVVal.
  eapply sem_val_ext; eauto. do 8 (eapply extension_trans; eauto).
  eapply RVLt. eauto. eapply RVNat.
Defined.

Lemma parse_ikev2_proposal_adequate :
  forall a env vs, adequate parse_ikev2_proposal (`sig_parse_ikev2_proposal) a env vs.
Proof. destruct sig_parse_ikev2_proposal. auto. Qed.

Definition sig_parse_ikev2_payload_sa :
    sig (fun code => forall n a env vs, adequate (parse_ikev2_payload_sa n) code a env vs).
  eapply exist. intros n a env vs. unfold parse_ikev2_payload_sa.
  eapply map_adequate. eapply (many1_adequate "IkeV2Proposal").
  intros. eapply parse_ikev2_proposal_adequate.
  intros. eapply RVSA. eauto.
Defined.

Lemma parse_ikev2_payload_sa_adequate :
  forall n a env vs, adequate (parse_ikev2_payload_sa n) (`sig_parse_ikev2_payload_sa) a env vs.
Proof. destruct sig_parse_ikev2_payload_sa. auto. Qed.

Definition sig_parse_ikev2_payload_kex : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_kex n) code a env vs).
  intro hn. eapply exist. intros. unfold parse_ikev2_payload_kex.
  eapply ite_adequate; intros. eapply fail_adequate.
  eapply bind_adequate. eapply map_adequate. eapply be_u16_adequate.
  intros. eapply RVmk_transformdh. eauto.
  intros. eapply bind_adequate. eapply be_u16_adequate.
  intros. eapply bind_adequate. eapply take_adequate.
  eapply RVMinus. eapply RVVal. eapply sem_val_ext; eauto. eapply extension_trans; eauto.
  eapply RVNat. eapply N.ltb_ge in H0. auto.
  intros. eapply ret_adequate. eapply RVKE. eapply RVmk_ExcPayload.
  eapply sem_val_ext; eauto. eapply extension_trans; eauto.
  eapply sem_val_ext; eauto. eauto.
  eapply RVLt. eapply RVVal. eauto. eapply RVNat.
Defined.

Lemma parse_ikev2_payload_kex_adequate : forall hn,
    forall n a env vs,
     sem_val env hn n ->
     adequate (parse_ikev2_payload_kex n) (proj1_sig (sig_parse_ikev2_payload_kex hn)) a env vs.
Proof. intros. destruct sig_parse_ikev2_payload_kex. auto. Qed.

Definition sig_parse_ikev2_payload_ident_init : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_ident_init n) code a env vs).
  intro hn. eapply exist. intros n a env vs VALN. unfold parse_ikev2_payload_ident_init.
  eapply ite_adequate; intros. eapply fail_adequate.
  eapply bind_adequate. eapply map_adequate. eapply be_u8_adequate.
  intros. eapply RVmk_ident. eauto.
  intros. eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply be_u16_adequate.
  intros. eapply bind_adequate. eapply take_adequate.
  eapply RVMinus. eapply RVVal. eapply sem_val_ext; eauto. do 2 (eapply extension_trans; eauto).
  eapply RVNat. eapply N.ltb_ge in H. lia.
  intros. eapply ret_adequate. eapply RVIDi. eapply RVmk_IdPayload.
  eapply sem_val_ext; eauto. do 2 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. do 2 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. eauto.
  eapply RVLt. eapply RVVal. eauto. eapply RVNat.
Defined.

Lemma parse_ikev2_payload_ident_init_adequate : forall hn,
  forall n a env vs,
    sem_val env hn n ->
    adequate (parse_ikev2_payload_ident_init n) (proj1_sig (sig_parse_ikev2_payload_ident_init hn)) a env vs.
Proof. intros. destruct sig_parse_ikev2_payload_ident_init. auto. Qed.

Definition sig_parse_ikev2_payload_ident_resp : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_ident_resp n) code a env vs).
  intro hn. eapply exist. intros. unfold parse_ikev2_payload_ident_resp.
  eapply ite_adequate; intros. eapply fail_adequate.
  eapply bind_adequate. eapply map_adequate. eapply be_u8_adequate.
  intros. eapply RVmk_ident. eauto.
  intros. eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply be_u16_adequate.
  intros. eapply bind_adequate. eapply take_adequate. eapply RVMinus.
  eapply RVVal. eapply sem_val_ext; eauto. repeat (eapply extension_trans; eauto).
  eapply RVNat. eapply N.ltb_ge in H0. auto.
  intros. eapply ret_adequate. eapply RVIDr. eapply RVmk_IdPayload.
  eapply sem_val_ext; eauto. repeat (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. repeat (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. eauto.
  eapply RVLt. eapply RVVal. eauto. eapply RVNat.
Defined.

Lemma parse_ikev2_payload_ident_resp_adequate : forall hn,
    forall n a env vs,
      sem_val env hn n ->
      adequate (parse_ikev2_payload_ident_resp n) (proj1_sig (sig_parse_ikev2_payload_ident_resp hn)) a env vs.
Proof. intros. destruct sig_parse_ikev2_payload_ident_resp. auto. Qed.

Definition sig_parse_ikev2_payload_certificate : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_certificate n) code a env vs).
  intro hn. eapply exist. intros. unfold parse_ikev2_payload_certificate.
  eapply ite_adequate; intros. eapply fail_adequate.
  eapply bind_adequate. eapply map_adequate. eapply be_u8_adequate.
  intros. eapply RVmk_certEnc. eauto.
  intros. eapply bind_adequate. eapply take_adequate. eapply RVMinus. eapply RVVal.
  eapply sem_val_ext; eauto. eapply RVNat. eapply N.ltb_ge in H0. auto.
  intros. eapply ret_adequate. eapply RVCertificatePC. eapply RVmk_certiPayload.
  eapply sem_val_ext; eauto. eauto. eapply RVLt. eapply RVVal. eauto. eapply RVNat.
Defined.

Lemma parse_ikev2_payload_certificate_adequate : forall hn,
  forall n a env vs,
    sem_val env hn n ->
    adequate (parse_ikev2_payload_certificate n)
             (proj1_sig (sig_parse_ikev2_payload_certificate hn)) a env vs.
Proof. intros. destruct sig_parse_ikev2_payload_certificate. auto. Qed.

Definition sig_parse_ikev2_payload_certificate_request : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_certificate_request n) code a env vs).
  intro hn. eapply exist. intros. unfold parse_ikev2_payload_certificate_request.
  eapply ite_adequate; intros. eapply fail_adequate.
  eapply bind_adequate. eapply map_adequate. eapply be_u8_adequate.
  intros. eapply RVmk_certEnc. eauto.
  intros. eapply bind_adequate. eapply take_adequate. eapply N.ltb_ge in H0.
  eapply RVMinus. eapply RVVal. eapply sem_val_ext; eauto. eapply RVNat. auto.
  intros. eapply ret_adequate. eapply RVCertificateRequestPC. eapply RVmk_certReqPayload.
  eapply sem_val_ext; eauto. eauto.
  eapply RVLt. eapply RVVal. eauto. eapply RVNat.
Defined.

Lemma parse_ikev2_payload_certificate_request_adequate : forall hn,
  forall n a env vs,
    sem_val env hn n ->
    adequate (parse_ikev2_payload_certificate_request n)
             (proj1_sig (sig_parse_ikev2_payload_certificate_request hn)) a env vs.
Proof. intros. destruct sig_parse_ikev2_payload_certificate_request. auto. Qed.

Definition sig_parse_ikev2_payload_authentication : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_authentication n) code a env vs).
  intro hn. eapply exist. intros. unfold parse_ikev2_payload_authentication.
  eapply ite_adequate; intros. eapply fail_adequate.
  eapply bind_adequate. eapply map_adequate. eapply be_u8_adequate.
  intros. eapply RVmk_authMethod. eauto.
  intros. eapply bind_adequate. eapply take_adequate. eapply RVMinus. eapply RVVal.
  eapply sem_val_ext; eauto. eapply RVNat. eapply N.ltb_ge. auto.
  intros. eapply ret_adequate. eapply RVAuthenticationPC. eapply RVmk_authPayload.
  eapply sem_val_ext; eauto. eauto. eapply RVLt. eapply RVVal. eauto. eapply RVNat.
Defined.

Lemma parse_ikev2_payload_authentication_adequate : forall hn,
    forall n a env vs,
      sem_val env hn n ->
      adequate (parse_ikev2_payload_authentication n)
               (proj1_sig (sig_parse_ikev2_payload_authentication hn)) a env vs.
Proof. intro hn. destruct sig_parse_ikev2_payload_authentication. auto. Qed.

Definition sig_parse_ikev2_payload_nonce : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_nonce n) code a env vs).
  intro hn. eapply exist. intros. unfold parse_ikev2_payload_nonce.
  eapply bind_adequate. eapply take_adequate. eapply RVVal. eauto.
  intros. eapply ret_adequate. eapply RVNoncePC. eapply RVmk_noncePayload. eauto.
Defined.

Lemma parse_ikev2_payload_nonce_adequate : forall hn,
    forall n a env vs,
      sem_val env hn n ->
      adequate (parse_ikev2_payload_nonce n)
               (proj1_sig (sig_parse_ikev2_payload_nonce hn)) a env vs.
Proof. intro hn. destruct sig_parse_ikev2_payload_nonce. auto. Qed.

Definition sig_parse_ikev2_payload_notify : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_notify n) code a env vs).
  intro hn. eapply exist. intros. unfold parse_ikev2_payload_notify.
  eapply bind_adequate. eapply map_adequate. eapply be_u8_adequate.
  intros. eapply RVmk_prot. eauto.
  intros. eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply map_adequate. eapply be_u16_adequate.
  intros. eapply RVmk_notify. eauto.
  intros. eapply bind_adequate. eapply cond_adequate; intros. eapply take_adequate.
  eapply RVVal. eapply sem_val_ext; eauto. eapply RVLt. eapply RVNat. eapply RVVal.
  eapply sem_val_ext; eauto.
  intros. eapply bind_adequate. eapply cond_adequate. intros. eapply take_adequate.
  eapply RVMinus. eapply RVVal. eapply sem_val_ext; eauto.
  do 3 (eapply extension_trans; eauto). eapply RVPlus. eapply RVNat. eapply RVVal.
  eapply sem_val_ext; eauto. do 3 (eapply extension_trans; eauto).
  eapply N.ltb_lt in H12. lia. eapply RVLt. eapply RVPlus. eapply RVNat. eapply RVVal.
  eapply sem_val_ext; eauto. do 3 (eapply extension_trans; eauto). eapply RVVal.
  eapply sem_val_ext; eauto. do 3 (eapply extension_trans; eauto).
  intros. eapply ret_adequate. eapply RVNotifyPC. eapply RVmk_notifyPayload.
  eapply sem_val_ext; eauto. do 3 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. do 3 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. do 3 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. eauto.
Defined.

Lemma parse_ikev2_payload_notify_adequate : forall hn,
    forall n a env vs,
      sem_val env hn n ->
      adequate (parse_ikev2_payload_notify n)
               (proj1_sig (sig_parse_ikev2_payload_notify hn)) a env vs.
Proof. intro hn. destruct sig_parse_ikev2_payload_notify. auto. Qed.

Definition sig_parse_ikev2_payload_vendor_id : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_vendor_id n) code a env vs).
  intro hn. eapply exist. intros. unfold parse_ikev2_payload_vendor_id.
  eapply ite_adequate; intros. eapply fail_adequate.
  eapply bind_adequate. eapply take_adequate. eapply RVMinus. eapply RVVal. eauto.
  eapply RVNat. eapply N.ltb_ge. eauto.
  intros. eapply ret_adequate. eapply RVVendorIDPC. eapply RVmk_vendorIdPayload. eauto.
  eapply RVLt. eapply RVVal. eauto. eapply RVNat.
Defined.

Lemma parse_ikev2_payload_vendor_id_adequate : forall hn,
  forall n a env vs,
    sem_val env hn n ->
    adequate (parse_ikev2_payload_vendor_id n)
             (proj1_sig (sig_parse_ikev2_payload_vendor_id hn)) a env vs.
Proof. intro hn. destruct sig_parse_ikev2_payload_vendor_id. auto. Qed.

Definition sig_parse_ikev2_payload_delete : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_delete n) code a env vs).
  intro hn. eapply exist. intros. unfold parse_ikev2_payload_delete.
  eapply ite_adequate; intros. eapply fail_adequate.
  eapply bind_adequate. eapply map_adequate. eapply be_u8_adequate.
  intros. eapply RVmk_prot. eauto.
  intros. eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply be_u16_adequate.
  intros. eapply bind_adequate. eapply take_adequate. eapply RVMinus. eapply RVVal.
  eapply sem_val_ext; eauto. do 2 (eapply extension_trans; eauto).
  eapply RVNat. eapply N.ltb_ge. auto.
  intros. eapply ret_adequate. eapply RVDeletePC. eapply RVmk_deletePayload.
  eapply sem_val_ext; eauto. do 2 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. do 2 (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. eauto. eapply RVLt. eapply RVVal. eauto. eapply RVNat.
Defined.

Lemma parse_ikev2_payload_delete_adequate : forall hn,
    forall n a env vs,
      sem_val env hn n ->
      adequate (parse_ikev2_payload_delete n)
               (proj1_sig (sig_parse_ikev2_payload_delete hn)) a env vs.
Proof. intro hn. destruct sig_parse_ikev2_payload_delete. auto. Qed.

Definition sig_parse_ts_addr: forall ht,
    sig (fun code => forall t a env vs,
             sem_val env ht t ->
             adequate (parse_ts_addr t) code a env vs).
  intro ht. eapply exist. intros. unfold parse_ts_addr.
  eapply natN_switch_adequate. eapply RVVal. eapply RVval_ts. eauto.
  eapply (LScons_adequate 8). eapply take_adequate. eapply RVNat.
  eapply (LScons_adequate 7). eapply take_adequate. eapply RVNat.
  eapply LSnil_adequate. intros n NOTIN.
  destruct n as [|elem]; try (exfalso; apply elem_neq; repeat constructor; done).
  eapply fail_adequate.
  repeat (destruct elem; try eapply fail_adequate).
  all : exfalso; eapply NOTIN; repeat econstructor; eauto.
Defined.

Lemma parse_ts_addr_adequate : forall ht,
    forall t a env vs,
      sem_val env ht t ->
      adequate (parse_ts_addr t) (proj1_sig (sig_parse_ts_addr ht)) a env vs.
Proof. intro ht. destruct sig_parse_ts_addr. auto. Qed.

Definition sig_parse_ikev2_ts :
  sig (fun code => forall a env vs, adequate parse_ikev2_ts code a env vs).
  eapply exist. intros. unfold parse_ikev2_ts.
  eapply bind_adequate. eapply map_adequate. eapply be_u8_adequate.
  intros. eapply RVmk_tstype. eauto.
  intros. eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply be_u16_adequate.
  intros. eapply bind_adequate. eapply be_u16_adequate.
  intros. eapply bind_adequate. eapply be_u16_adequate.
  intros. eapply bind_adequate. eapply parse_ts_addr_adequate.
  eapply sem_val_ext; eauto. repeat (eapply extension_trans; eauto).
  intros. eapply bind_adequate. eapply parse_ts_addr_adequate.
  eapply sem_val_ext; eauto. repeat (eapply extension_trans; eauto).
  intros. eapply ret_adequate. eapply RVmk_trafficSelec.
  eapply sem_val_ext; eauto. repeat (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. repeat (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. repeat (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. repeat (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. repeat (eapply extension_trans; eauto).
  eapply sem_val_ext; eauto. eauto.
Defined.

Lemma parse_ikev2_ts_adequate : forall a env vs,
    adequate parse_ikev2_ts (`sig_parse_ikev2_ts) a env vs.
Proof. destruct sig_parse_ikev2_ts. auto. Qed.

Definition sig_parse_ikev2_payload_ts : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_ts n) code a env vs).
  intro hn. eapply exist. intros. unfold parse_ikev2_payload_ts.
  eapply ite_adequate; intros. eapply fail_adequate.
  eapply bind_adequate. eapply be_u8_adequate.
  intros. eapply bind_adequate. eapply take_adequate. eapply RVNat.
  intros. eapply bind_adequate. eapply map_parser_adequate. eapply take_adequate.
  eapply RVMinus. eapply RVVal. eapply sem_val_ext; eauto. eapply extension_trans; eauto.
  eapply RVNat. eapply N.ltb_ge. auto.
  intros. eapply (many1_adequate "TrafficSelector"). intros. eapply parse_ikev2_ts_adequate.
  intros. eapply ret_adequate. eapply RVmk_tsp. eapply sem_val_ext; eauto.
  eapply extension_trans; eauto. eapply sem_val_ext; eauto. eauto.
  eapply RVLt. eapply RVVal. eauto. eapply RVNat.
Defined.

Lemma parse_ikev2_payload_ts_adequate : forall hn,
  forall n a env vs,
    sem_val env hn n ->
    adequate (parse_ikev2_payload_ts n) (proj1_sig (sig_parse_ikev2_payload_ts hn)) a env vs.
Proof. intros. destruct sig_parse_ikev2_payload_ts. auto. Qed.

Definition sig_parse_ikev2_payload_ts_init : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_ts_init n) code a env vs).
  intro hn. eapply exist. intros. unfold parse_ikev2_payload_ts_init.
  eapply map_adequate. eapply parse_ikev2_payload_ts_adequate. eauto.
  intros. eapply RVTSi. eauto.
Defined.

Lemma parse_ikev2_payload_ts_init_adequate : forall hn,
    forall n a env vs,
      sem_val env hn n ->
      adequate (parse_ikev2_payload_ts_init n)
               (proj1_sig (sig_parse_ikev2_payload_ts_init hn)) a env vs.
Proof. intros.  destruct sig_parse_ikev2_payload_ts_init. auto. Qed.


Definition sig_parse_ikev2_payload_ts_resp : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_ts_resp n) code a env vs).
  intro hn. eapply exist. intros. unfold parse_ikev2_payload_ts_resp.
  eapply map_adequate. eapply parse_ikev2_payload_ts_adequate. eauto.
  intros. eapply RVTSr. eauto.
Defined.

Lemma parse_ikev2_payload_ts_resp_adequate : forall hn,
    forall n a env vs,
      sem_val env hn n ->
      adequate (parse_ikev2_payload_ts_resp n)
               (proj1_sig (sig_parse_ikev2_payload_ts_resp hn)) a env vs.
Proof. intros. destruct sig_parse_ikev2_payload_ts_resp. auto. Qed.

Definition sig_parse_ikev2_payload_encrypted : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_encrypted n) code a env vs).
  intro hn. eapply exist. intros. unfold parse_ikev2_payload_encrypted.
  eapply map_adequate. eapply take_adequate. eapply RVVal. eauto.
  intros. eapply RVEncrypted. eapply RVmk_EncPay. eauto.
Defined.

Lemma parse_ikev2_payload_encrypted_adequate : forall hn,
    forall n a env vs,
      sem_val env hn n ->
      adequate (parse_ikev2_payload_encrypted n)
               (proj1_sig (sig_parse_ikev2_payload_encrypted hn)) a env vs.
Proof. intros. destruct sig_parse_ikev2_payload_encrypted. auto. Qed.

Definition sig_parse_ikev2_payload_unknown : forall hn,
    sig (fun code => forall n a env vs,
             sem_val env hn n ->
             adequate (parse_ikev2_payload_unknown n) code a env vs).
  intro hn. eapply exist. intros. unfold parse_ikev2_payload_unknown.
  eapply map_adequate. eapply take_adequate. eapply RVVal. eauto.
  intros. eapply RVUnknown. eauto.
Defined.

Lemma parse_ikev2_payload_unknown_adequate : forall hn,
    forall n a env vs,
      sem_val env hn n ->
      adequate (parse_ikev2_payload_unknown n)
               (proj1_sig (sig_parse_ikev2_payload_unknown hn)) a env vs.
Proof. intros. destruct sig_parse_ikev2_payload_unknown. auto. Qed.


Definition sig_parse_ikev2_payload_with_type : forall hn hnpt,
    sig (fun code => forall n npt a env vs,
             sem_val env hn n ->
             sem_val env hnpt npt ->
             adequate (parse_ikev2_payload_with_type n npt) code a env vs).
  intros hn hnpt. eapply exist. intros. unfold parse_ikev2_payload_with_type.
  eapply map_parser_adequate. eapply take_adequate. eapply RVVal. eauto.
  intros. eapply natN_switch_adequate. eapply RVVal. eapply RVvalpayload.
  eapply sem_val_ext; eauto.
  eapply (LScons_adequate 39).
  eapply parse_ikev2_payload_authentication_adequate. eapply sem_val_ext; eauto.
  eapply (LScons_adequate 43).
  eapply parse_ikev2_payload_vendor_id_adequate. eapply sem_val_ext; eauto.
  eapply (LScons_adequate 35).
  eapply parse_ikev2_payload_ident_init_adequate. eapply sem_val_ext; eauto.
  eapply (LScons_adequate 45).
  eapply parse_ikev2_payload_ts_resp_adequate. eapply sem_val_ext; eauto.
  eapply (LScons_adequate 37).
  eapply parse_ikev2_payload_certificate_adequate. eapply sem_val_ext; eauto.
  eapply (LScons_adequate 41).
  eapply parse_ikev2_payload_notify_adequate. eapply sem_val_ext; eauto.
  eapply (LScons_adequate 33).
  eapply parse_ikev2_payload_sa_adequate.
  eapply (LScons_adequate 46).
  eapply parse_ikev2_payload_encrypted_adequate. eapply sem_val_ext; eauto.
  eapply (LScons_adequate 38).
  eapply parse_ikev2_payload_certificate_request_adequate. eapply sem_val_ext; eauto.
  eapply (LScons_adequate 42).
  eapply parse_ikev2_payload_delete_adequate. eapply sem_val_ext; eauto.
  eapply (LScons_adequate 34).
  eapply parse_ikev2_payload_kex_adequate. eapply sem_val_ext; eauto.
  eapply (LScons_adequate 44).
  eapply parse_ikev2_payload_ts_init_adequate. eapply sem_val_ext; eauto.
  eapply (LScons_adequate 36).
  eapply parse_ikev2_payload_ident_resp_adequate. eapply sem_val_ext; eauto.
  eapply (LScons_adequate 40).
  eapply parse_ikev2_payload_nonce_adequate. eapply sem_val_ext; eauto.
  eapply LSnil_adequate. intros value NOTEQ.
  destruct value as [|elem].
  eapply parse_ikev2_payload_unknown_adequate. eapply sem_val_ext; eauto.
  repeat (destruct elem as [elem|elem|]; try (exfalso; apply NOTEQ; repeat constructor; done);
    try (eapply parse_ikev2_payload_unknown_adequate; eapply sem_val_ext; eauto)).
Defined.

Lemma parse_ikev2_payload_with_type_adequate : forall hn hnpt,
    forall n npt a env vs,
      sem_val env hn n ->
      sem_val env hnpt npt ->
      adequate (parse_ikev2_payload_with_type n npt)
               (proj1_sig (sig_parse_ikev2_payload_with_type hn hnpt)) a env vs.
Proof. intros. destruct sig_parse_ikev2_payload_with_type. auto. Qed.

Definition sig_parse_ikev2_payload_list_fold : forall hv hp,
    sig (fun code => forall v p a env vs,
             sem_val env hv v ->
             sem_val env hp p ->
             adequate (parse_ikev2_payload_list_fold v p) code a env vs).
  intros hv hp. eapply exist. intros. rewrite parse_ikev2_payload_list_fold_equation_1.
  eapply ite_adequate; intros. eapply fail_adequate.
  destruct (Array.get v (Array.size (`v) - 1)) as [ivp|] eqn:?.
  - eapply ite_adequate; intros. eapply fail_adequate.
    eapply scope_adequate. eapply bind_adequate. eapply parse_ikev2_payload_with_type_adequate.
    eapply RVNatN. eapply RVMinus. eapply RVVal. eapply RVpayload_length.
    eapply RVhdrGen. eauto. eapply RVNat. eapply N.ltb_ge. auto.
    eapply RVnext_payload_type. eapply RVhdr. eapply RVGetArray. 3: eapply Heqo.
    eapply RVMinus. eapply RVSizeArray. eauto. eapply RVNat. eapply N.eqb_neq in H1. lia. eauto.
    intros. apply bind_adequate. eapply length_adequate.
    intros. eapply ite_adequate; intros.
    eapply ret_adequate. eapply RVAddArray.
    eapply sem_val_ext; eauto. eapply extension_trans; eauto.
    eapply RVmk_payload. eapply RVhdrGen.
    eapply sem_val_ext; eauto. eapply extension_trans; eauto.
    eapply sem_val_ext; eauto. eapply fail_adequate. eapply RVEq. eauto. eapply RVNat.
    eapply RVpayloadGen. eauto. eapply RVLt. eapply RVVal.
    eapply RVpayload_length. eapply RVhdrGen. eauto. eapply RVNat.
  - clear H H0. destruct v as [arr Arr]. destruct Arr. exfalso. unfold Array.get in Heqo.
    simpl in *. rewrite <- Size_wf in Heqo.
    destruct (Values.values_size _ (Array.values arr)). eapply N.eqb_neq in H1. lia.
    rewrite H in Heqo. inversion Heqo.
  - eapply RVEq. eapply RVSizeArray. eauto. eapply RVNat.
Defined.

Lemma parse_ikev2_payload_list_fold_adequate : forall hv hp,
    forall v p a env vs,
      sem_val env hv v ->
      sem_val env hp p ->
      adequate (parse_ikev2_payload_list_fold v p)
               (proj1_sig (sig_parse_ikev2_payload_list_fold hv hp)) a env vs.
Proof. intros. destruct sig_parse_ikev2_payload_list_fold. auto. Qed.

Definition sig_parse_ikev2_payload_list : forall hi,
    sig (fun code => forall i a env vs,
             sem_val env hi i ->
             adequate (parse_ikev2_payload_list i) code a env vs).
  intro hi. eapply exist. intros. rewrite parse_ikev2_payload_list_equation_1.
  eapply repeat_None_adequate.
  intros. eapply bind_adequate. eapply length_adequate.
  intros. eapply ite_adequate; intros. eapply fail_adequate.
  eapply bind_adequate. eapply parse_ikev2_payload_generic_adequate.
  intros. eapply parse_ikev2_payload_list_fold_adequate.
  eapply sem_val_ext; eauto. eapply extension_trans; eauto. eauto.
  eapply RVEq. eauto. eapply RVNat. eapply RVAddArray.
  eapply (RVMakeArray _ "IkeV2Payload"). eapply RVNat. eapply RVmk_payload.
  eapply RVmk_payloadheader. eauto. eapply RVBool. eapply RVNatN. eapply RVNat.
  eapply RVNatN. eapply RVNat. eapply RVDummy.
Defined.

Lemma parse_ikev2_payload_list_adequate : forall hi,
    forall i a env vs,
      sem_val env hi i ->
      adequate (parse_ikev2_payload_list i)
               (proj1_sig (sig_parse_ikev2_payload_list hi)) a env vs.
Proof. intros. destruct sig_parse_ikev2_payload_list. auto. Qed.

Definition sig_parse_ikev2_message :
  sig (fun code => forall a env vs, adequate parse_ikev2_message code a env vs).
  eapply exist. intros. unfold parse_ikev2_message.
  eapply bind_adequate. eapply parse_ikev2_header_adequate.
  intros. eapply ite_adequate; intros. eapply fail_adequate.
  eapply bind_adequate. eapply map_parser_adequate.
  eapply take_adequate. eapply RVMinus. eapply RVVal. eapply RVlength.
  eauto. eapply RVNat. eapply N.ltb_ge. auto.
  intros. eapply parse_ikev2_payload_list_adequate.
  eapply RVnext_payload. eapply sem_val_ext; eauto.
  intros. eapply ret_adequate. eapply RVmk_message.
  eapply sem_val_ext; eauto. eauto.
  eapply RVLt. eapply RVVal. eapply RVlength. eauto. eapply RVNat.
Defined.

Lemma parse_ikev2_message_adequate : forall a env vs,
    adequate parse_ikev2_message (`sig_parse_ikev2_message) a env vs.
Proof. destruct sig_parse_ikev2_message. auto. Qed.
