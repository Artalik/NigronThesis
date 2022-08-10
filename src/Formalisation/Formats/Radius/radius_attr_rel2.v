From Formalisation Require Import SizeNat Nom IpAddr radius_attr.
From Raffinement Require Import PHOAS2 RelNomPHOAS2.


Definition attribute : PHOAS2.type :=
Sum
  (Sum (Sum (Sum (Sum Span Span) (Pair (NatN 8) Span)) (Sum (Sum (Unknown "ipv4") (NatN 32)) (NatN 32)))
     (Sum (Sum (Sum (NatN 32) (Unknown "ipv4")) (Unknown "ipv4")) (Sum (Sum (NatN 32) Span) (Sum (NatN 32) (NatN 32)))))
  (Sum (Sum (Pair (NatN 32) Span) Span) (Sum Span (Pair (NatN 8) Span))).

Definition username (s : VAL Span) : @VAL val attribute :=
  EUna EInl (EUna EInl (EUna EInl (EUna EInl (EUna EInl s)))).

Definition userpass (s : VAL Span) : @VAL val attribute :=
  EUna EInl (EUna EInl (EUna EInl (EUna EInl (EUna EInr s)))).

Definition chappass (n : VAL (NatN 8)) (s: VAL Span): @VAL val attribute :=
  EUna EInl (EUna EInl (EUna EInl (EUna EInr (EBin EPair n s)))).

Definition nasipadd (ip : VAL (Unknown "ipv4")) : @VAL val attribute :=
  EUna EInl (EUna EInl (EUna EInr (EUna EInl (EUna EInl ip)))).

Definition nasport (port : VAL (NatN 32)) : @VAL val attribute :=
  EUna EInl (EUna EInl (EUna EInr (EUna EInl (EUna EInr port)))).

Definition service (service : VAL (NatN 32)) : @VAL val attribute :=
  EUna EInl (EUna EInl (EUna EInr (EUna EInr service))).

Definition protocol (protocol : VAL (NatN 32)) : @VAL val attribute :=
  EUna EInl (EUna EInr (EUna EInl (EUna EInl (EUna EInl protocol)))).

Definition framedipadd (ip : VAL (Unknown "ipv4")) : @VAL val attribute :=
  EUna EInl (EUna EInr (EUna EInl (EUna EInl (EUna EInr ip)))).

Definition framedipmask (ip : VAL (Unknown "ipv4")) : @VAL val attribute :=
  EUna EInl (EUna EInr (EUna EInl (EUna EInr ip))).

Definition routing (fr : VAL (NatN 32)) : @VAL val attribute :=
  EUna EInl (EUna EInr (EUna EInr (EUna EInl (EUna EInl fr)))).

Definition filterid (s : VAL Span) : @VAL val attribute :=
  EUna EInl (EUna EInr (EUna EInr (EUna EInl (EUna EInr s)))).

Definition framedMTU (n : VAL (NatN 32)) : @VAL val attribute :=
  EUna EInl (EUna EInr (EUna EInr (EUna EInr (EUna EInl n)))).

Definition compression (n : VAL (NatN 32)) : @VAL val attribute :=
  EUna EInl (EUna EInr (EUna EInr (EUna EInr (EUna EInr n)))).

Definition vendor (n : VAL (NatN 32)) (s : VAL Span) : @VAL val attribute :=
  EUna EInr (EUna EInl (EUna EInl (EBin EPair n s))).

Definition called (s : VAL Span) : @VAL val attribute :=
  EUna EInr (EUna EInl (EUna EInr s)).

Definition calling (s : VAL Span) : @VAL val attribute :=
  EUna EInr (EUna EInr (EUna EInl s)).

Definition unknown (n : VAL (NatN 8)) (s : VAL Span) : @VAL val attribute :=
  EUna EInr (EUna EInr (EUna EInr (EBin EPair n s))).

Inductive attribute_rel : RadiusAttribute -> type_to_Type attribute -> Prop :=
| SUserName : forall hs s x,
    sem_VAL (username hs) x ->
    sem_VAL hs s ->
    attribute_rel (UserName s) x
| SUserPassword : forall hs  s  x,
    sem_VAL (userpass hs) x ->
    sem_VAL hs s ->
    attribute_rel (UserPassword s) x
| SChapPassword : forall hn  n hs  s  x,
    sem_VAL (chappass hn hs) x ->
    sem_VAL hs s ->
    sem_VAL hn n ->
    attribute_rel (ChapPassword n s) x
| SNIA : forall hip vip ip x,
    sem_VAL (nasipadd hip) x ->
    sem_VAL hip vip ->
    (* ipv4_spec ip (sem_val vip) -> *)
    attribute_rel (NasIPAddress ip) x
| SNP : forall hs  s x,
    sem_VAL (nasport hs) x ->
    sem_VAL hs s ->
    attribute_rel (NasPort s) x
| SService :
  forall hs s x,
    sem_VAL (service hs) x ->
    sem_VAL hs s ->
    attribute_rel (Service (mk_service s)) x
| SProtocol :
  forall hs  s x,
    sem_VAL (protocol hs) x ->
    sem_VAL hs s ->
    attribute_rel (Protocol (mk_protocol s)) x
| SFramedIPAddress :
  forall hip vip ip x,
    sem_VAL (framedipadd hip) x ->
    sem_VAL hip vip ->
    (* ipv4_spec ip (sem_val vip) -> *)
    attribute_rel (FramedIPAddress ip) x
| SFramedIPnetmask :
  forall hip vip ip x,
    sem_VAL (framedipmask hip) x ->
    sem_VAL hip vip ->
    (* ipv4_spec ip (sem_val vip) -> *)
    attribute_rel (FramedIPNetmask ip) x
| SRouting :
  forall hs  s x,
    sem_VAL (routing hs) x ->
    sem_VAL hs s ->
    attribute_rel (Routing (mk_routing s)) x
| SFilterId :
  forall hs  s x,
    sem_VAL (filterid hs) x ->
    sem_VAL hs s ->
    attribute_rel (FilterId s) x
| SFramedMTU :
  forall hs  s x,
    sem_VAL (framedMTU hs) x ->
    sem_VAL hs s ->
    attribute_rel (FramedMTU s) x
| SCompression :
  forall hs  s x,
    sem_VAL (compression hs) x ->
    sem_VAL hs s ->
    attribute_rel (Compression (mk_compression s)) x
| SVendorSpecific :
  forall hn  n hs  s x,
    sem_VAL (vendor hn hs) x ->
    sem_VAL hs s ->
    sem_VAL hn n ->
    attribute_rel (VendorSpecific n s) x
| SCalledStationId :
  forall hs  s x,
    sem_VAL (called hs) x ->
    sem_VAL hs s ->
    attribute_rel (CalledStationId s) x
| SCallingStationId : forall hs  s x,
    sem_VAL (calling hs) x ->
    sem_VAL hs s ->
    attribute_rel (CallingStationId s) x
| SUnknown :
  forall hn  n hs  s x,
    sem_VAL (unknown hn hs) x ->
    sem_VAL hs s ->
    sem_VAL hn n ->
    attribute_rel (radius_attr.Unknown n s) x.

Definition parse_attribute_content_rel (ht : VAL (NatN 8)) :
  {code | forall data s t,
      sem_VAL ht t ->
      adequate (fun _ => attribute_rel)(parse_attribute_content t) code data s}.
  eapply exist. intros. unfold parse_attribute_content.
  eapply (natN_switch_adequate _ (EUna EVal ht)); repeat econstructor; eauto.

  (* 31 *)
  eapply (LScons_adequate _ _ 31).
  step. eapply rest_adequate. destruct H0 as [P0 [P1 P2]].
  eapply (ret_adequate _ _ _ (calling (Var vres))); subst; repeat econstructor; eauto.

  (* 11 *)
  eapply (LScons_adequate _ _ 11).
  step. eapply rest_adequate. destruct H0 as [P0 [P1 P2]].
  eapply (ret_adequate _ _ _ (filterid (Var vres))); subst; repeat econstructor; eauto.

  (* 7 *)
  eapply (LScons_adequate _ _ 7).
  eapply bind_adequate. eapply be_u32_adequate. intros. be_spec_clean.
  eapply (ret_adequate _ _ _ (protocol (Var vres))); subst; repeat econstructor; eauto.

  (* 13 *)
  eapply (LScons_adequate _ _ 13).
  eapply bind_adequate. eapply be_u32_adequate. intros. be_spec_clean.
  eapply (ret_adequate _ _ _ (compression (Var vres))); subst; repeat econstructor; eauto.

  (* 9 *)
  eapply (LScons_adequate _ _ 9).
  eapply map_parser_adequate. eapply consequence_adequate. unfold size4u. step.
  intros. clean_up. split; auto. intros. step.
  eapply get_ipv4_adequate.
  eapply (ret_adequate _ _ _ (framedipmask (Var vres))); subst; repeat econstructor; eauto.

  (* 5 *)
  eapply (LScons_adequate _ _ 5).
  eapply bind_adequate. eapply be_u32_adequate. intros. be_spec_clean. subst.
  eapply (ret_adequate _ _ _ (nasport (Var vres))); subst; repeat econstructor; eauto.

    (* 3 *)
  eapply (LScons_adequate _ _ 3).
  repeat step. eapply be_u8_adequate.
  eapply rest_adequate. be_spec_clean. destruct H2 as [P3 [P4 P2]].
  eapply (ret_adequate _ _ _ (chappass (Var vres0) (Var vres1))); subst; repeat econstructor; eauto.

  (* 30 *)
  eapply (LScons_adequate _ _ 30).
  repeat step. eapply rest_adequate. destruct H0 as [P0 [P1 P2]]. subst.
  eapply (ret_adequate _ _ _ (called (Var vres))); subst; repeat econstructor; eauto.

  (* 26 *)
  eapply (LScons_adequate _ _ 26).
  repeat step. eapply be_u32_adequate. eapply rest_adequate.
  be_spec_clean. destruct H2 as [P2 [P3 P4]].
  eapply (ret_adequate _ _ _ (vendor (Var vres0) (Var vres1))); subst; repeat econstructor; eauto.

  (* 10 *)
  eapply (LScons_adequate _ _ 10).
  eapply bind_adequate. eapply be_u32_adequate. intros. be_spec_clean. subst.
  eapply (ret_adequate _ _ _ (routing (Var vres))); repeat econstructor; eauto.

  (* 6 *)
  eapply (LScons_adequate _ _ 6).
  eapply bind_adequate. eapply be_u32_adequate. intros. be_spec_clean. subst.
  eapply (ret_adequate _ _ _ (service (Var vres))); repeat econstructor; eauto.

  (* 12 *)
  eapply (LScons_adequate _ _ 12).
  eapply bind_adequate. eapply be_u32_adequate. intros. be_spec_clean. subst.
  eapply (ret_adequate _ _ _ (framedMTU (Var vres))); repeat econstructor; eauto.

  (* 8 *)
  eapply (LScons_adequate _ _ 8).
  eapply map_parser_adequate. eapply consequence_adequate. unfold size4u. step.
  intros. clean_up. split; auto. intros.
  step. eapply get_ipv4_adequate.
  eapply (ret_adequate _ _ _ (framedipadd (Var vres))); repeat econstructor; eauto.

  (* 4 *)
  eapply (LScons_adequate _ _ 4).
  eapply map_parser_adequate. eapply consequence_adequate. unfold size4u. step.
  intros. clean_up. split; auto. intros.
  step. eapply get_ipv4_adequate.
  eapply (ret_adequate _ _ _ (nasipadd (Var vres))); repeat econstructor; eauto.

  (* 2 *)
  eapply (LScons_adequate _ _ 2).
  step. eapply rest_adequate. destruct H0 as [P0 [P1 P2]].
  eapply (ret_adequate _ _ _ (userpass (Var vres))); subst; repeat econstructor; eauto.

  (* 1 *)
  eapply (LScons_adequate _ _ 1).
  step. eapply rest_adequate. destruct H0 as [P0 [P1 P2]].
  eapply (ret_adequate _ _ _ (username (Var vres))); subst; repeat econstructor; eauto.

  (* default *)
  eapply LSnil_adequate. intros elem elem_neq.
  destruct elem as [|elem]; try (exfalso; apply elem_neq; repeat constructor; done).

  Ltac solve_default ht :=
      step; [eapply rest_adequate |
          match goal with
          | H : rest_spec _ _ _ ?vres |- _ =>
              let P0 := fresh "P" in
              let P1 := fresh "P" in
              let P2 := fresh "P" in
              destruct H as [P0 [P1 P2]]; subst;
              eapply (ret_adequate _ _ _ (unknown ht (Var vres))); repeat econstructor; eauto
          end].
  solve_default ht.
  repeat (destruct elem; try (exfalso; apply elem_neq; repeat constructor; done);
          try solve_default ht).
Defined.

Lemma parse_attribute_content_adequate (ht : VAL (NatN 8)) :
    forall data s t,
      sem_VAL ht t ->
      adequate (fun _ => attribute_rel)(parse_attribute_content t)
        (proj1_sig (parse_attribute_content_rel ht)) data s.
Proof. intros. destruct parse_attribute_content_rel. eauto. Qed.


Definition parse_radius_attribute_rel :
  {code | forall data vs, adequate (fun _ => attribute_rel) parse_radius_attribute code data vs}.
  eapply exist. intros data vs. unfold parse_radius_attribute.
  repeat step. eapply be_u8_adequate. eapply verify_adequate.
  2 : eapply be_u8_adequate. be_spec_clean. intros vy x s [P2 P1]. subst.
  instantiate (1 := fun vy => EBin ELe (Const (ENat 2)) (EUna EVal (Var vy))).
  simpl. repeat econstructor; eauto. be_spec_clean.
  destruct H0 as [[P1 P3] P2]. subst.
  eapply map_parser_adequate. eapply consequence_adequate. step.
  intros. repeat clean_up. split; auto.
  intros. eapply (parse_attribute_content_adequate (Var vres)); repeat econstructor; eauto.
Defined.

Lemma parse_radius_attribute_adequate : forall data vs,
    adequate (fun _ => attribute_rel) parse_radius_attribute (proj1_sig parse_radius_attribute_rel) data vs.
Proof. intros. destruct parse_radius_attribute_rel. eauto. Qed.

Definition equiv_parse_radius_attribute_rel {var} :
  {code : @PHOAS var _ | equiv_prog Nil _ (`parse_radius_attribute_rel) code}.
  eapply exist. repeat econstructor.
Defined.
