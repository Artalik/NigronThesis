From FreeMonad Require Import SizeNat Nom IpAddr radius_attr PHOAS RelNomPHOAS.

(* Definition attribute : Type := *)
(*   span + span + (nat8 * span) + Ipv4 + nat32 + nat32 + *)
(*     nat32 + Ipv4 + Ipv4 + nat32 + span + nat32 + nat32 + *)
(*     (nat32 * span) + span + span + (nat8 * span). *)

(* Fixpoint inls (n : nat) () *)

Definition attribute : Type :=
  ((span + span + (nat8 * span)) + (ipv4 + nat32 + nat32)) +
    ((nat32 + ipv4 + ipv4) + ((nat32 + span) + (nat32 + nat32))) +
    (((nat32 * span) + span) + (span + (nat8 * span))).

(* Definition username (s : span) : attribute := inl (inl (inl (inl (inl s)))). *)
(* Definition userpass (s : span) : attribute := inl (inl (inl (inl (inr s)))). *)
(* Definition chappass (n : nat8) (s: span): attribute := inl (inl (inl (inr (n,s)))). *)
(* Definition nasipadd (ip : Ipv4) : attribute := inl (inl (inr (inl (inl ip)))). *)
(* Definition nasport (port : nat32) : attribute := inl (inl (inr (inl (inr port)))). *)
(* Definition service (service : nat32) : attribute := inl (inl (inr (inr service))). *)
(* Definition protocol (protocol : nat32) : attribute := inl (inr (inl (inl (inl protocol)))). *)
(* Definition framedipadd (ip : Ipv4) : attribute := inl (inr (inl (inl (inr ip)))). *)
(* Definition framedipmask (ip : Ipv4) : attribute := inl (inr (inl (inr ip))). *)
(* Definition routing (fr : nat32) : attribute := inl (inr (inr (inl (inl fr)))). *)
(* Definition filterid (s : span) : attribute := inl (inr (inr (inl (inr s)))). *)
(* Definition framedMTU (n : nat32) : attribute := inl (inr (inr (inr (inl n)))). *)
(* Definition called (s : span) : attribute := inr (inl (inr s)). *)
(* Definition calling (s : span) : attribute := inr (inr (inl s)). *)
(* Definition unknown (n : nat8) (s : span) : attribute := inr (inr (inr (n,s))). *)

Definition username (s : VAL span) : @VAL val attribute :=
  EUna EInl (EUna EInl (EUna EInl (EUna EInl (EUna EInl s)))).

Definition userpass (s : VAL span) : @VAL val attribute :=
  EUna EInl (EUna EInl (EUna EInl (EUna EInl (EUna EInr s)))).

Definition chappass (n : VAL nat8) (s: VAL span): @VAL val attribute :=
  EUna EInl (EUna EInl (EUna EInl (EUna EInr (EBin EPair n s)))).

Definition nasipadd (ip : VAL ipv4) : @VAL val attribute :=
  EUna EInl (EUna EInl (EUna EInr (EUna EInl (EUna EInl ip)))).

Definition nasport (port : VAL nat32) : @VAL val attribute :=
  EUna EInl (EUna EInl (EUna EInr (EUna EInl (EUna EInr port)))).

Definition service (service : VAL nat32) : @VAL val attribute :=
  EUna EInl (EUna EInl (EUna EInr (EUna EInr service))).

Definition protocol (protocol : VAL nat32) : @VAL val attribute :=
  EUna EInl (EUna EInr (EUna EInl (EUna EInl (EUna EInl protocol)))).

Definition framedipadd (ip : VAL ipv4) : @VAL val attribute :=
  EUna EInl (EUna EInr (EUna EInl (EUna EInl (EUna EInr ip)))).

Definition framedipmask (ip : VAL ipv4) : @VAL val attribute :=
  EUna EInl (EUna EInr (EUna EInl (EUna EInr ip))).

Definition routing (fr : VAL nat32) : @VAL val attribute :=
  EUna EInl (EUna EInr (EUna EInr (EUna EInl (EUna EInl fr)))).

Definition filterid (s : VAL span) : @VAL val attribute :=
  EUna EInl (EUna EInr (EUna EInr (EUna EInl (EUna EInr s)))).

Definition framedMTU (n : VAL nat32) : @VAL val attribute :=
  EUna EInl (EUna EInr (EUna EInr (EUna EInr (EUna EInl n)))).

Definition compression (n : VAL nat32) : @VAL val attribute :=
  EUna EInl (EUna EInr (EUna EInr (EUna EInr (EUna EInr n)))).

Definition vendor (n : VAL nat32) (s : VAL span) : @VAL val attribute :=
  EUna EInr (EUna EInl (EUna EInl (EBin EPair n s))).

Definition called (s : VAL span) : @VAL val attribute :=
  EUna EInr (EUna EInl (EUna EInr s)).

Definition calling (s : VAL span) : @VAL val attribute :=
  EUna EInr (EUna EInr (EUna EInl s)).

Definition unknown (n : VAL nat8) (s : VAL span) : @VAL val attribute :=
  EUna EInr (EUna EInr (EUna EInr (EBin EPair n s))).

Inductive attribute_rel : RadiusAttribute -> attribute -> Prop :=
| SUserName : forall hs vs s v x,
    sem_VAL (username hs) v ->
    sem_val v = x ->
    sem_VAL hs vs ->
    sem_val vs = s ->
    attribute_rel (UserName s) x
| SUserPassword : forall hs vs s v x,
    sem_VAL (userpass hs) v ->
    sem_val v = x ->
    sem_VAL hs vs ->
    sem_val vs = s ->
    attribute_rel (UserPassword s) x
| SChapPassword : forall hn vn n hs vs s v x,
    sem_VAL (chappass hn hs) v ->
    sem_val v = x ->
    sem_VAL hs vs ->
    sem_val vs = s ->
    sem_VAL hn vn ->
    sem_val vn = n ->
    attribute_rel (ChapPassword n s) x
| SNIA : forall hip vip ip v x,
    sem_VAL (nasipadd hip) v ->
    sem_val v = x ->
    sem_VAL hip vip ->
    ipv4_spec ip (sem_val vip) ->
    attribute_rel (NasIPAddress ip) x
| SNP : forall hs vs s v x,
    sem_VAL (nasport hs) v ->
    sem_val v = x ->
    sem_VAL hs vs ->
    sem_val vs = s ->
    attribute_rel (NasPort s) x
| SService :
  forall hs vs s v x,
    sem_VAL (service hs) v ->
    sem_val v = x ->
    sem_VAL hs vs ->
    sem_val vs = s ->
    attribute_rel (Service (mk_service s)) x
| SProtocol :
  forall hs vs s v x,
    sem_VAL (protocol hs) v ->
    sem_val v = x ->
    sem_VAL hs vs ->
    sem_val vs = s ->
    attribute_rel (Protocol (mk_protocol s)) x
| SFramedIPAddress :
  forall hip vip ip v x,
    sem_VAL (framedipadd hip) v ->
    sem_val v = x ->
    sem_VAL hip vip ->
    ipv4_spec ip (sem_val vip) ->
    attribute_rel (FramedIPAddress ip) x
| SFramedIPnetmask :
  forall hip vip ip v x,
    sem_VAL (framedipmask hip) v ->
    sem_val v = x ->
    sem_VAL hip vip ->
    ipv4_spec ip (sem_val vip) ->
    attribute_rel (FramedIPNetmask ip) x
| SRouting :
  forall hs vs s v x,
    sem_VAL (routing hs) v ->
    sem_val v = x ->
    sem_VAL hs vs ->
    sem_val vs = s ->
    attribute_rel (Routing (mk_routing s)) x
| SFilterId :
  forall hs vs s v x,
    sem_VAL (filterid hs) v ->
    sem_val v = x ->
    sem_VAL hs vs ->
    sem_val vs = s ->
    attribute_rel (FilterId s) x
| SFramedMTU :
  forall hs vs s v x,
    sem_VAL (framedMTU hs) v ->
    sem_val v = x ->
    sem_VAL hs vs ->
    sem_val vs = s ->
    attribute_rel (FramedMTU s) x
| SCompression :
  forall hs vs s v x,
    sem_VAL (compression hs) v ->
    sem_val v = x ->
    sem_VAL hs vs ->
    sem_val vs = s ->
    attribute_rel (Compression (mk_compression s)) x
| SVendorSpecific :
  forall hn vn n hs vs s v x,
    sem_VAL (vendor hn hs) v ->
    sem_val v = x ->
    sem_VAL hs vs ->
    sem_val vs = s ->
    sem_VAL hn vn ->
    sem_val vn = n ->
    attribute_rel (VendorSpecific n s) x
| SCalledStationId :
  forall hs vs s v x,
    sem_VAL (called hs) v ->
    sem_val v = x ->
    sem_VAL hs vs ->
    sem_val vs = s ->
    attribute_rel (CalledStationId s) x
| SCallingStationId : forall hs vs s v x,
    sem_VAL (calling hs) v ->
    sem_val v = x ->
    sem_VAL hs vs ->
    sem_val vs = s ->
    attribute_rel (CallingStationId s) x
| SUnknown :
  forall hn vn n hs vs s v x,
    sem_VAL (unknown hn hs) v ->
    sem_val v = x ->
    sem_VAL hs vs ->
    sem_val vs = s ->
    sem_VAL hn vn ->
    sem_val vn = n ->
    attribute_rel (Unknown n s) x.

Definition parse_attribute_content_rel (ht : VAL nat8) :
  {code | forall data s vt t,
      sem_VAL ht vt ->
      sem_val vt = t ->
      adequate (fun _ => attribute_rel)(parse_attribute_content t) code data s}.
  eapply exist. intros. unfold parse_attribute_content. subst.
  eapply (natN_switch_adequate _ (EUna EVal ht)); repeat econstructor; eauto.

  (* 31 *)
  eapply (LScons_adequate 31).
  step. eapply rest_adequate. destruct H0 as [P0 [P1 P2]].
  eapply (ret_adequate _ (calling (Var vres))); repeat econstructor; eauto.

  (* 11 *)
  eapply (LScons_adequate 11).
  step. eapply rest_adequate. destruct H0 as [P0 [P1 P2]].
  eapply (ret_adequate _ (filterid (Var vres))); repeat econstructor; eauto.

  (* 7 *)
  eapply (LScons_adequate 7).
  eapply bind_adequate. eapply be_u32_adequate. intros. clean_up.
  eapply (ret_adequate _ (protocol (Var vres))); repeat econstructor; eauto.

  (* 13 *)
  eapply (LScons_adequate 13).
  eapply bind_adequate. eapply be_u32_adequate. intros. clean_up.
  eapply (ret_adequate _ (compression (Var vres))); repeat econstructor; eauto.

  (* 9 *)
  eapply (LScons_adequate 9).
  eapply map_parser_adequate. eapply consequence_adequate. unfold size4u. step.
  intros. clean_up. auto. intros. step.
  eapply get_ipv4_adequate. unfold ipv4_spec in H1. repeat clean_up.
  eapply (ret_adequate _ (framedipmask (Var vres))); repeat econstructor; eauto.

  (* 5 *)
  eapply (LScons_adequate 5).
  eapply bind_adequate. eapply be_u32_adequate. intros. clean_up. subst.
  eapply (ret_adequate _ (nasport (Var vres))); repeat econstructor; eauto.

    (* 3 *)
  eapply (LScons_adequate 3).
  repeat step. eapply be_u8_adequate.
  eapply rest_adequate. repeat clean_up. destruct H2 as [P3 [P4 P2]]. subst.
  eapply (ret_adequate _ (chappass (Var vres0) (Var vres1))); repeat econstructor; eauto.

  (* 30 *)
  eapply (LScons_adequate 30).
  repeat step. eapply rest_adequate. destruct H0 as [P0 [P1 P2]]. subst.
  eapply (ret_adequate _ (called (Var vres))); repeat econstructor; eauto.

  (* 26 *)
  eapply (LScons_adequate 26).
  repeat step. eapply be_u32_adequate. eapply rest_adequate.
  repeat clean_up. destruct H2 as [P2 [P3 P4]]. subst.
  eapply (ret_adequate _ (vendor (Var vres0) (Var vres1))); repeat econstructor; eauto.

  (* 10 *)
  eapply (LScons_adequate 10).
  eapply bind_adequate. eapply be_u32_adequate. intros. repeat clean_up. subst.
  eapply (ret_adequate _ (routing (Var vres))); repeat econstructor; eauto.

  (* 6 *)
  eapply (LScons_adequate 6).
  eapply bind_adequate. eapply be_u32_adequate. intros. repeat clean_up. subst.
  eapply (ret_adequate _ (service (Var vres))); repeat econstructor; eauto.

  (* 12 *)
  eapply (LScons_adequate 12).
  eapply bind_adequate. eapply be_u32_adequate. intros. repeat clean_up. subst.
  eapply (ret_adequate _ (framedMTU (Var vres))); repeat econstructor; eauto.

  (* 8 *)
  eapply (LScons_adequate 8).
  eapply map_parser_adequate. eapply consequence_adequate. unfold size4u. step.
  intros. clean_up. auto. intros.
  step. eapply get_ipv4_adequate. unfold ipv4_spec in H1. repeat clean_up.
  eapply (ret_adequate _ (framedipadd (Var vres))); repeat econstructor; eauto.

  (* 4 *)
  eapply (LScons_adequate 4).
  eapply map_parser_adequate. eapply consequence_adequate. unfold size4u. step.
  intros. clean_up. auto. intros.
  step. eapply get_ipv4_adequate. unfold ipv4_spec in H1. repeat clean_up.
  eapply (ret_adequate _ (nasipadd (Var vres))); repeat econstructor; eauto.

  (* 2 *)
  eapply (LScons_adequate 2).
  step. eapply rest_adequate. destruct H0 as [P0 [P1 P2]].
  eapply (ret_adequate _ (userpass (Var vres))); repeat econstructor; eauto.

  (* 1 *)
  eapply (LScons_adequate 1).
  step. eapply rest_adequate. destruct H0 as [P0 [P1 P2]].
  eapply (ret_adequate _ (username (Var vres))); repeat econstructor; eauto.

  (* default *)
  eapply LSnil_adequate. intros elem elem_neq.
  destruct elem as [|elem]; try (exfalso; apply elem_neq; repeat constructor; done).
  Ltac solve_default ht :=
      step; [eapply rest_adequate |
          match goal with
          | H : rest_spec _ _ _ (sem_val ?vres) |- _ =>
              let P0 := fresh "P" in
              let P1 := fresh "P" in
              let P2 := fresh "P" in
              destruct H as [P0 [P1 P2]]; subst;
              eapply (ret_adequate _ (unknown ht (Var vres))); repeat econstructor; eauto
          end].
    solve_default ht.
    repeat (destruct elem; try (exfalso; apply elem_neq; repeat constructor; done);
            try solve_default ht).
Defined.

Lemma parse_attribute_content_adequate ht :
    forall data s vt t,
      sem_VAL ht vt ->
      sem_val vt = t ->
      adequate (fun _ => attribute_rel)(parse_attribute_content t)
        (proj1_sig (parse_attribute_content_rel ht)) data s.
Proof. intros. destruct parse_attribute_content_rel. eauto. Qed.


Definition parse_radius_attribute_rel :
  {code | forall data vs, adequate (fun _ => attribute_rel) parse_radius_attribute code data vs}.
  eapply exist. intros data vs. unfold parse_radius_attribute.
  repeat step. eapply be_u8_adequate. eapply verify_adequate.
  2 : eapply be_u8_adequate. clean_up. intros vy x s [P2 P1]. subst.
  instantiate (1 := fun vy => EBin ELe (Const (ENat 2)) (EUna EVal (Var vy))).
  eexists. split; repeat econstructor; eauto. clean_up.
  destruct H0 as [[P1 P3] P2]. subst.
  eapply map_parser_adequate. eapply consequence_adequate. step.
  intros. repeat clean_up. auto.
  intros. eapply (parse_attribute_content_adequate (Var vres)); repeat econstructor; eauto.
Defined.

Lemma parse_radius_attribute_adequate : forall data vs,
    adequate (fun _ => attribute_rel) parse_radius_attribute (proj1_sig parse_radius_attribute_rel) data vs.
Proof. intros. destruct parse_radius_attribute_rel. eauto. Qed.
