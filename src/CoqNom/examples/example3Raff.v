From stdpp Require Import numbers.
From SepLogic Require Import SepSet.
From Examples Require Import example2 example3.
From FreeMonad Require Import FreeMonad.


Section PHOAS.

(* =var= *)
Context {var : Type -> Type}.
(* =end= *)

(* =VAL= *)
Inductive VAL : Type -> Type :=
| Var : forall {X}, var X -> VAL X
| Const : N -> VAL N
| Add : VAL N -> VAL N -> VAL N
| Sub : VAL N -> VAL N -> VAL N
| Le : VAL N -> VAL N -> VAL bool
| Lt : VAL N -> VAL N -> VAL bool
| Len : VAL span -> VAL N
| Pair : forall {X Y}, VAL X -> VAL Y -> VAL (X * Y)
| Fst : forall {X Y}, VAL (X * Y) -> VAL X
| Snd : forall {X Y}, VAL (X * Y) -> VAL Y
| ToU32 : VAL octet -> VAL octet -> VAL octet -> VAL octet -> VAL N.
(* =end= *)

(* =Expr= *)
Inductive Expr : Type -> Type :=
| Val : forall {X}, VAL X -> Expr X
| LetIn : forall {X}, Expr X -> forall {Y}, (var X -> Expr Y) -> Expr Y
| IfThenElse: VAL bool -> forall {X}, Expr X -> Expr X -> Expr X
| Take : VAL N -> Expr span
| Read : VAL span -> VAL N -> Expr octet
| Length : Expr N
| Fail : forall {X}, Expr X.
(* =end= *)

End PHOAS.

Notation "'let%' v ':=' e 'in' k" := (LetIn e (fun v => k))(at level 50).
Notation "'If' b 'Then' et 'Else' ef" := (IfThenElse b et ef)(at level 50).
Notation "b0 '<!' b1" := (Lt b0 b1)(at level 30).
Notation "b0 '<=!' b1" := (Le b0 b1)(at level 30).
Notation "n0 '+!' n1" := (Add n0 n1)(at level 25, left associativity).
Notation "n0 '-!' n1" := (Sub n0 n1)(at level 25, left associativity).
Notation "'(!' a ',' b ')'" := (Pair a b)(at level 25, left associativity).

Section sem_PHOAS.

(* =ID= *)
Definition ID (X : Type) := X.
(* =end= *)

Definition lookup_default (data : data) n default :=
  match lookup n data with
  | Some v => v
  | None => default
  end.

(* =sem_VAL= *)
Inductive sem_VAL : forall {X}, @VAL ID X -> ID X -> Prop :=
(* =end= *)
| sem_Const : forall n, sem_VAL (Const n) n
(* =sem_Add= *)
| sem_Add : forall vm m vn n,
    sem_VAL vm m ->
    sem_VAL vn n ->
    sem_VAL (Add vm vn) (m + n)
(* =end= *)
| sem_Sub : forall vm m vn n,
    sem_VAL vm m ->
    sem_VAL vn n ->
    sem_VAL (Sub vm vn) (m - n)
| sem_Le : forall vm vn m n,
    sem_VAL vm m ->
    sem_VAL vn n ->
    sem_VAL (Le vm vn) (m <=? n)
| sem_Lt : forall vm vn m n,
    sem_VAL vm m ->
    sem_VAL vn n ->
    sem_VAL (Lt vm vn) (m <? n)
| sem_Len : forall vs s,
    sem_VAL vs s ->
    sem_VAL (Len vs) (len s)
| sem_Pair : forall X Y va (a : ID X) vb (b : ID Y),
    sem_VAL va a ->
    sem_VAL vb b ->
    sem_VAL (Pair va vb) (a,b)
| sem_Fst : forall X Y v (a : ID X) (b : ID Y),
    sem_VAL v (a, b) ->
    sem_VAL (Fst v) a
| sem_Snd : forall X Y v (a : ID X) (b : ID Y),
    sem_VAL v (a, b) ->
    sem_VAL (Snd v) b
| sem_ToU32 : forall va vb vc vd a b c d,
    sem_VAL va a ->
    sem_VAL vb b ->
    sem_VAL vc c ->
    sem_VAL vd d ->
    sem_VAL (ToU32 va vb vc vd) (to_u32 a b c d)
| sem_Var : forall X (v : ID X), sem_VAL (Var v) v.

(* =sem_Expr= *)
Inductive sem_Expr {data : list N} :
  span -> forall {X}, @Expr ID X -> option (ID X * span) -> Prop
(* =end= *)
:=
| sem_Val : forall s X (v :VAL X) res,
    sem_VAL v res ->
    sem_Expr s (Val v) (Some (res, s))
| sem_LetInF : forall X ex Y (k : X -> Expr Y) s,
    sem_Expr s ex None ->
    sem_Expr s (LetIn ex k) None
| sem_LetInS : forall X ex Y (k : X -> Expr Y) s v sv res,
    sem_Expr s ex (Some (v, sv)) ->
    sem_Expr sv (k v) res ->
    sem_Expr s (LetIn ex k) res
| sem_IfThenElseT : forall vb X (et ee : Expr X) res s,
    sem_VAL vb true ->
    sem_Expr s et res ->
    sem_Expr s (IfThenElse vb et ee) res
| sem_IfThenElseF : forall vb X (et ee : Expr X) res s,
    sem_VAL vb false ->
    sem_Expr s ee res ->
    sem_Expr s (IfThenElse vb et ee) res

(* =sem_Take= *)
| sem_Take : forall s vn n,
    sem_VAL vn n ->
    sem_Expr s (Take vn) (Some ({| pos := pos s; len := n |},
                                {| pos := pos s + n; len := len s - n |}))
(* =end= *)

(* =sem_Read= *)
| sem_Read : forall s vrange range vn n v default,
    sem_VAL vrange range ->
    sem_VAL vn n ->
    lookup_default data (pos range + n) default = v ->
    sem_Expr s (Read vrange vn) (Some (v, s))
(* =end= *)

| sem_Length : forall s, sem_Expr s Length (Some (len s, s))
| sem_Fail : forall X s, sem_Expr s (Fail : Expr X) None.

End sem_PHOAS.

(* =span_data_wf= *)
Definition span_data_wf (data : list N) (s : span) :=
    pos s + len s <= length data.
(* =end= *)

Definition adequate {X Y} (R : X -> Y -> Prop) (d : Decodeur X) (e : Expr Y) (data : list N) :=
  forall s res,
    span_data_wf data s ->
    @sem_Expr data s Y e res ->
    match res with
    | None => eval d data s = None
    | Some (v, t) => ∃ r, eval d data s = Some (r, t) /\ R r v
    end.

Axiom adequacy_pure : forall X e (Q : X -> Prop),
    {{ emp }} e {{ v; ⌜Q v⌝ }} ->
    forall data (v : X) s' s,
      eval e data s = Some (v, s') ->
      Q v.

Lemma adequacy_pure_PHOAS :
  forall X Q (e : Decodeur X) (h : Expr X),
    {{ emp }} e {{ v; ⌜Q v⌝ }} ->
    forall data,
      adequate eq e h data ->
      forall vv s sres,
        @sem_Expr data s X h (Some (vv, sres)) ->
        span_data_wf data s ->
        Q vv.
Proof.
  intros X Q e h TRIPLE data ADE vv s sres SEM WF.
  eapply ADE in SEM as [r [EVAL EQ]]; eauto. subst.
  eapply adequacy_pure; eauto.
Qed.

Ltac simpl_existT :=
  repeat match goal with
         | H : existT _ _ = existT _ _ |- _ =>
             repeat eapply Eqdep.EqdepTheory.inj_pair2 in H
    end.

Ltac next_step H := inversion H; subst; simpl_existT; subst; clear H.

Ltac head t :=
  match t with
  | ?t' _ => head t'
  | _ => t
  end.

Ltac head_constructor t :=
  let t' := head t in is_constructor t'.

Lemma sem_VAL_inj : forall X (v : VAL X) a b,
    sem_VAL v a ->
    sem_VAL v b ->
    a = b.
Proof.
  Ltac ind_inj IH :=
    match goal with
    | H : sem_VAL ?t _ |- _ =>
        head_constructor t; next_step H
    | H0 : sem_VAL ?t _, H1 : sem_VAL ?t _ |- _ =>
        injection (IH _ t _ _ H0 H1); clear H0; clear H1
    | H0 : sem_VAL ?t _, H1 : sem_VAL ?t _ |- _ =>
        eapply (IH _ t _ _ H0) in H1
    end.
  fix IH 2.
  destruct v; intros; repeat ind_inj IH; intros; simpl_existT; subst; reflexivity.
Qed.

Ltac sem_VAL_unif :=
  match goal with
  | H : sem_VAL ?t _, H0 : sem_VAL ?t _ |- _ => eapply (sem_VAL_inj _ t _ _ H) in H0
  end.

(* Ltac inj_val := *)
(*   match goal with *)
(*   | H : VNat _ = VNat _ |- _ => injection H; intros; clear H *)
(*   | H : VSpan _ = VSpan _ |- _ => injection H; intros; clear H *)
(*   | H : VBool _ = VBool _ |- _ => injection H; intros; clear H *)
(*   | H : VPair _ _ = VPair _ _ |- _ => injection H; intros; clear H *)
(*   end. *)

Ltac VAL_unif := repeat sem_VAL_unif.

Open Scope free_monad_scope.

Axiom run_bind_fail : forall s data X Y e (k : X -> Decodeur Y),
    eval e data s = None ->
    eval (let! v := e in k v) data s = None.

Lemma bind_adequate :
  forall data (X X0 Y Y0 : Type) R R0 (e : Decodeur X) (ke : X -> Decodeur Y)
    (h : Expr X0) (kh : X0 -> Expr Y0),
    adequate R0 e h data ->
    (forall res vres, R0 res vres -> adequate R (ke res) (kh vres) data) ->
    adequate R (let! v := e in ke v) (let% v := h in kh v) data.
Proof.
  unfold adequate.
  intros data X X0 Y Y0 R R0 e ke h kh SEME SEMK s res WF SEM.
  next_step SEM.
  - eapply SEME in H2 as P1; auto.
    eapply run_bind_fail. auto.
  - eapply SEME in H3 as [r [P0 R0r]]; auto.
    eapply SEMK in H6. destruct res.
    + destruct p. destruct H6 as [r0 [EVAL Rr0]]. exists r0. split; auto.
      admit.
    + admit.
    + eauto.
    + admit.
Admitted.


Lemma ret_adequate :
  forall Y (va : VAL Y) (X : Type) (R : X -> Y -> Prop) a (v : X) data,
    sem_VAL va a ->
    R v a ->
    adequate R (ret v) (Val va) data.
Proof.
  unfold adequate.
  intros Y va X R a v data SEMA RA s res WF SEM.
  next_step SEM. VAL_unif. subst. exists v. split; auto.
Qed.

Definition span_eq_take data n (s0 s1 : span) : Prop :=
  s0 = s1 /\ span_data_wf data s1 /\ len s1 = n.

Lemma take_adequate : forall (hn : VAL N) data (n : N),
    sem_VAL hn n ->
    adequate (span_eq_take data n) (take n)
      (let% len := Length in
       IfThenElse (Le hn (Var len))
         (Take hn)
         Fail) data.
Proof.
  intros hn data n VALN s res WF SEM.
  next_step SEM.
  - next_step H2.
  - next_step H6.
    + next_step H3. next_step H8. next_step H4. next_step H5.
      simpl in *. repeat VAL_unif. subst.
      simpl. unfold example2.bind. unfold takeM.
      eexists. rewrite H1. split. reflexivity.
      repeat split. unfold span_data_wf in *. simpl.
      eapply N.leb_le in H1. simpl in *. lia.
    + next_step H8. next_step H4. next_step H5. next_step H3.
      repeat VAL_unif. subst.
      simpl. unfold example2.bind. unfold takeM.
      rewrite H1. reflexivity.
Qed.


Lemma lookup_lt : forall pos (data : data),
    pos < length data ->
    exists v, lookup pos data = Some v.
Proof.
  induction pos using N.peano_ind; simpl; intros data LT.
  - destruct data; simpl in *; intros.
    + exfalso. eapply N.nlt_0_r. eexact LT.
    + rewrite lookup_equation_2. exists o. reflexivity.
  - destruct data; simpl in *.
    + exfalso. eapply N.nlt_0_r. eexact LT.
    + rewrite length_equation_2 in LT. eapply N.succ_lt_mono in LT.
      eapply IHpos in LT. destruct LT. rewrite <- N.succ_pos_spec.
      rewrite lookup_equation_3. rewrite N.succ_pos_spec. rewrite N.pred_succ.
      exists x. auto.
Qed.


Lemma lookup_nth : forall pos (data : data) default,
    pos < length data ->
    lookup pos data = Some (lookup_default data pos default).
Proof.
  induction pos using N.peano_ind; simpl; intros data default LT.
  - destruct data; simpl in *; intros.
    + exfalso. eapply N.nlt_0_r. eexact LT.
    + rewrite lookup_equation_2. reflexivity.
  - destruct data; simpl in *.
    + exfalso. eapply N.nlt_0_r. eexact LT.
    + rewrite length_equation_2 in LT. eapply N.succ_lt_mono in LT.
      eapply IHpos in LT. rewrite <- N.succ_pos_spec.
      rewrite lookup_equation_3. rewrite N.succ_pos_spec. rewrite N.pred_succ.
      erewrite LT.
      f_equal. unfold lookup_default. rewrite <- N.succ_pos_spec.
      rewrite lookup_equation_3. rewrite N.succ_pos_spec. rewrite N.pred_succ.
      reflexivity.
Qed.

Lemma read_adequate : forall hs hn data (n n0 : N) s,
    span_eq_take data n0 s s ->
    sem_VAL hs s ->
    sem_VAL hn n ->
    adequate eq (read s n) (IfThenElse (Lt hn (Len hs)) (Read hs hn) Fail) data.
Proof.
  intros hs hn data n n0 s RS ADES ADEN s0 res WF SEM.
  next_step SEM.
  - next_step H3. next_step H4. next_step H6. repeat VAL_unif. subst. simpl in *.
    destruct RS as [P0 [P1 P2]]. subst.
    unfold example2.bind, readM. rewrite H1. eapply N.ltb_lt in H1.
    rewrite (lookup_nth (pos range + n1) data default).
    eexists. split; auto. unfold span_data_wf in P1. lia.
  - next_step H6. next_step H3. next_step H4. repeat VAL_unif. subst. simpl in *.
    destruct RS as [P0 [P1 P2]]. subst.
    unfold example2.bind, readM. rewrite H1. reflexivity.
Qed.

Lemma read2_adequate : forall hs hn data (n n0 : N) s,
    span_eq_take data n0 s s ->
    sem_VAL hs s ->
    sem_VAL hn n ->
    n < n0 ->
    adequate eq (read s n) (Read hs hn) data.
Proof.
  intros hs hn data n n0 s RS ADES ADEN LT s0 res WF SEM.
  next_step SEM.
  repeat VAL_unif. subst. simpl. unfold example2.bind, readM. eapply N.ltb_lt in LT.
  destruct RS as [P0 [P1 P2]]. subst.
  unfold span_data_wf in *. simpl in *. rewrite LT. eapply N.ltb_lt in LT.
  rewrite (lookup_nth (pos range + n1) data default).
  eexists. split; auto. lia.
Qed.

Lemma ite_adequate : forall hb data X Y R (b : bool) (et : Decodeur X) (ht : Expr Y) ef hf,
    sem_VAL hb b ->
    (b = true -> adequate R et ht data) ->
    (b = false -> adequate R ef hf data) ->
    adequate R (if b then et else ef) (IfThenElse hb ht hf) data.
Proof.
  intros hb data X Y R b et ht ef hf EQ ADET ADEF s res WF SEM.
  subst. next_step SEM.
  - repeat VAL_unif. subst. simpl. eapply ADET; auto.
  - repeat VAL_unif. subst. simpl. eapply ADEF; auto.
Qed.

Lemma fail_adequate : forall data X Y R,
    adequate R (fail : Decodeur X) (Fail : Expr Y) data.
Proof. intros data X Y R s res WF SEM. next_step SEM. reflexivity. Qed.

Ltac Pos_is_literal p :=
  match p with
  | xO ?p  => Pos_is_literal p
  | xI ?p => Pos_is_literal p
  | xH => idtac
  end.

Ltac N_is_literal n :=
  match n with
  | N0 => idtac
  | Npos ?p => Pos_is_literal p
  end.

Ltac what_is e k :=
  match e with
  | ?e => N_is_literal e; k (@Const ID e)
  | _ =>
      match goal with
      | H : sem_VAL ?v e |- _ => k v
      | H : ?v = e |- _ => is_var e; k (@Var ID v)
      | H : e = ?v |- _ => is_var e; k (@Var ID v)
      end
  (* | H : sem_val ?v = ?e |- ?e => is_var e; k (@Var var v) *)
  (* | ?e => is_var e; k (@Var _ var e) *)
  | ?l <=? ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@Le ID l r)))
  | ?l <? ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@Lt ID l r)))
  | ?l + ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@Add ID l r)))
  | ?l - ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@Sub ID l r)))
  | to_u32 ?a ?b ?c ?d =>
      what_is a ltac:(fun a =>
       what_is b ltac:(fun b =>
        what_is c ltac:(fun c =>
                          what_is d ltac:(fun d => k (@ToU32 ID a b c d)))))
  | ?e => is_var e; k (@Var ID _ e)
  end.

Ltac clean_up :=
  match goal with
  | H : span_eq_take _ _ _ _ |- _ =>
      let P0 := fresh "P" in
      let P1 := fresh "P" in
      let P2 := fresh "P" in
      destruct H as [P0 [P1 P2]]
  end.

Ltac step := repeat clean_up; subst;
  match goal with
  | |- adequate _ (let! _ := _ in _) _ _ =>
        eapply bind_adequate; [ idtac | intros  ]
  | |- adequate _ (take ?e) _ _ =>
      what_is e ltac:(fun v => eapply (take_adequate v)); repeat econstructor
  | |- adequate _ (read ?s ?n) _ _ =>
      what_is s ltac:(fun s => what_is n ltac:(fun n => eapply (read2_adequate s n)));
      [repeat split; eauto | repeat econstructor | repeat econstructor | lia]
  | |- adequate _ (read ?s ?n) _ _ =>
      what_is s ltac:(fun s => what_is n ltac:(fun n => eapply (read_adequate s n)));
      [repeat split; eauto | repeat econstructor | repeat econstructor]
  | |- adequate _ (if ?b then ?et else ?ef) _ _ =>
      what_is b ltac:(fun s => eapply (ite_adequate s));
      repeat econstructor; eauto; intros
  | |- adequate _ fail _ _ => eapply fail_adequate
  | |- adequate _ (ret ?v) _ _ =>
      what_is v ltac:(fun v => eapply (ret_adequate _ v)); repeat econstructor; eauto
  end.

Ltac StartDF :=
  eapply exist; intros;
  match goal with
  | |- adequate _ ?f _ _ =>
      let v := head f in
      unfold f
  end.

Local Hint Extern 3 (adequate _ _ _ _) => (* repeat  *)step : core.

Definition decode_next_DF_example :
  {code | forall data, adequate eq decode_next code data}.
Proof.
  what_is 1 ltac:(fun v => pose (H := v)).
  eapply exist. intro. unfold decode_next.
  eapply bind_adequate.
  - eapply (take_adequate (Const 1)); constructor.
  - intros res vres [P0 [P1 P2]]. subst.
    eapply (read_adequate (Var vres) (Const 0)); constructor; auto.
Defined.

Definition decode_next_DF :
  {code | forall data, adequate eq decode_next code data}.
Proof. StartDF; auto. Defined.

Lemma decode_first_eq : proj1_sig decode_next_DF_example = proj1_sig decode_next_DF.
Fail reflexivity. Abort.

Compute (proj1_sig decode_next_DF).

Lemma decode_next_adequate :
  forall data, adequate eq decode_next (`decode_next_DF) data.
Proof. intros. destruct (decode_next_DF) as [x P]. eapply P. Qed.

Ltac FMfirst :=
  match goal with
  | |- adequate _ decode_next _ _ => eapply decode_next_adequate
  | |- _ => step
  end.

Local Hint Extern 3 (adequate _ decode_next _ _) => eapply decode_next_adequate : core.

Definition decode_u32_DF :
  { code | forall data, adequate eq decode_u32 code data}.
Proof. StartDF; auto. Defined.

Compute (proj1_sig decode_u32_DF).

Lemma decode_u32_adequate :
  forall data, adequate eq decode_u32 (`decode_u32_DF) data.
Proof. intros. destruct (decode_u32_DF) as [x P]. eapply P. Qed.

Ltac FMU32 :=
  match goal with
  | |- adequate _ decode_u32 _ _ => eapply decode_u32_adequate
  | |- _ => FMfirst
  end.

Local Hint Extern 3 (adequate _ decode_u32 _ _) => eapply decode_u32_adequate : core.

Definition RpacketSSH (s : packet_SSH) (v : (N * N) * (span * span)) :=
  v.1.1 = packet_length s /\
  v.1.2 = padding_length s /\
  v.2.1 = payload s /\
  v.2.2 = mac s.

Definition decode_packet_SSH_sig :
  { code | forall data, adequate RpacketSSH decode_packet_SSH code data}.
Proof.
  StartDF. repeat FMU32. repeat clean_up.
  eapply bind_adequate. step. intros. clean_up.
  eapply (ret_adequate _ (Pair (Pair (Var vres) (Var vres0)) (Pair (Var vres1) (Var vres3)))).
  repeat econstructor.
  repeat split; eauto.
Defined.

Compute (proj1_sig decode_packet_SSH_sig).
