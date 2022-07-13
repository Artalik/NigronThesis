From Formalisation Require Import String Span.
From Formalisation Require Import (* Axioms *) Nom (* ProgramLogic adequacy *) Monotone FuelMono.

From Formalisation Require Import combinator multi sequence bin_combinators.
From Formalisation Require Import ProgramLogic adequacy.
From Raffinement Require Import PHOAS.

(* From Equations Require Import Equations. *)
Open Scope N_scope.

Definition span_data_wf (data : list nat8) (s : span) :=
    pos s + len s < lengthN data.

Definition adequate {X Y} (R : span -> X -> Y -> Prop) (n : NomG X) (e : PHOASV Y)
  (data : list nat8) (s : span) :=
  span_data_wf data s ->
  forall res,
    sem_PHOAS data s e res ->
    match res with
    | None => exists fuel, run fuel n data s = NoRes
    | Some (v, t) => exists r, R t r (sem_val v) /\ exists fuel, run fuel n data s = Res (t, r)
    end.

Lemma adequacy_pure_PHOAS {X Y} :
  forall (d : NomG X) (e : PHOASV Y)  (R : span -> X -> Y -> Prop) data s,
    adequate R d e data s ->
    span_data_wf data s ->
    forall v t,
      sem_PHOAS data s e (Some (v, t)) ->
      forall (Q : X -> Prop) (P : Y -> Prop),
        {{ emp }} d {{ v; ⌜Q v⌝ }} ->
        (forall x, Q x -> R t x (sem_val v) -> P (sem_val v)) ->
        P (sem_val v).
Proof.
  unfold adequate. intros e h R data s ADE WF vv sres SEM Q P TRIPLE R_OK.
  eapply ADE in SEM as [r [Rr [fuel RUN]]].
  eapply R_OK; eauto. eapply adequacy_pure; eauto. auto.
Qed.

Lemma adequacy_pure_PHOAS_disjoint `{Foldable X} `{Foldable Y}:
  forall (e : NomG (X span)) (h : PHOASV (Y span)),
    {{ emp }} e {{ v; ⌜all_disjointM v⌝ }} ->
    forall (R : span -> X span -> Y span -> Prop) data s,
      adequate R e h data s ->
      forall vv sres,
        sem_PHOAS data s h (Some (vv,sres)) ->
        span_data_wf data s ->
        (forall x, all_disjointM x -> R sres x (sem_val vv) -> all_disjointM (sem_val vv)) ->
        all_disjointM (sem_val vv).
Proof.
  unfold adequate. intros e h TRIPLE R data s ADE vv sres SEM WF R_OK.
  eapply adequacy_pure_PHOAS; eauto.
Qed.

Ltac simpl_existT :=
  repeat match goal with
         | H : existT _ _ = existT _ _ |- _ =>
             repeat eapply Eqdep.EqdepTheory.inj_pair2 in H
    end.

Ltac next_step H := inversion H; subst; simpl_existT; subst; clear H.

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

Ltac VAL_unif := repeat sem_VAL_unif. (* repeat inj_val. *)

Lemma ret_adequate data s :
  forall Y (va : VAL Y) (X : Type) (R : span -> X -> Y -> Prop) a (v : X),
    sem_VAL va a ->
    R s v (sem_val a) ->
    adequate R (ret v) (Val va) data s.
Proof.
  unfold adequate.
  intros Y va X R a v SEMA RA WF res SEM.
  next_step SEM. VAL_unif. subst. eexists. repeat split. eauto. exists O. reflexivity.
Qed.

Lemma cstruct_adequate :
  forall ty constr l Y (X : Type) (v : X) data s,
    adequate (fun _ _ _ => True%type) (ret v) (Cstruct ty constr l : PHOAS Y) data s.
Proof.
  unfold adequate.
  intros ty constr l Y X v data s WF res SEM.
  next_step SEM. exists v. split; auto. exists O. reflexivity.
Qed.

Lemma bind_adequate data s :
  forall (X Y X0 Y0 : Type) T R (e : NomG X) (ke : X -> NomG Y)
    (h : PHOASV X0) (kh : PHOAS.val X0 -> PHOASV Y0),
    adequate T e h data s ->
    (forall vres r t, T t r (sem_val vres) -> adequate R (ke r) (kh vres) data t) ->
    adequate R (let! v := e in ke v) (let% v := h in kh v) data s.
Proof.
  unfold adequate.
  intros X Y X0 Y0 T R e ke h kh SEME SEMK WF res SEM.
  next_step SEM.
  - eapply SEME in H3 as [x [Rx [fuel P1]]]; auto.
    eapply SEMK in H6. destruct res as [[v0 t]|].
    + destruct H6 as [x0 [Rx0 [fuel0 RUN]]]. exists x0.
      repeat split; auto. eapply run_bind_weak; eauto.
    + destruct H6 as [fuel0 RUN]. eapply run_bind_weak; eauto.
    + eauto.
    + eapply run_mono in P1 as [P1 P2]. unfold span_data_wf in *. lia.
  - eapply SEME in H2 as [fuel P1]; auto.
    exists fuel. eapply run_bind_fail. auto.
Qed.

Lemma consequence_adequate :
  forall (X Y : Type) (R T : span -> X -> Y -> Prop) (e : NomG X) (h : PHOASV Y) data s,
    adequate R e h data s ->
    (forall t v hv, R t v hv -> T t v hv) ->
    adequate T e h data s.
Proof.
  intros X Y R T e h data s ADE IMPL WF res SEM.
  eapply ADE in SEM; auto. destruct res as [[v p]| ]; auto.
  destruct SEM as [r [Rr [fuel RUN]]].
  exists r. split; auto. exists fuel. auto.
Qed.

Definition length_spec s t x y := s = t /\ x = y /\ x = len t.

Lemma length_adequate : forall data s, adequate (length_spec s) length Length data s.
Proof.
  intros data s WF res SEM. next_step SEM.
  simpl. eexists. split. repeat split; econstructor. exists O. reflexivity.
Qed.

Definition span_eq data (s0 s1 : span) := s0 = s1 /\ span_data_wf data s0.

Definition span_eq_take data s n t (s0 s1 : span) : Prop :=
  span_eq data s0 s1 /\ len s0 = n /\ len t = len s - n.

Lemma take_verif_adequate data s : forall (hn : VAL N) (n : N) vn,
    sem_VAL hn vn ->
    sem_val vn = n ->
    adequate (span_eq_take data s n) (take n)
      (let% len := Length in
       If hn <=! Var len
         Then Take hn
         Else Fail) data s.
Proof.
  intros hn n vn VALN EQ WF res SEM.
  next_step SEM.
  - next_step H3. next_step H6.
    + next_step H3. next_step H10. next_step H9. next_step H7.
      simpl in *. repeat VAL_unif. subst. simpl.
      eexists. repeat split.
      * unfold span_data_wf. simpl in *.
        unfold span_data_wf in *.
        eapply N.leb_le in H1. lia.
      * eapply O.
      * unfold_MonSem. unfold run_take. unfold_MonSem.
        rewrite H1. reflexivity.
    + next_step H7. next_step H3. next_step H8. next_step H9.
      repeat VAL_unif. subst.
      exists O. unfold run. simpl. unfold_MonSem. unfold run_take. unfold_MonSem.
      rewrite H1. reflexivity.
  - next_step H2.
Qed.

Lemma take_adequate data s : forall (hn : VAL N) (n : N) vn,
    sem_VAL hn vn ->
    sem_val vn = n ->
    n <= len s ->
    adequate (span_eq_take data s n) (take n) (Take hn) data s.
Proof.
  intros hn n vn VALN EQ LE WF res SEM.
  next_step SEM. VAL_unif. subst. simpl in *.
  eexists. repeat split.
  - unfold span_data_wf in *. simpl. lia.
  - apply O.
  - unfold_MonSem. unfold run_take. unfold_MonSem.
    eapply N.leb_le in LE. rewrite LE. reflexivity.
Qed.

Lemma fail_adequate : forall data s X Y (R : span -> X -> Y -> Prop),
    adequate R fail Fail data s.
Proof.
  intros data s X Y R WF res SEM.
  next_step SEM. exists O. reflexivity.
Qed.

Lemma lookupN_lt : forall pos X (data : list X),
    pos < lengthN data ->
    forall s v, lookupN data pos s = Res (s,nth (N.to_nat pos) data v).
Proof.
  induction pos using N.peano_ind; simpl; intros X data LT s v.
  - induction data; simpl in *; intros.
    + exfalso. eapply N.nlt_0_r. eexact LT.
    + rewrite lookupN_equation_2. reflexivity.
  - destruct data; simpl in *.
    + exfalso. eapply N.nlt_0_r. eexact LT.
    + eapply N.succ_lt_mono in LT. eapply IHpos in LT.
      rewrite <- N.succ_pos_spec. rewrite lookupN_equation_3.
      rewrite N.succ_pos_spec. rewrite N.pred_succ.
      rewrite N2Nat.inj_succ. eapply LT.
Qed.

Definition read_spec (s t : span) (x0 x1 : nat8) := s = t /\ x0 = x1.

Lemma read_verif_adequate data s : forall ht hn vn (n n0 : N) vt t,
    span_data_wf data t ->
    sem_VAL ht vt ->
    sem_val vt = t ->
    sem_VAL hn vn ->
    sem_val vn = n ->
    adequate (read_spec s) (read t n)
      (If hn <! EUna ELen ht
         Then
         Read ht hn
         Else Fail) data s.
Proof.
  intros ht hn vn n n0 vt t RS VALR ADES ADEN VALn WF res SEM.
  next_step SEM.
  - next_step H3. next_step H6. next_step H10. next_step H9. next_step H10.
    repeat VAL_unif. subst. simpl in *.
    do 2 eexists. repeat split.
    exists O. unfold run_read. unfold_MonSem.
    rewrite H1. erewrite lookupN_lt. reflexivity.
    unfold span_data_wf in RS. eapply N.ltb_lt in H1. lia.
  - next_step H6. next_step H3. next_step H9. next_step H8. next_step H7.
    repeat VAL_unif. subst.
    exists O. simpl. unfold run_read. unfold_MonSem. rewrite H1. reflexivity.
Qed.

Lemma read_adequate data s : forall ht hn vn (n : N) vt t,
    span_data_wf data t ->
    sem_VAL ht vt ->
    sem_val vt = t ->
    sem_VAL hn vn ->
    sem_val vn = n ->
    n < len t ->
    adequate (read_spec s) (read t n) (Read ht hn) data s.
Proof.
  intros ht hn vn n vt t RS VALr ADES ADEN VALn LT WF res SEM.
  next_step SEM.
  repeat VAL_unif. subst. eexists. repeat split. simpl in *.
  exists O. unfold run_read. eapply N.ltb_lt in LT. rewrite LT.
  unfold_MonSem. erewrite lookupN_lt. reflexivity.
  eapply N.ltb_lt in LT. unfold span_data_wf in RS. lia.
Qed.

Lemma alt_adequate data s : forall X Y R (e0 : NomG X) e1 (h0 : PHOASV Y) h1,
    adequate R e0 h0 data s ->
    adequate R e1 h1 data s ->
    adequate R (alt e0 e1) (Alt h0 h1) data s.
Proof.
  intros X Y R e0 e1 h0 h1 ADE0 ADE1 WF res SEM.
  next_step SEM.
  - eapply ADE0 in H2 as [x [RX [fuel0 P0]]]; auto.
    exists x. repeat split; auto. exists fuel0.
    simpl. unfold run_alt. unfold_MonSem. rewrite P0. reflexivity.
  - eapply ADE0 in H4 as [fuel0 P0]; auto. destruct res as [[v p]|].
    + eapply ADE1 in H5 as [x [ROK [fuel1 P1]]]; auto.
      eexists. repeat split; eauto.
      exists (Nat.max fuel1 fuel0). simpl.
      unfold run_alt. unfold_MonSem. eapply run_fuel_mono in P0.
      erewrite P0. eapply run_fuel_mono in P1.
      erewrite P1. reflexivity. auto. lia. auto. lia.
    + eapply ADE1 in H5 as [fuel1 P1]; auto. exists (Nat.max fuel1 fuel0).
      simpl. unfold run_alt. unfold_MonSem.
      eapply run_fuel_mono in P0. erewrite P0.
      eapply run_fuel_mono in P1. erewrite P1. reflexivity. auto. lia. auto. lia.
Qed.

Definition local_spec {X Y} (R : X -> Y -> Prop) (s t : span) x y :=
  s = t /\ R x y.

Lemma peek_adequate data s : forall X Y R (e : NomG X) (h : PHOASV Y),
    adequate (fun _ => R) e h data s ->
    adequate (local_spec R s) (peek e) (Local (Const ENone) h) data s.
Proof.
  intros X Y R e h ADEE res WF SEM. next_step SEM.
  - next_step H4. next_step H2.
  - next_step H4. next_step H2.
  - eapply ADEE in H5 as [fuel RUN].
    exists fuel. simpl. unfold run_peek. unfold_MonSem. rewrite RUN. reflexivity. auto.
  - eapply ADEE in H5 as [x [Rr [fuel RUN]]].
    eexists. repeat split; eauto.
    exists fuel. simpl. unfold run_peek. unfold_MonSem. rewrite RUN. reflexivity. auto.
Qed.

Lemma scope_adequate data s : forall erange range X Y R (e : NomG X) (h : PHOASV Y) vr,
    adequate (fun _ => R) e h data range ->
    sem_VAL erange vr ->
    sem_val vr = range ->
    span_data_wf data range ->
    adequate (local_spec R s) (scope range e) (Local (EUna ESome erange) h) data s.
Proof.
  intros erange range X Y R e h vr ADEE VALR EQr WFR WF res SEM. next_step SEM.
  - next_step H4. next_step H7. VAL_unif. subst. simpl in *.
    eapply ADEE in H5 as [fuel RUN]. exists fuel.
    simpl. unfold run_scope. unfold_MonSem. rewrite RUN. reflexivity. eauto.
  - next_step H4. next_step H7. VAL_unif. subst. simpl in *.
    eapply ADEE in H5 as [x [Rx [fuel RUN]]]. exists x.
    repeat split; auto. exists fuel.
    unfold run_scope. unfold_MonSem. rewrite RUN. reflexivity. eauto.
  - next_step H4. next_step H7.
  - next_step H4. next_step H7.
Qed.

Fixpoint case_adequate {X Y} (R : span -> X -> Y -> Prop) (e : N -> NomG X)
  (c : case_switch Y) (l : list N) data s {struct c}: Prop :=
  match c in (case_switch T) return ((span -> X -> T -> Prop) -> Prop) with
  | LSnil p => fun R => forall (n : N), n ∉ l -> adequate R (e n) p data s
  | LScons n p c => fun R =>
      adequate R (e n) p data s /\ case_adequate R e c (n :: l) data s
  end R.

Lemma switch_adequate_bis data s : forall X Y R (cases : case_switch Y) n (e : N -> NomG X) hn vn l,
    sem_VAL hn vn ->
    sem_val vn = n ->
    n ∉ l ->
    case_adequate R e cases l data s ->
    adequate R (e n) (Switch hn cases) data s.
Proof.
  induction cases; simpl; intros.
  - intros res WF SEM. next_step SEM. next_step H9.
    repeat VAL_unif. subst. eapply H2; auto.
  - destruct H2 as [P0 P1]. intros res WF SEM. next_step SEM. next_step H8.
    + repeat VAL_unif. subst. eapply P0; auto.
    + repeat VAL_unif. subst. eapply IHcases.
      4 : eapply P1. eapply H. constructor. intro. inversion H0.
      subst. contradiction. subst. contradiction. auto.
      econstructor; eauto.
Qed.

Definition app {X Y} (e : X -> Y) (x : X): Y := e x.

Lemma switch_adequate : forall hn X Y (R : span -> X -> Y -> Prop) cases (e : N -> NomG X) n vn data s,
    sem_VAL hn vn ->
    sem_val vn = n ->
    case_adequate R e cases nil data s ->
    adequate R (e n) (Switch hn cases) data s.
Proof.
  intros. eapply switch_adequate_bis; eauto. intro P. inversion P.
Qed.

Lemma match_N_adequate data s : forall hn X Y (R : span -> X -> Y -> Prop) cases (e1 : NomG X) e2 n vn,
    sem_VAL hn vn ->
    sem_val vn = n ->
    case_adequate R (fun n => match n with
                              | 0 => e1
                              | Npos p => e2 p
                              end) cases nil data s ->
    adequate R (match n with
                | 0 => e1
                | Npos p => e2 p
                end) (Switch hn cases) data s.
Proof.
  intros.
  assert (match n with
          | 0 => e1
          | N.pos p0 => e2 p0
          end = app (fun n => match n with
                              | 0 => e1
                              | N.pos p0 => e2 p0
                              end) n) as P by auto.
  rewrite P. clear P.
  eapply switch_adequate; eauto.
Qed.

Lemma natN_switch_adequate_bis :
  forall X Y (R : span -> X -> Y -> Prop) cases p (n : natN p) hn vn (e1 : NomG X) e2 data l s,
    sem_VAL hn vn ->
    sem_val vn = (↓ n) ->
    ↓ n ∉ l ->
    case_adequate R (fun n => match n with
                              | N0 => e1
                              | N.pos p => e2 p
                              end) cases l data s ->
    adequate R (match SizeNat.val n with
                | N0 => e1
                | N.pos p => e2 p
                end) (Switch hn cases) data s.
Proof.
  intros X Y R cases p n hn vn e1 e2 data l s P0 P1 P2 case.
  assert (match ↓ n with
          | 0 => e1
          | N.pos p0 => e2 p0
          end = app (fun n => match n with
                              | 0 => e1
                              | N.pos p0 => e2 p0
                              end) (↓ n)) by auto.
  rewrite H. clear H.
  eapply switch_adequate_bis; eauto.
Qed.

Lemma natN_switch_adequate :
  forall p hn X Y (R : span -> X -> Y -> Prop) cases (n : natN p) vn (e1 : NomG X) e2 data s,
    sem_VAL hn vn ->
    sem_val vn = (↓ n) ->
    case_adequate R (fun n => match n with
                              | 0 => e1
                              | N.pos p => e2 p
                              end) cases nil data s ->
    adequate R (match SizeNat.val n with
                | 0 => e1
                | N.pos p => e2 p
                end) (Switch hn cases) data s.
Proof.
  intros. eapply natN_switch_adequate_bis; eauto. intro P. inversion P.
Qed.

Lemma LScons_adequate data s : forall n X Y (R : span -> X -> Y -> Prop) cases (e : N -> NomG X) h l,
    adequate R (e n) h data s ->
    case_adequate R e cases (n :: l) data s ->
    case_adequate R e (LScons n h cases) l data s.
Proof. simpl. intros. split; auto. Qed.

Lemma LSnil_adequate data s: forall X Y (R : span -> X -> Y -> Prop) (e : N -> NomG X) h l,
    (forall n, n ∉ l -> adequate R (e n) h data s) ->
    case_adequate R e (LSnil h) l data s.
Proof. simpl. intros. eapply H. eapply H0. Qed.

Lemma ite_adequate data s : forall hb X Y R vb (b : bool) (et : NomG X) (ht : PHOASV Y) ef hf,
    sem_VAL hb vb ->
    sem_val vb = b ->
    (b = true -> adequate R et ht data s) ->
    (b = false -> adequate R ef hf data s) ->
    adequate R (if b then et else ef) (If hb Then ht Else hf) data s.
Proof.
  intros hb X Y R vb b et ht ef hf VALb EQ ADET ADEF res WF SEM.
  subst. next_step SEM.
  - repeat VAL_unif. subst. eapply ADET; auto.
  - repeat VAL_unif. subst. eapply ADEF; auto.
Qed.


Definition compt_Some n {X Y} (R : span -> X -> Y -> Prop) (RX : N -> X -> Prop) (RY : N -> Y -> Prop) s x0 x1:=
  R s x0 x1 /\ RX n x0 /\ RY n x1.

Lemma repeat_Some_adequate_aux data s :
  forall hmax X Y (hb : VAL Y) (R : span -> X -> Y -> Prop) RX RY max e b he vb rb vmax start,
    sem_VAL hb vb ->
    sem_val vb = rb ->
    sem_VAL hmax vmax ->
    sem_val vmax = Some max ->
    compt_Some start R RX RY s b rb ->
    (forall hv rv v n s,
        sem_val hv = rv ->
        compt_Some n R RX RY s v rv ->
        n < max + start ->
        adequate (compt_Some (N.succ n) R RX RY) (e v) (he hv) data s) ->
    forall res,
      span_data_wf data s ->
      sem_PHOAS data s (Repeat hmax he hb) res ->
      match res with
      | None =>
          exists fuel, run fuel (repeat (Some max) e b) data s = NoRes
      | Some (v, t) =>
          exists r,
          R t r (sem_val v) /\
            exists fuel, run fuel (repeat (Some max) e b) data s = Res (t, r)
    end.
Proof.
  intros hmax X Y hb R RX RY max e b he vb rb vmax start VALb valb VALmax EQmax R'B IH res WF SEM.
  next_step SEM.
  - VAL_unif. subst. inversion EQmax.
  - VAL_unif. subst. simpl in *. injection EQmax. intro; subst. clear EQmax.
    clear VALmax VALb hb. revert b start R'B IH. induction H7.
    + intros. destruct R'B as [P0 [P1 P2]]. eexists. split. eauto. exists O. auto.
    + intros. eapply (IH _ _ _ start) in H as [r [Rr [fuel RUN]]].
      eapply IHsem_repeat_Some in Rr. destruct res as [[v p]|].
      * destruct Rr as [r0 [R0 [fuel0 RUN0]]]. subst.
        eexists. repeat split. eauto.
        exists (Nat.max fuel fuel0). rewrite N2Nat.inj_succ. unfold_MonSem.
        erewrite run_fuel_mono; eauto. simpl.
        erewrite repeat_some_fuel_mono. eapply RUN0.
        intros. erewrite run_fuel_mono; eauto. rewrite H. auto. reflexivity. lia.
        intro. rewrite H in RUN0. inversion RUN0. lia.
      * destruct Rr as [fuel0 RUN0].
        exists (Nat.max fuel fuel0). rewrite N2Nat.inj_succ.
        unfold_MonSem. erewrite run_fuel_mono; eauto. simpl.
        erewrite repeat_some_fuel_mono. eapply RUN0.
        intros. erewrite run_fuel_mono; eauto. rewrite H. auto. reflexivity. lia.
        intro. rewrite H in RUN0. inversion RUN0. lia.
      * unfold span_data_wf in *. eapply run_mono in RUN as [P2 P3]. lia.
      * intros. rewrite <- N.add_succ_comm in H1. eapply IH; eauto.
      * eauto.
      * eauto.
      * lia.
      * auto.
    + intros. eapply IH in H as [fuel RUN]; eauto.
      exists fuel. unfold_MonSem. rewrite N2Nat.inj_succ. rewrite RUN. reflexivity. lia.
Qed.

Lemma repeat_Some_adequate :
  forall hmax Y (hb : VAL Y) X (R : span -> X -> Y -> Prop) RX RY max e b he vb rb vmax data s,
    sem_VAL hb vb ->
    sem_val vb = rb ->
    sem_VAL hmax vmax ->
    sem_val vmax = Some max ->
    compt_Some 0 R RX RY s b rb ->
    (forall hv rv v n s,
        sem_val hv = rv ->
        compt_Some n R RX RY s v rv ->
        n < max ->
        adequate (compt_Some (N.succ n) R RX RY) (e v) (he hv) data s) ->
    adequate R (repeat (Some max) e b) (Repeat hmax he hb) data s.
Proof.
  intros. intros res WF SEM. eapply repeat_Some_adequate_aux; eauto.
  intros. eapply H4; eauto. lia.
Qed.

Lemma repeat_Some2_adequate : forall hn X Y (hb : VAL Y) n e b he vb rb vn (R : span -> X -> Y -> Prop) data s,
    sem_VAL hb vb ->
    sem_val vb = rb ->
    sem_VAL hn vn ->
    sem_val vn = n ->
    R s b rb ->
    (forall hv rv v t, sem_val hv = rv -> R t v rv -> adequate R (e v) (he hv) data t) ->
    adequate R (repeat (Some n) e b) (Repeat (EUna ESome hn) he hb) data s.
Proof.
  intros hn X Y hb n e b he vb rb vn R data s VALb valb VALn EQn R'B IH.
  subst. eapply repeat_Some_adequate; repeat econstructor; eauto.
  instantiate (1 := fun _ _ => True%type). simpl. trivial.
  instantiate (1 := fun _ _ => True%type). simpl. trivial.
  intros. eapply consequence_adequate. eapply IH; eauto.
  destruct H0. auto. intros. repeat split; auto.
Qed.

Lemma repeat_adequate data s : forall ho X Y (hb : VAL Y) (R : span -> X -> Y -> Prop) o e b he vb rb vo,
    sem_VAL hb vb ->
    sem_VAL ho vo ->
    sem_val vo = o ->
    sem_val vb = rb ->
    R s b rb ->
    (forall hv rv v t, sem_val hv = rv -> R t v rv -> adequate R (e v) (he hv) data t) ->
    adequate R (repeat o e b) (Repeat ho he hb) data s.
Proof.
  intros ho X Y hb R o e b he vb rb vo VALb VALn EQn' valb RB IH WF res SEM.
  subst. next_step SEM.
  - VAL_unif. subst. revert b RB. induction H7.
    + intros. eapply IH in H; eauto. destruct H as [fuel P0].
      do 2 eexists. repeat split; eauto. exists (S fuel).
      simpl. unfold_MonSem.
      erewrite run_fuel_mono; eauto. simpl. reflexivity.
    + intros. eapply IH in H; eauto. destruct H as [r [Rr [fuel RUN]]].
      subst. eapply IHsem_repeat_None in Rr; eauto.
      2 : instantiate (1 := Var ve); econstructor. destruct res as [[p v]|].
      * destruct Rr as [r0 [Rr0 [fuel0 RUN0]]].
        do 2 eexists. repeat split; eauto. exists (S (Nat.max fuel0 fuel)).
        simpl. unfold_MonSem. erewrite run_fuel_mono; eauto. simpl.
        simpl in RUN0. rewrite ret_neutral_right in RUN0.
        unfold_MonSem. eapply repeat_none_fuel_mono in RUN0.
        unfold_MonSem. erewrite RUN0. reflexivity.
        intros. eapply run_fuel_mono. eapply H. auto. lia. lia. lia. auto. lia.
      * destruct Rr as [fuel0 RUN0].
        simpl in RUN0. rewrite ret_neutral_right in RUN0.
        unfold_MonSem. destruct fuel0. inversion RUN0.
        destruct (match run (S fuel0) (e r) data p1 with
           | Res (s, x) =>
               (fix sem_repeat_none (n : nat) (x1 : X) {struct n} : MonSem X :=
                  match n with
                  | 0%nat => λ _ : span, NoFuel
                  | S n0 =>
                      λ s0 : span,
                        match
                          match run (S fuel0) (e x1) data s0 with
                          | Res (s1, x3) => sem_repeat_none n0 x3 s1
                          | NoRes => NoRes
                          | NoFuel => NoFuel
                          end
                        with
                        | Res (s1, v) => Res (s1, v)
                        | NoRes => Res (s0, x1)
                        | NoFuel => NoFuel
                        end
                  end) fuel0 x s
           | NoRes => NoRes
           | NoFuel => NoFuel
                  end). destruct x. inversion RUN0. inversion RUN0. inversion RUN0.
      * unfold span_data_wf in *. eapply run_mono in RUN as [P0 P1]. lia.
  - VAL_unif. subst. subst. eapply repeat_Some2_adequate; eauto.
    instantiate (2 := Const (ENat n)). repeat econstructor. reflexivity.
    eapply SRepeatS. repeat econstructor. eauto. auto.
Qed.

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

Ltac Bool_is_literal b :=
  match b with
  | true => idtac
  | false => idtac
  end.

Ltac String_is_literal s :=
  match s with
  | EmptyString => idtac
  | String _ ?s => String_is_literal s
  end.

Ltac is_None o :=
  match o with
  | None => idtac
  end.

Ltac is_Unit o :=
  match o with
  | tt => idtac
  end.

Ltac natN_is_literal n :=
  match n with
  | mk_natN _ _ _ => idtac
  end.

Ltac what_is e k :=
  match e with
  (* Const *)
  | ?e => N_is_literal e; k (@Const val _ (ENat e))
  | ?e => natN_is_literal e; k (@Const val _ (ENatN e))
  | ?e => Bool_is_literal e; k (@Const val _ (EBool e))
  | ?e => String_is_literal e; k (@Const val _ (EString e))
  | ?e => is_None e; k (@Const val _ ENone)
  | ?e => is_Unit e; k (@Const val _ EUnit)

  (* Var *)
  | _ =>
      match goal with
      | H : sem_VAL ?h ?v, H0 :sem_val ?v = e |- _  =>  is_var v; k h
      | H : sem_val ?v = e |- _  =>  is_var v; k (@Var val _ v)
      | H : e = sem_val ?v |- _  =>  is_var v; k (@Var val _ v)
      | H : string_get ?n ?s = Some e |- _ =>
          what_is n ltac:(fun n => what_is s ltac:(fun s => k (@EBin val _ _ _ EStringGet n s)))
      end
  | sem_val ?e =>
      match goal with
      | H : sem_VAL ?h e |- _ => is_var e; k h
      | |- _ => is_var e; k (@Var val _ e)
      end

  (* EBin *)
  | ?l + ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@EBin val _ _ _ EAdd l r)))
  | ?l - ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@EBin val _ _ _ ESub l r)))
  | ?l * ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@EBin val _ _ _ EMult l r)))
  | ?l / ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@EBin val _ _ _ EDiv l r)))
  | ?l `mod` ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@EBin val _ _ _ EMod l r)))
  | ?l =? ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@EBin val _ _ _ EEq l r)))
  | SizeNat.eqb ?l ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@EBin val _ _ _ EEq (EUna EVal l) (EUna EVal r))))
  | ?l <=? ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@EBin val _ _ _ ELe l r)))
  | ?l <? ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@EBin val _ _ _ ELt l r)))
  | ?l && ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@EBin val _ _ _ EAnd l r)))
  | ?l || ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@EBin val _ _ _ EOr l r)))
  | string_get ?n ?s => what_is n ltac:(fun n => what_is s ltac:(fun s => k (@EBin val _ _ _ EStringGet n s)))
  | (?l, ?r) => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@EBin val _ _ _ EPair l r)))
  | ?l ↑ ?r => what_is l ltac:(fun l => what_is r ltac:(fun r => k (@EBin val _ _ _ EpTo2p l r)))

  (* EUna *)
  | SizeNat.val ?n => what_is n ltac:(fun n => k (@EUna val _ _ EVal n ))
  | negb ?n => what_is n ltac:(fun n => k (@EUna val _ _ ENot n))
  | string_length ?v => what_is v ltac:(fun v => k (@EUna val _ _ EStringLen v))
  | fst ?v => what_is v ltac:(fun v => k (@EUna val _ _ EFst v))
  | snd ?v => what_is v ltac:(fun v => k (@EUna val _ _ ESnd v))
  | Some ?v => what_is v ltac:(fun v => k (@EUna val _ _ ESome v))
  | inl ?v => what_is v ltac:(fun v => k (@EUna val _ _ EInl v))
  | inr ?v => what_is v ltac:(fun v => k (@EUna val _ _ EInr v))
  | len ?s => what_is s ltac:(fun s => k (@EUna val _ _ ELen s))
  end.


Lemma test: False.
  String_is_literal "abc". String_is_literal "". pose (h := ""). Fail String_is_literal h.
  Fail is_None (Some 1) . is_None (None : option nat).
  Fail is_Some (None : option nat). is_Unit tt.
  is_Unit tt. what_is tt ltac:(fun v => pose v).
Abort.

Ltac clean_up :=
  cbv beta in *;
  match goal with
  | H : _ /\ _ |- _ =>
      let P0 := fresh "P" in
      let P1 := fresh "P" in
      destruct H as [P0 P1]
  | H : span_eq_take _ _ _ _ _ _ |- _ =>
      let P0 := fresh "P" in
      let P1 := fresh "P" in
      let P2 := fresh "P" in
      let P3 := fresh "P" in
      destruct H as [[P0 P1] [P2 P3]]
  | H : span_eq _ _ _ |- _ =>
      let P0 := fresh "P" in
      let P1 := fresh "P" in
      destruct H as [P0 P1]
  | H : length_spec _ _ _ _  |- _ =>
      let P0 := fresh "P" in
      let P1 := fresh "P" in
      let P2 := fresh "P" in
      destruct H as [P0 [P1 P2]]
  | H : read_spec _ _ _ _  |- _ =>
      let P0 := fresh "P" in
      let P1 := fresh "P" in
      destruct H as [P0 P1]
  | H : local_spec _ _ _  |- _ =>
      let P0 := fresh "P" in
      let P1 := fresh "P" in
      destruct H as [P0 P1]
  | H : compt_Some _ _ _ _ _ _ _ |- _ =>
      let P0 := fresh "P" in
      let P1 := fresh "P" in
      let P2 := fresh "P" in
      destruct H as [P0 [P1 P2]]
  end.


Ltac step := repeat clean_up; subst;
  match goal with
  | |- adequate _ (let! _ := _ in _) _ _ _ =>
      eapply bind_adequate; [ idtac | intros (* intros; repeat clean_up; subst *) ]
  | |- adequate _ (take ?e) _ _ _ =>
      what_is e ltac:(fun v => eapply (take_adequate _ _ v));
      [repeat econstructor| eauto| lia]
  | |- adequate _ (take ?e) _ _ _ =>
      what_is e ltac:(fun v => eapply (take_verif_adequate _ _ v)); repeat econstructor
  | |- adequate _ (read ?s ?n) _ _ _ =>
      what_is s ltac:(fun s => what_is n ltac:(fun n => eapply (read_adequate _ _ s n)));
      [repeat split; eauto | repeat econstructor | eauto | repeat econstructor | eauto | lia]
  | |- adequate _ (read ?s ?n) _ _ _ =>
      what_is s ltac:(fun s => what_is n ltac:(fun n => eapply (read_verif_adequate _ _ s n)))(* ; *)
      (* [repeat split; eauto | repeat econstructor | repeat econstructor | eauto] *)
  | |- adequate _ (if ?b then ?et else ?ef) _ _ _ =>
      what_is b ltac:(fun s => eapply (ite_adequate _ _ s));
      repeat econstructor; eauto; intros
  | |- adequate _ fail _ _ _ => eapply fail_adequate
  | |- adequate _ length _ _ _ => eapply length_adequate
  | |- adequate _ (peek _) _ _ _ => eapply peek_adequate
  | |- adequate _ (ret ?v) _ _ _ =>
      what_is v ltac:(fun v => eapply (ret_adequate _ _ _ v)); repeat econstructor; eauto
  end.

(* Lemma decompose_app_adequate : forall Z (hv : VAL Z) v X Y (e : Z -> NomG X) h (R : X -> Y -> Prop) data, *)
(*     (forall vv, sem_VAL hv vv -> *)
(*            sem_val vv = v -> *)
(*            adequate R (e v) (h vv) data) -> *)
(*     adequate R (e v) (let% v := Val hv in h v) data. *)
(* Proof. *)
(*   intros Z hv v X Y e h R data ADE s res WF SEM. *)
(*   next_step SEM. *)
(*   - next_step H3. eapply ADE; eauto. *)
(*   - next_step H2. *)
(* Qed. *)

Definition rest_spec data t x y := len t = 0 /\ span_eq data x y /\ x = y.

Definition rest_adequate_sig : {code | forall data s, adequate (rest_spec data) rest code data s}.
  eapply exist. intros. unfold rest.
  repeat step. eapply consequence_adequate. step.
  clean_up. intros t0 v hv [P2 [P3 P4]]. clean_up. subst. repeat split; eauto.
  rewrite P1 in P4. rewrite P4. apply N.sub_diag.
Defined.

Lemma rest_adequate : forall data s, adequate (rest_spec data) rest (`rest_adequate_sig) data s.
Proof. intros. destruct rest_adequate_sig as [p a]. eapply a. Qed.

Definition verify_spec {X Y} (R : span -> X -> Y -> Prop)
  (hb : val Y -> VAL bool) (b : X -> bool) s x y :=
  R s x y /\
    (exists vy, sem_val vy = y /\ exists hv, sem_VAL (hb vy) hv /\ sem_val hv = true) /\
    b x = true.

Definition verify_adequate_sig {Y} h (hb : val Y -> VAL bool) :
  {code | forall X b (R : span -> X -> Y -> Prop),
      (forall vy x s,
          R s x (sem_val vy) ->
          ∃ vb, sem_VAL (hb vy) vb /\ sem_val vb = b x) ->
      forall data s (e : NomG X),
        adequate R e h data s ->
        adequate (verify_spec R hb b) (verify e b) code data s}.
  eapply exist. intros. unfold verify.
  repeat step. eauto.
  destruct (H vres r t) as [vb [P0 P1]]; eauto.
  eapply (ite_adequate _ _ (hb vres)); eauto; intro.
  eapply (ret_adequate _ _  _ (Var vres)). econstructor.
  repeat split; auto. exists vres. split; auto. exists vb. split; auto. rewrite P1 H2 //.
  step.
Defined.

Lemma verify_adequate {Y} h (hb : val Y -> VAL bool) :
  forall X b (R : span -> X -> Y -> Prop),
    (forall vy x s,
        R s x (sem_val vy) ->
        ∃ vb, sem_VAL (hb vy) vb /\ sem_val vb = b x) ->
    forall data s (e : NomG X),
      adequate R e h data s ->
      adequate (verify_spec R hb b) (verify e b) (proj1_sig (verify_adequate_sig h hb)) data s.
Proof. intros. destruct verify_adequate_sig as [a p]. eapply p; eauto. Qed.

(* Definition verify_spec {X Y} (R : span -> X -> Y -> Prop) *)
(*   (hb : VAL Y -> VAL bool) (b : X -> bool) s x y := *)
(*   R s x y /\ *)
(*     (forall hy vy, sem_VAL hy vy -> sem_val vy = y -> exists hv, sem_VAL (hb hy) hv /\ sem_val hv = true) /\ *)
(*     b x = true. *)


(* Definition verify_adequate_sig {Y} h (hb : VAL Y -> VAL bool) : *)
(*   {code | forall X b (R : span -> X -> Y -> Prop), *)
(*       (forall hy vy x s, *)
(*           sem_VAL hy vy -> *)
(*           R s x (sem_val vy) -> *)
(*           ∃ vb, sem_VAL (hb hy) vb /\ sem_val vb = b x) -> *)
(*       forall data s (e : NomG X), *)
(*         adequate R e h data s -> *)
(*         adequate (verify_spec R hb b) (verify e b) code data s}. *)
(*   eapply exist. intros. unfold verify. *)
(*   repeat step. eauto. *)
(*   destruct (H (Var vres) vres r t) as [vb [P0 P1]]; eauto. econstructor. *)
(*   eapply (ite_adequate (hb (Var vres))); eauto; intro. *)
(*   eapply (ret_adequate _ (Var vres)). econstructor. *)
(*   repeat split; auto. intros. rewrite <- H4 in H1. *)
(*   eapply H in H3 as [vb0 [P2 P3]]; eauto. step. *)
(* Defined. *)

(* Lemma verify_adequate {Y} h (hb : VAL Y -> VAL bool) : *)
(*   forall X b (R : span -> X -> Y -> Prop), *)
(*     (forall hy vy x s, *)
(*         sem_VAL hy vy -> *)
(*         R s x (sem_val vy) -> *)
(*         ∃ vb, sem_VAL (hb hy) vb /\ sem_val vb = b x) -> *)
(*     forall data s (e : NomG X), *)
(*       adequate R e h data s -> *)
(*       adequate (verify_spec R hb b) (verify e b) (proj1_sig (verify_adequate_sig h hb)) data s. *)
(* Proof. intros. destruct verify_adequate_sig as [a p]. eapply p; eauto. Qed. *)

Lemma decompose_app_adequate : forall Z (hv : VAL Z) X Y vv v (e : Z -> NomG X) h (R : span -> X -> Y -> Prop) data s,
    sem_VAL hv vv ->
    sem_val vv = v ->
    adequate R (e v) (h vv) data s ->
    adequate R (e v) (let% v := Val hv in h v) data s.
Proof.
  intros Z hv X Y vv v e h R data s VALv EQv ADE WF res SEM.
  next_step SEM.
  - next_step H3. VAL_unif. subst. eapply ADE; auto.
  - next_step H2.
Qed.


(* Lemma decompose_app2_adequate : *)
(*   forall Z0 (hv0 : VAL Z0) W0 (hv1 : VAL W0) vv0 v0 vv1 v1 X Y (e : Z -> W -> NomG X) h *)
(*     (R : span -> X -> Y -> Prop) data s, *)
(*     sem_VAL hv0 vv0 -> *)
(*     sem_val vv0 = v0 -> *)
(*     sem_VAL hv1 vv1 -> *)
(*     sem_val vv1 = v1 -> *)
(*     adequate R (e v0 v1) (h vv0 vv1) data s -> *)
(*     adequate R (e v0 v1) (let% v0 := Val hv0 in *)
(*                           let% v1 := Val hv1 in *)
(*                           h v0 v1) data s. *)
(* Proof. *)
(*   intros Z hv0 W hv1 vv0 v0 vv1 v1 X Y e h R data s VALv0 EQv0 VALv1 EQv1 ADE WF res SEM. *)
(*   next_step SEM. *)
(*   - next_step H3. next_step H6. *)
(*     + next_step H3. VAL_unif. subst. eapply ADE; auto. *)
(*     + next_step H2. *)
(*   - next_step H2. *)
(* Qed. *)

Lemma decompose_app2_adequate :
  forall A0 (hv0 : VAL A0) B0 (hv1 : VAL B0) A B vv0 v0 vv1 v1 X Y (e : A -> B -> NomG X) h (R : span -> X -> Y -> Prop) data s,
    sem_VAL hv0 vv0 ->
    sem_VAL hv1 vv1 ->
    adequate R (e v0 v1) (h vv0 vv1) data s ->
    adequate R (e v0 v1) (let% v0 := Val hv0 in
                          let% v1 := Val hv1 in
                          h v0 v1) data s.
Proof.
  intros A0 hv0 B0 hv1 A B vv0 v0 vv1 v1 X Y e h R data s VALv0 VALv1 ADE WF res SEM.
  next_step SEM.
  - next_step H3. next_step H6.
    + next_step H3. VAL_unif. subst. eapply ADE; auto.
    + next_step H2.
  - next_step H2.
Qed.

(* Definition R_some {X Y} (R : X -> Y -> Prop) (b : N) (x : N * X) (y : N * Y) := *)
(*   R x.2 y.2 /\ x.1 = y.1 /\ y.1 <= b. *)

Definition repeat_compt_Some_adequate_sig hon {Y} (h : val N -> val Y -> PHOASV Y) hb :
  {code | forall X von vb c e (b : X) (R : span -> X -> Y -> Prop) data s,
      sem_VAL hon von ->
      sem_val von = Some c ->
      sem_VAL hb vb ->
      R s b (sem_val vb) ->
      (forall vn n vx x t,
          sem_val vn = n ->
          compt_Some n R (fun _ _ => True%type) (fun _ _ => True%type) t x (sem_val vx) ->
          n < c ->
          adequate R (e n x) (h vn vx) data t) ->
      adequate R (repeat_compt (Some c) e b) code data s}.
Proof.
  eapply exist. intros. unfold repeat_compt.
  step.
  eapply (repeat_Some_adequate hon _ (EBin EPair (Const (ENat 0)) hb));
    repeat econstructor; simpl; eauto.
  instantiate (1 := (fun s x y => x.1 = y.1 /\ R s x.2 y.2 )). simpl. split; auto.
  instantiate (1 := (fun n x => n = x.1)). simpl. reflexivity.
  instantiate (1 := (fun n x => n = x.1)). simpl. reflexivity.
  intros. subst. destruct H5 as [[P0 P3] [P1 P2]]. subst. eapply bind_adequate.
  eapply (decompose_app2_adequate _ (EUna EFst (Var hv)) _ (EUna ESnd (Var hv)));
    repeat econstructor.
  eapply H3. simpl. auto. repeat split; auto. lia.
  intros. eapply (ret_adequate _ _ _ (EBin EPair (EBin EAdd (EUna EFst (Var hv)) (Const (ENat 1))) (Var vres))); repeat econstructor.
  simpl. rewrite P0. reflexivity. simpl. auto. simpl. lia. simpl. lia.
  simpl in *. destruct H4.
  eapply (ret_adequate _ _ _ (EUna ESnd (Var vres))); repeat econstructor. auto.
Defined.

Lemma repeat_compt_Some_adequate hon {Y} (h : val N -> val Y -> PHOASV Y) hb :
  forall X von vb c e (b : X) (R : span -> X -> Y -> Prop) data s,
      sem_VAL hon von ->
      sem_val von = Some c ->
      sem_VAL hb vb ->
      R s b (sem_val vb) ->
      (forall vn n vx x t,
          sem_val vn = n ->
          compt_Some n R (fun _ _ => True%type) (fun _ _ => True%type) t x (sem_val vx) ->
          n < c ->
          adequate R (e n x) (h vn vx) data t) ->
      adequate R (repeat_compt (Some c) e b) (proj1_sig (repeat_compt_Some_adequate_sig hon h hb)) data s.
Proof. intros. destruct repeat_compt_Some_adequate_sig as [a p]. eapply p; eauto. Qed.

Definition repeat_compt_adequate_sig hon {Y} (h : val N -> val Y -> PHOASV Y) hb :
  {code | forall X von vb on e b (R : span -> X -> Y -> Prop) data s,
      sem_VAL hon von ->
      sem_val von = on ->
      sem_VAL hb vb ->
      R s b (sem_val vb) ->
      (forall vn n vx x t, sem_val vn = n -> R t x (sem_val vx) -> adequate R (e n x) (h vn vx) data t) ->
      adequate R (repeat_compt on e b) code data s}.
Proof.
  eapply exist. intros. unfold repeat_compt.
  step. eapply (repeat_adequate _ _ hon _ _ (EBin EPair (Const (ENat 0)) hb) _);
    repeat econstructor; eauto.
  simpl. instantiate (1 := fun s x y => x.1 = y.1 /\ R s x.2 y.2). split; auto.
  intros. subst. destruct H4. eapply bind_adequate.
  eapply (decompose_app2_adequate _ (EUna EFst (Var hv)) _ (EUna ESnd (Var hv)));
  repeat econstructor.
  eapply H3; eauto.
  intros.  eapply (ret_adequate _ _ _ (EBin EPair (EBin EAdd (EUna EFst (Var hv)) (Const (ENat 1))) (Var vres))); repeat econstructor.
  simpl. lia. simpl. auto.
  eapply (ret_adequate _ _ _ (EUna ESnd (Var vres))); repeat econstructor. simpl in *.
  destruct H0. auto.
Defined.

Lemma repeat_compt_adequate hon {Y} (h : val N -> val Y -> PHOASV Y) hb :
  forall X von vb on e b (R : span -> X -> Y -> Prop) data s,
      sem_VAL hon von ->
      sem_val von = on ->
      sem_VAL hb vb ->
      R s b (sem_val vb) ->
      (forall vn n vx x t, sem_val vn = n -> R t x (sem_val vx) -> adequate R (e n x) (h vn vx) data t) ->
      adequate R (repeat_compt on e b) (proj1_sig (repeat_compt_adequate_sig hon h hb)) data s.
Proof. intros. destruct repeat_compt_adequate_sig as [a p]. eapply p; eauto. Qed.

Lemma string_get_lt : forall s n, n < string_length s -> exists r, string_get n s = Some r.
Proof.
  induction s; simpl; intros.
  - exfalso. eapply N.nlt_0_r. eauto.
  - destruct n.
    + rewrite string_get_equation_2. eexists. reflexivity.
    + rewrite <- N.succ_pos_pred in H.
      eapply N.succ_lt_mono in H.
      eapply IHs in H. destruct H.
      rewrite string_get_equation_3.
      exists x. rewrite <- N.pos_pred_spec. auto.
Qed.

Definition tag_adequate_sig hs :
  {code | forall vs, sem_VAL hs vs -> forall str, sem_val vs = str -> forall data s,
          adequate (fun t x y => len t = len s - string_length str /\ x = y) (tag str) code data s}.
  eapply exist. intros. unfold tag.
  repeat step; repeat econstructor; eauto.
  eapply (repeat_compt_Some_adequate (EUna ESome (EUna EStringLen hs)) _ (Const (EBool true)));
    repeat econstructor; eauto.
  simpl. instantiate (1 := fun t0 x y => t = t0 /\ x = y). split; auto.
  intros. destruct H1 as [[P5 P6] [P3 P4]]. subst. repeat step.
  clean_up. subst. eapply string_get_lt in H2. destruct H2. rewrite H0.
  eapply (ret_adequate _ _ _ (EBin EAnd (Var vx) (EBin EEq (EUna EVal (Var vres0)) (EUna EVal (EBin EStringGet (Var vn) hs))))). repeat econstructor; eauto.
  repeat split; auto. clean_up. subst. repeat step.
Defined.

Lemma tag_adequate hs : forall vs,
    sem_VAL hs vs -> forall str,
      sem_val vs = str -> forall data s,
        adequate (fun t x y => len t = len s - string_length str /\ x = y)
          (tag str) (proj1_sig (tag_adequate_sig hs)) data s.
Proof. intros. destruct tag_adequate_sig as [a p]. eapply p; eauto. Qed.

Definition recognize_adequate_sig {X} (h : PHOASV X) :
  {code | forall e data s, adequate (fun _ => eq) e h data s ->
                      adequate (fun _ => span_eq data) (recognize e) code data s}.
  eapply exist. intros. unfold recognize.
  repeat step. eauto. simpl in *. destruct H0. subst. eapply consequence_adequate. step.
  intros t1 v hv [P2 [P3 P4]]. subst. instantiate (1 := eq). reflexivity.
  destruct H0 as [P0 P2]. subst. eapply consequence_adequate.
  eapply (take_verif_adequate _ _ (EBin ESub (Var vres) (Var vres0))); repeat econstructor; eauto.
  intros. clean_up. subst. split; auto.
Defined.

Definition recognize_adequate : forall X (h : PHOASV X),
  forall e data s,
    adequate (fun _ => eq) e h data s ->
    adequate (fun _ => span_eq data) (recognize e) (proj1_sig (recognize_adequate_sig h)) data s.
Proof. intros. destruct (recognize_adequate_sig h). eapply a; auto. Qed.

Definition be_u8_adequate_sig :
  {code | forall data s, adequate (fun t x y => len t = len s -1 /\ x = y) be_u8 code data s}.
  eapply exist. intros. unfold be_u8.
  repeat step; repeat econstructor; eauto.
  clean_up. subst. eapply consequence_adequate. step.
  intros t0 v hv [P3 P4]. subst. split; auto.
Defined.

Definition be_u8_adequate :
  forall data s, adequate (fun t x y => len t = len s -1 /\ x = y) be_u8 (proj1_sig be_u8_adequate_sig) data s.
Proof. intros. destruct be_u8_adequate_sig as [p a]. eapply a. Qed.

Definition be_u16_adequate_sig :
  {code | forall data s, adequate (fun t x y => len t = len s - 2 /\ x = y) be_u16 code data s}.
Proof.
  eapply exist. intros. unfold be_u16.
  repeat step; repeat econstructor; eauto.
  1-2 : eapply be_u8_adequate. clean_up. subst. step. lia.
Defined.

Lemma be_u16_adequate : forall data s,
    adequate (fun t x y => len t = len s - 2 /\ x = y) be_u16 (`be_u16_adequate_sig) data s.
Proof. intro. destruct be_u16_adequate_sig as [a p]. eapply p. Qed.

Definition be_u32_adequate_sig :
  {code | forall data s, adequate (fun t x y => len t = len s - 4 /\ x = y) be_u32 code data s}.
Proof.
  eapply exist. intros. unfold be_u32. repeat step.
  1-2 : eapply be_u16_adequate. clean_up. subst. step. lia.
Defined.

Lemma be_u32_adequate : forall data s,
    adequate (fun t x y => len t = len s - 4 /\ x = y) be_u32 (`be_u32_adequate_sig) data s.
Proof. intro. destruct be_u32_adequate_sig as [a p]. eapply p. Qed.

Definition value_not_in_string_adequate_sig hv hs :
  {code | forall vv v,
      sem_VAL hv vv ->
      sem_val vv = v ->
      forall vs str,
        sem_VAL hs vs ->
        sem_val vs = str ->
        forall data s, adequate (fun t x y => t = s /\ x = y) (value_not_in_string v str) code data s}.
Proof.
  eapply exist. intros. subst. unfold value_not_in_string.
  eapply (repeat_compt_Some_adequate (EUna ESome (EUna EStringLen hs)) _ (Const (EBool true)));
    repeat econstructor; eauto.
  intros. eapply string_get_lt in H3. destruct H3. rewrite H3.
  clean_up. step.
Defined.

Lemma value_not_in_string_adequate : forall hv hs vv v,
    sem_VAL hv vv ->
      sem_val vv = v ->
      forall vs str,
        sem_VAL hs vs ->
        sem_val vs = str ->
        forall data s, adequate (fun t x y => t = s /\ x = y) (value_not_in_string v str)
                    (proj1_sig (value_not_in_string_adequate_sig hv hs)) data s.
Proof. intros. destruct value_not_in_string_adequate_sig as [a p]. eapply p; eauto. Qed.

Definition is_not_adequate_sig hs :
  {code | forall vs,
      sem_VAL hs vs ->
      forall str, sem_val vs = str ->
           forall data s, adequate (fun _ => eq) (is_not str) code data s}.
  eapply exist. intros. unfold is_not.
  eapply consequence_adequate. eapply recognize_adequate.
  eapply (repeat_adequate _ _ (Const ENone) _ _ (Const EUnit)); repeat econstructor; eauto.
  intros. step. eapply be_u8_adequate. repeat step; repeat econstructor; eauto.
  eapply (value_not_in_string_adequate (Var vres) hs); repeat econstructor; eauto.
  clean_up. repeat step. intros t v hv [P0 P1]. auto.
Defined.

Lemma is_not_adequate : forall hs vs,
    sem_VAL hs vs ->
      forall str, sem_val vs = str ->
             forall data s, adequate (fun _ => eq) (is_not str) (proj1_sig (is_not_adequate_sig hs)) data s.
Proof. intros. destruct is_not_adequate_sig as [a p]. eapply p; eauto. Qed.

Definition char_adequate_sig hn :
  {code | forall vn, sem_VAL hn vn -> forall n,
        sem_val vn = n -> forall data s,
          adequate (fun t x y => len t = len s - 1 /\ x = y) (char n) code data s}.
  eapply exist. intros. unfold char.
  step. eapply be_u8_adequate. clean_up. subst. repeat step.
Defined.

Lemma char_adequate : forall hn vn,
    sem_VAL hn vn -> forall n,
        sem_val vn = n -> forall data s,
        adequate (fun t x y => len t = len s - 1 /\ x = y) (char n) (proj1_sig (char_adequate_sig hn)) data s.
Proof. intros. destruct char_adequate_sig. eapply a; eauto. Qed.

Definition length_data_adequate_sig h :
  {code | forall e data s,
      adequate (fun _ => eq) e h data s ->
      adequate (fun _ => span_eq data) (length_data e) code data s}.
  eapply exist. intros. unfold length_data.
  step. eauto. simpl in *. subst. eapply consequence_adequate. step.
  intros t0 v hv [[P0 P1] [P3 P2]]. split; auto.
Defined.

Definition length_data_adequate : forall h e data s,
    adequate (fun _ => eq) e h data s ->
      adequate (fun _ => span_eq data) (length_data e) (proj1_sig (length_data_adequate_sig h)) data s.
Proof. intros. destruct length_data_adequate_sig as [a p]. eapply p; eauto. Qed.

Definition map_parser_adequate_sig hc1 {X} (hc2 : PHOASV X) :
  {code | forall c1 Y (c2 : NomG Y) R' data s,
      adequate (fun _ x y => x = y /\ span_data_wf data x) c1 hc1 data s ->
      (forall r res, span_data_wf data r -> r = res -> adequate (fun _ => R') c2 hc2 data res) ->
      adequate (fun _ => R') (map_parser c1 c2) code data s}.
  eapply exist. intros. unfold map_parser.
  step. eauto. clean_up. subst.
  eapply consequence_adequate. eapply scope_adequate.
  eapply consequence_adequate. eapply H0. eauto. reflexivity.
  intros. eapply H1. 2 : eauto. eapply SVar. auto.
  intros t0 v hv [P1 P2]. auto.
Defined.

Lemma map_parser_adequate hc1 {X} (hc2 : PHOASV X) :
  forall c1 Y (c2 : NomG Y) R' data s,
    adequate (fun _ x y => x = y /\ span_data_wf data x) c1 hc1 data s ->
    (forall r res, span_data_wf data r -> r = res -> adequate (fun _ => R') c2 hc2 data res) ->
    adequate (fun _ => R') (map_parser c1 c2) (proj1_sig (map_parser_adequate_sig hc1 hc2)) data s.
Proof. intros. destruct map_parser_adequate_sig. auto. Qed.

(* Definition ipv4 : Type := nat8 * nat8 * nat8 * nat8. *)

(* Definition ipv4_spec (ip : Ipv4) (i : ipv4) := *)
(*   a4 ip = i.1.1.1 /\ b4 ip = i.1.1.2 /\ c4 ip = i.1.2 /\ d4 ip = i.2. *)

(* Definition get_ipv4_adequate_sig : *)
(*   {code | forall data s, adequate (fun t x y => len t = len s - 4 /\ ipv4_spec x y) get_ipv4 code data s}. *)
(*   eapply exist. intros. unfold get_ipv4. *)
(*   repeat step. *)
(*   1-4 : eapply be_u8_adequate. repeat clean_up. subst. *)
(*   eapply (ret_adequate _ (EBin EPair (EBin EPair (EBin EPair (Var vres) (Var vres0)) (Var vres1)) (Var vres2))); repeat econstructor. lia. *)
(* Defined. *)

(* Lemma get_ipv4_adequate : forall data s, *)
(*     adequate (fun t x y => len t = len s - 4 /\ ipv4_spec x y) *)
(*       get_ipv4 (`get_ipv4_adequate_sig) data s. *)
(* Proof. intros. destruct get_ipv4_adequate_sig. eauto. Qed. *)

Definition get_ipv4_adequate_sig :
  {code : PHOAS Ipv4 | forall data s, adequate (fun _ _ _ => True%type) get_ipv4 code data s}.
  eapply exist. intros. unfold get_ipv4.
  repeat step.
  1-4 : eapply be_u8_adequate. repeat clean_up. subst.
  eapply (cstruct_adequate "ipv4" "create_ipv4"
            (CONS (Var vres)
               (CONS (Var vres0)
                  (CONS (Var vres1)
                     (CONS (Var vres2) NIL))))).
Defined.

Lemma get_ipv4_adequate : forall data s,
    adequate (fun _ _ _ => True%type) get_ipv4 (`get_ipv4_adequate_sig) data s.
Proof. intros. destruct get_ipv4_adequate_sig. eauto. Qed.

Definition cond_adequate_sig {Y} hb h :
  {code | forall X vb b e (R : span -> X -> Y -> Prop) data s,
      sem_VAL hb vb ->
      sem_val vb = b ->
      (b = true -> adequate R e h data s) ->
      adequate (fun t x y => match x, y with
                          | None, None => t = s
                          | Some x, Some y => R t x y
                          | _,_ => False%type
                          end) (cond b e) code data s}.
  eapply exist. intros. unfold cond.
  repeat step. eapply H1. auto.
  eapply (ret_adequate _ _ _ (EUna ESome (Var vres))); repeat econstructor; eauto.
  eapply (ret_adequate _ _ _ (Const ENone)); repeat econstructor; eauto.
Defined.

Lemma cond_adequate {Y} hb h :
  forall X vb b e (R : span -> X -> Y -> Prop) data s,
      sem_VAL hb vb ->
      sem_val vb = b ->
      (b = true -> adequate R e h data s) ->
      adequate (fun t x y => match x, y with
                          | None, None => t = s
                          | Some x, Some y => R t x y
                          | _,_ => False%type
                          end) (cond b e) (proj1_sig (cond_adequate_sig hb h)) data s.
Proof. intros. destruct cond_adequate_sig. eauto. Qed.


Definition VECTOR_spec {X Y} (R : X -> Y -> Prop) (vecx : VECTOR X) (vecy : VECTOR Y) :=
  (forall n, List.In n (List.split (vector_to_list vecx)).1 <->
          List.In n (List.split (vector_to_list vecy)).1) /\
    forall n x y,
      List.In (n,x) (vector_to_list vecx) ->
      List.In (n,y) (vector_to_list vecy) ->
      R x y.

(* Definition VECTOR_spec {X Y} (R : X -> Y -> Prop) (vecx : VECTOR X) (vecy : VECTOR Y) := *)
(*   forall n, *)
(*     Vector.size (`vecx) = Vector.size (`vecy) -> *)
(*     n < Vector.size (`vecx) -> *)
(*     match Vector.get vecx n, Vector.get vecy n with *)
(*     | Some x, Some y => R x y *)
(*     | None, None => True *)
(*     | _,_ => False *)
(*     end. *)

Lemma test : forall X Y (R : X -> Y -> Prop) v0 v1 r0 r1,
    R r0 r1 ->
    VECTOR_spec R v0 v1 ->
    VECTOR_spec R (add v0 r0) (add v1 r1).
Proof.
  intros.
  destruct H0. split.
  - intro. split; intros.
    + destruct v0. destruct v1. destruct x. destruct x0. destruct v. destruct v0.
      simpl in *. subst. unfold add in *. unfold vector_to_list in *. simpl in *.
Admitted.

Definition many1_adequate_sig {Y} h :
  {code | forall X e (R : X -> Y -> Prop) data s,
      (forall t, adequate (fun _ => R) e h data t) ->
      adequate (fun _ => VECTOR_spec R) (many1 e) code data s}.
  eapply exist. intros. unfold many1.
  repeat step. eapply H.
  eapply (repeat_adequate _ _ (Const ENone) _ _ (EBin EAddVec (EUna EMake (Const (ENat 2))) (Var vres0))).
  1-4 : repeat econstructor; eauto.
  simpl. split.
  - simpl. reflexivity.
  - intros. edestruct add_vector_list. erewrite H4 in H2.
    edestruct add_vector_list. erewrite H5 in H3. clear H4 H5.
    simpl in *. destruct H2; try contradiction. inversion H2. subst.
    destruct H3; try contradiction. inversion H3. subst. auto.
  - intros. repeat step. eapply H. simpl in *.
    eapply (ret_adequate _ _ _ (EBin EAddVec (Var hv) (Var vres3))).
    repeat econstructor; eauto.
    eapply test; auto.
Defined.

Lemma many1_adequate {Y} h :
  forall X e (R : X -> Y -> Prop) data s,
    (forall t, adequate (fun _ => R) e h data t) ->
    adequate (fun _ => VECTOR_spec R) (many1 e) (proj1_sig (many1_adequate_sig h)) data s.
Proof. destruct many1_adequate_sig. eauto. Qed.

Close Scope N_scope.
