From stdpp Require Import numbers.
From Equations Require Import Equations.

From Formalisation Require Export SizeNat IpAddr Vector Span.
From SepLogic Require Export SepBasicCore SepSet.
From Classes Require Export Foldable.

Open Scope N_scope.

Module signature.

  From FreeMonad Require Import FreeMonad.

(* =atom= *)
Context {atom : Type}.
(* =end= *)

(* =signature= *)
Inductive NOM : Type -> Type :=
| FAIL : forall X, NOM X
| LENGTH : NOM N
| READ : span -> N -> NOM atom
| TAKE : N -> NOM span
| ALT : forall X, Free NOM X -> Free NOM X -> NOM X
| LOCAL : option span -> forall X, Free NOM X -> NOM X
| REPEAT : option N -> forall X, (X -> Free NOM X) -> X -> NOM X.
(* =end= *)

Definition NomG := Free NOM.

Global Arguments FAIL {X}.
Global Arguments ALT [X].
Global Arguments LOCAL _ [X].
Global Arguments REPEAT _ [X].

Definition fail {X} : NomG X := syntax_effect FAIL.

Definition length : NomG N := syntax_effect LENGTH.

Definition take (n : N) : NomG span := syntax_effect (TAKE n).

Definition read (s : span) (pos : N): NomG atom := syntax_effect (READ s pos).

Definition alt {X} (c1 : NomG X) (c2 : NomG X) : NomG X := syntax_effect (ALT c1 c2).

(* =local= *)
Definition local (s : option span) {X} (e : NomG X) : NomG X :=
  syntax_effect (LOCAL s e).

Definition scope (s : span) {X} (e : NomG X) := local (Some s) e.

Definition peek {X} (e : NomG X) : NomG X := local None e.
(* =end= *)

(* =repeat= *)
Definition repeat (n : option N) {X} (e : X -> NomG X) (base : X): NomG X :=
  syntax_effect (REPEAT n e base).

Definition repeat_n (n : N) {X} (e : X -> NomG X) (base : X): NomG X :=
  repeat (Some n) e base.

Definition many {X} (e : X -> NomG X) (base : X): NomG X :=
  repeat None e base.
(* =end= *)

End signature.

Section NomG_syntax.

Context {atom : Type}.

Inductive NOM : Type -> Type :=
| FAIL : forall X, NOM X
| LENGTH : NOM N
| READ : span -> N -> NOM atom
| TAKE : N -> NOM span
| ALT : forall X, NomG X -> NomG X -> NOM X
| LOCAL : option span -> forall X, NomG X -> NOM X
| REPEAT : option N -> forall X, (X -> NomG X) -> X -> NOM X


(* =NomG= *)
with NomG : Type -> Type :=
| ret : forall X, X -> NomG X
| op : forall Y, NOM Y -> forall X, (Y -> NomG X) -> NomG X.
(* =end= *)

Global Arguments FAIL {X}.
Global Arguments ALT [X].
Global Arguments LOCAL _ [X].
Global Arguments REPEAT _ [X].

Global Arguments ret {X}.
  Global Arguments op [Y] _ [X].

  Fixpoint bind {X Y} (m : NomG X) (f : X -> NomG Y) : NomG Y :=
    match m in (NomG T) return (T -> NomG Y) -> NomG Y with
    | ret v => fun f => f v
    | op e c => fun f => op e (fun v => bind (c v) f)
    end f.

  Definition algeff {X} (e : NOM X) : NomG X := op e ret.

  Definition fail {X} : NomG X := algeff FAIL.

  Definition length : NomG N := algeff LENGTH.

  Definition take (n : N) : NomG span := algeff (TAKE n).

  Definition read (s : span) (pos : N): NomG atom := algeff (READ s pos).

  Definition alt {X} (c1 : NomG X) (c2 : NomG X) : NomG X := algeff (ALT c1 c2).

Definition local (s : option span) {X} (e : NomG X) : NomG X :=
  algeff (LOCAL s e).

Definition scope (s : span) {X} (e : NomG X) := local (Some s) e.

Definition peek {X} (e : NomG X) : NomG X := local None e.

Definition repeat (n : option N) {X} (e : X -> NomG X) (base : X): NomG X :=
  algeff (REPEAT n e base).

Definition repeat_n (n : N) {X} (e : X -> NomG X) (base : X): NomG X :=
  repeat (Some n) e base.

Definition many {X} (e : X -> NomG X) (base : X): NomG X :=
  repeat None e base.


  (* Induction *)

  Notation "'let!' x ':=' e1 'in' e2" :=
    (bind e1 (fun x => e2)) (x name, at level 50).

  Notation "'let!' ( i , v ) ':=' e1 'in' e2" :=
    (bind e1 (fun ___temp =>
                let i := fst ___temp in
                let v := snd ___temp in
                e2)) (at level 50).

  Definition repeat_compt (n : option N) {X} (e : N -> X -> NomG X) (base : X): NomG X :=
    let! v := repeat n (fun x =>
                          let! v := e (fst x) (snd x) in
                          ret (fst x + 1, v)) (0,base) in
    ret (v.2).

  Lemma Nom_ind : forall (P : forall {X}, NomG X -> Prop),
      (forall X (v : X), P (ret v)) ->
      (forall X X0 (k : X0 -> NomG X), P (let! v := fail in k v)) ->
      (forall X (k : N -> NomG X), (forall v, P (k v)) -> P (let! v := length in k v)) ->
      (forall X (k: span -> NomG X) n, (forall v, P (k v)) -> P (let! v := take n in k v)) ->
      (forall X (k : atom -> NomG X) s pos, (forall v, P (k v)) -> P (let! v := read s pos in k v)) ->
      (forall X X0 (k : X0 -> NomG X) (c1 c2 : NomG X0), P c1 -> P c2 -> (forall v, P (k v)) -> P (let! v := alt c1 c2 in k v)) ->
      (forall X X0 (k : X0 -> NomG X) s c, P c -> (forall v, P (k v)) -> P (let! v := scope s c in k v)) ->
      (forall X X0 (k : X0 -> NomG X) c, P c -> (forall v, P (k v)) -> P (let! v := peek c in k v)) ->
      (forall X X0 (k : X0 -> NomG X) c, (forall res, P (c res)) -> (forall v, P (k v)) -> forall o b, P (let! v := repeat o c b in k v)) ->
      forall X (e :NomG X), P e.
  Proof.
    intros P Pret Pfail Plength Ptake Pread Palt Pscope Ppeek Prepeat. fix IH 2. destruct e.
    eapply Pret.
    destruct n.
    eapply Pfail.
    eapply Plength. intro. eapply IH.
    eapply Pread. intro. eapply IH.
    eapply Ptake. intro. eapply IH.
    eapply Palt. eapply IH. eapply IH. intro. eapply IH.
    destruct o.
    eapply Pscope. eapply IH. intro. eapply IH.
    eapply Ppeek. eapply IH. intro. eapply IH.
    eapply Prepeat. intros. eapply IH. intro. eapply IH.
  Qed.

End NomG_syntax.

Definition NomB := @NomG nat8.

Notation "'let!' x ':=' e1 'in' e2" :=
  (bind e1 (fun x => e2)) (x name, at level 50).

Notation "'let!' ( i , v ) ':=' e1 'in' e2" :=
  (bind e1 (fun ___temp =>
              let i := fst ___temp in
              let v := snd ___temp in
              e2)) (at level 50).

Section NomG_sem.

  Context {atom : Type}.

  (* Run *)

(* =Result= *)
Inductive Result X :=
| Res (x :X)
| NoRes
| NoFuel.
(* =end= *)

Global Arguments Res {X}.
Global Arguments NoRes {X}.
Global Arguments NoFuel {X}.

(* =MonSem= *)
Definition MonSem X := span -> Result (span * X).

Definition run_ret {X} (x : X) : MonSem X := fun s => Res (s, x).

Definition run_bind {X} (e : MonSem X) {Y} (f : X -> MonSem Y) : MonSem Y :=
  fun s =>
    match e s with
    | NoRes => NoRes
    | NoFuel => NoFuel
    | Res (s, x) => f x s
    end.

Notation "'let*' x ':=' e1 'in' e2" :=
  (run_bind e1 (fun x => e2)) (x name, at level 50).

Definition run_fail {X} : MonSem X := fun _ => NoRes.
Definition run_try_with {X} (e : MonSem X) (f: MonSem X): MonSem X :=
  fun s =>
    match e s with
    | NoFuel => NoFuel
    | NoRes => f s
    | Res (s,v) => Res (s,v)
    end.
Definition run_get : MonSem span := fun s => Res (s,s).
Definition run_set (s : span) : MonSem unit := fun _ => Res (s,tt).
(* =end= *)

(* =run_length= *)
Definition run_length :=
  let* s := run_get in
  run_ret (len s).
(* =end= *)

(* =run_take= *)
Definition run_take (n : N) : MonSem span :=
  let* s := run_get in
  if n <=? len s then
    let* _ := run_set (mk_span (pos s + n) (len s - n)) in
    run_ret (mk_span (pos s) n)
  else
    run_fail.
(* =end= *)

(* =lookup= *)
Equations lookupN {X} (l : list X) (n : N) (s : span): Result (span * X) by wf (N.to_nat n) lt :=
  lookupN [] n s := NoRes;
  lookupN (h :: t) 0 s := Res (s,h);
  lookupN (h :: t) pos s := lookupN t (N.pred pos) s.
Next Obligation.
  intros. unfold pos. lia.
Defined.
(* =end= *)

(* =run_read= *)
Definition run_read (arg1 : span) (arg2 : N) (a : list atom) : MonSem atom :=
  if arg2 <? len arg1
  then
    lookupN a (pos arg1 + arg2)
  else
    run_fail.
(* =end= *)

(* =run_alt= *)
Definition run_alt (run : forall {X}, NomG X -> list atom -> MonSem X) {X}
  (e1 e2 : @NomG atom X) (data : list atom) : MonSem X :=
  run_try_with (run e1 data) (run e2 data).
(* =end= *)

(* =run_scope= *)
Definition run_scope (run : forall {X}, NomG X -> list atom -> MonSem X) {X}
  (range : span) (e : @NomG atom X)  (data : list atom) : MonSem X :=
  let* save := run_get in
  let* _ := run_set range in
  let* v := run e data in
  let* _ := run_set save in
  run_ret v.
(* =end= *)

(* =run_peek= *)
Definition run_peek (run : forall {X}, NomG X -> list atom -> MonSem X) {X}
  (e : @NomG atom X) (data : list atom) : MonSem X :=
  let* save := run_get in
  let* v := run e data in
  let* _ := run_set save in
  run_ret v.
(* =end= *)

(* =run= *)
Fixpoint run (fuel : nat) {X} (m : NomG X) (data : list atom) {struct m} : MonSem X :=
  match m with
  | ret v => run_ret v
  | op o c =>
      let* v := run_op fuel o data in
      run fuel (c v) data
  end
(* =end= *)

(* =run_op= *)
with run_op (fuel : nat) {X} (m : NOM X) (data :list atom) : MonSem X :=
  match m with
  | FAIL  => run_fail
  | LENGTH => run_length
  | READ range pos => run_read range pos data
  | TAKE n => run_take n
  | ALT c1 c2 => run_alt (@run fuel) c1 c2 data
  | LOCAL (Some range) e => run_scope (@run fuel) range e data
  | LOCAL None e => run_peek (@run fuel) e data
  | @REPEAT _ (Some n) T e b =>
      (fix sem_repeat_some (n : nat) (x : T) : MonSem T :=
         match n with
         | O => run_ret x
         | S n =>
             let* v := run fuel (e x) data in
             sem_repeat_some n v
         end) (N.to_nat n) b
  | @REPEAT _ None T e b =>
      (fix sem_repeat_none (n : nat) (x : T) : MonSem T :=
         match n with
         | O => fun _ => NoFuel
         | S n =>
             run_try_with
               (let* v := run fuel (e x) data in
                sem_repeat_none n v)
               (run_ret x)
         end) fuel b
       end.
(* =end= *)

End NomG_sem.

Ltac unfold_MonSem := unfold run_alt, run_scope, run_length, run_peek, run_bind, run_try_with, run_ret, run_get, run_set, run_fail in *.

(* Expected : NoRes *)
Lemma test1 : run 1000 (let! v := alt (ret 0) (ret 1) in
                        if v =? 0
                        then fail
                        else ret v) ([] : list nat8) (mk_span 0 0) = NoRes.
Proof. reflexivity. Qed.

(* Res ({| pos := 0; len := 13 |}, {| pos := 0; len := 2 |}) *)
Compute (run 1000 (peek (take 2)) ([_8 5; _8 6; _8 115; _8 116;
                                    _8 0; _8 1; _8 0; _8 2;
                                    _8 0; _8 5; _8 0; _8 6;
                                    _8 0]) (mk_span 0 13)).
Notation "'let*' x ':=' e1 'in' e2" :=
  (run_bind e1 (fun x => e2)) (x name, at level 50).

Section equations.

  Context {atom : Type}.

  Variable fuel : nat.
  Variable data : list atom.

  Lemma run_ret_eq : forall s X (x :X), run fuel (ret x) data s = Res (s, x).
  Proof. reflexivity. Qed.

  Lemma run_fail_eq : forall s X, run fuel (fail : NomG X) data s = NoRes.
  Proof. reflexivity. Qed.

  Lemma ret_neutral_right : forall X (e : MonSem X) s,
      run_bind e run_ret s = e s.
  Proof.
    unfold_MonSem. intros. destruct (e s); simpl. destruct x; auto. auto. auto.
  Qed.

  Lemma ret_neutral_left : forall X (v : X) Y (k : X -> MonSem Y) s,
      run_bind (run_ret v) k s = (k v) s.
  Proof. reflexivity.  Qed.

  Lemma bind_assoc : forall X Y Z (e : MonSem X) f (g : Y -> MonSem Z) s,
      run_bind (run_bind e f) g s = run_bind e (fun v => run_bind (f v) g) s.
  Proof.
    unfold_MonSem. intros. destruct (e s); simpl. destruct x; auto. auto. auto.
  Qed.

  Lemma run_bind_eq : forall X Y (e e': MonSem X) (k k' : X -> MonSem Y) s,
      e s = e' s ->
      (forall v s, k v s = k' v s) ->
      run_bind e k s = run_bind e' k' s.
  Proof.
    unfold_MonSem. intros. rewrite H. destruct (e' s); simpl. destruct x; auto. auto. auto.
  Qed.

  Lemma run_bind_monsem : forall X e s Y (k : X -> NomG Y),
      run fuel (let! v := e in k v) data s =
        (let* v := run fuel e data in
         run fuel (k v) data) s.
  Proof.
    fix IH 2.
    destruct e; simpl; intros.
    - rewrite ret_neutral_left. reflexivity.
    - rewrite bind_assoc. eapply run_bind_eq; auto.
  Qed.

  Lemma run_bind_fail : forall X Y e s,
      run fuel e data s = NoRes ->
      forall (k : X -> NomG Y), run fuel (bind e k) data s = NoRes.
  Proof.
    intros X Y e s RUN k.
    rewrite run_bind_monsem. unfold_MonSem. rewrite RUN. reflexivity.
  Qed.

  Lemma lookupN_eq_span : forall X a n s1 s2 (v : X),
      lookupN a n s1 = Res (s2, v) -> s1 = s2.
  Proof.
    induction a; intros.
    - erewrite lookupN_equation_1 in H. inversion H.
    - revert s1 s2 v H. destruct n using N.peano_ind; intros.
      + erewrite lookupN_equation_2 in H. inversion H. reflexivity.
      + rewrite <- N.succ_pos_spec in H. erewrite lookupN_equation_3 in H.
        rewrite N.succ_pos_spec in H. rewrite N.pred_succ in H.
        eapply IHa. eauto.
  Qed.

  Lemma lookupN_NoFuel : forall X a n s1,
      lookupN a n s1 <> (NoFuel : Result (span * X)).
  Proof.
    induction a; intros.
    - erewrite lookupN_equation_1. auto.
    - revert s1. destruct n using N.peano_ind; intros.
      + erewrite lookupN_equation_2. auto.
      + rewrite <- N.succ_pos_spec. erewrite lookupN_equation_3.
        rewrite N.succ_pos_spec. rewrite N.pred_succ.
        eapply IHa.
  Qed.

  Lemma lookupN_indep_state_res : forall X a n s s' sres (v0 : X),
      lookupN a n s = Res (sres, v0) ->
      lookupN a n s' = Res (s', v0).
  Proof.
    induction a; intros.
    - rewrite lookupN_equation_1 in H. inversion H.
    - destruct n using N.peano_ind; intros.
      + rewrite lookupN_equation_2. rewrite lookupN_equation_2 in H.
        inversion H. reflexivity.
      + rewrite <- N.succ_pos_spec. erewrite lookupN_equation_3.
        rewrite N.succ_pos_spec. rewrite N.pred_succ.
        rewrite <- N.succ_pos_spec in H. erewrite lookupN_equation_3 in H.
        rewrite N.succ_pos_spec in H. rewrite N.pred_succ in H.
        eapply IHa; eauto.
  Qed.

  Lemma lookupN_indep_state_NoRes : forall X a n s s' ,
      lookupN a n s = (NoRes : Result (span * X)) ->
      lookupN a n s' = NoRes.
  Proof.
    induction a; intros.
    - rewrite lookupN_equation_1. reflexivity.
    - destruct n using N.peano_ind; intros.
      + rewrite lookupN_equation_2 in H. inversion H.
      + rewrite <- N.succ_pos_spec. erewrite lookupN_equation_3.
        rewrite N.succ_pos_spec. rewrite N.pred_succ.
        rewrite <- N.succ_pos_spec in H. erewrite lookupN_equation_3 in H.
        rewrite N.succ_pos_spec in H. rewrite N.pred_succ in H.
        eapply IHa; eauto.
  Qed.

  Lemma run_read_eq_span : forall s n s1 s2 v,
      run_read s n data s1 = Res (s2, v) -> s1 = s2.
  Proof.
    intros. unfold run_read in H. destruct (n <? len s) eqn:?.
    - eapply lookupN_eq_span. eauto.
    - unfold run_fail in H. inversion H.
  Qed.

  Lemma run_bind_decompose : forall X Y e (k : X -> NomG Y) s s_res v1 res,
      run fuel e data s = Res (s_res, v1) ->
      run fuel (k v1) data s_res = res ->
      run fuel (bind e k) data s = res.
  Proof.
    destruct e; intros k s s_res v1 res RUNE RUNK.
    - rewrite run_bind_monsem. rewrite ret_neutral_left.
      rewrite run_ret_eq in RUNE. inversion RUNE. subst.
      reflexivity.
    - rewrite run_bind_monsem. unfold_MonSem. rewrite RUNE. eapply RUNK.
  Qed.

End equations.


(* Expected : Res ({| pos := 1; len := 9 |}, [_8 50]) *)
Compute (run 1000 (let! s := take 1 in
                   let! v := read s 0 in
                   ret [v] : @NomG nat8 (list nat8))
           [_8 50;_8 1;_8 2;_8 3;_8 4;_8 5;_8 6;_8 7;_8 8;_8 9]
           (mk_span 0 10)).

(* Expected : NoRes *)
Compute (run 1000 (let! s := take 1 in
                   let! v := read s 1 in
                   ret [v] : @NomG nat8 (list nat8))
           [_8 50;_8 1;_8 2;_8 3;_8 4;_8 5;_8 6;_8 7;_8 8;_8 9]
           (mk_span 0 10)).

(* Expected : Res ({| pos := 10; len := 0 |}, 95) *)
Compute (run 11 (repeat None (fun x =>
                                let! s := take 1 in
                                let! v := read s 0 in
                                ret (x + val v)) 0)
           [_8 50;_8 1;_8 2;_8 3;_8 4;_8 5;_8 6;_8 7;_8 8;_8 9]
           (mk_span 0 10)).

(* Expected : NoFuel *)
Compute (run 9 (repeat None (fun x =>
                               let! s := take 1 in
                               let! v := read s 0 in
                               ret (x + val v)) 0)
           [_8 50;_8 1;_8 2;_8 3;_8 4;_8 5;_8 6;_8 7;_8 8;_8 9]
           (mk_span 0 10)).


(* Expected : Res ({| pos := 10; len := 0 |}, 190) *)
Compute (run 11 (let! v0 := peek (repeat None (fun x =>
                                                 let! s := take 1 in
                                                 let! v := read s 0 in
                                                 ret (x + val v)) 0) in
                 let! v1 := repeat None (fun x =>
                                           let! s := take 1 in
                                           let! v := read s 0 in
                                           ret (x + val v)) 0 in
                 let! _ := length in
                 ret (v0 + v1))
           [_8 50;_8 1;_8 2;_8 3;_8 4;_8 5;_8 6;_8 7;_8 8;_8 9]
           (mk_span 0 10)).


(* Expected : Res ({| pos := 8; len := 2 |}, 78) *)
Compute (run 11 (repeat (Some 8) (fun x =>
                                    let! s := take 1 in
                                    let! v := read s 0 in
                                    ret (x + val v)) 0)
           [_8 50;_8 1;_8 2;_8 3;_8 4;_8 5;_8 6;_8 7;_8 8;_8 9]
           (mk_span 0 10)).


(* Expected : Res ({| pos := 8; len := 2 |}, 78) *)
Compute (run 0 (repeat (Some 8) (fun x =>
                                   let! s := take 1 in
                                   let! v := read s 0 in
                                   ret (x + val v)) 0)
           [_8 50;_8 1;_8 2;_8 3;_8 4;_8 5;_8 6;_8 7;_8 8;_8 9]
           (mk_span 0 10)).

(* Expected : NoRes *)
Compute (run 0 (repeat (Some 12) (fun x =>
                                    let! s := take 1 in
                                    let! v := read s 0 in
                                    ret (x + val v)) 0)
           [_8 50;_8 1;_8 2;_8 3;_8 4;_8 5;_8 6;_8 7;_8 8;_8 9]
           (mk_span 0 10)).
