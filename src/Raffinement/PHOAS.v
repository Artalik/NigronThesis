From Formalisation Require Import String SizeNat Vector Span.
From stdpp Require Import numbers.


Open Scope N_scope.

Section Syntax.

  Context {var : Type -> Type}.

  Inductive OpBin : Type -> Type -> Type -> Type :=
  | EAdd : OpBin N N N
  | ESub : OpBin N N N
  | EMult : OpBin N N N
  | EDiv : OpBin N N N
  | EMod : OpBin N N N
  | EEq : OpBin N N bool
  | ELe : OpBin N N bool
  | ELt : OpBin N N bool
  | EAnd : OpBin bool bool bool
  | EOr : OpBin bool bool bool
  | EStringGet : OpBin N string nat8
  | EPair : forall {X Y}, OpBin X Y (X * Y)
  | EpTo2p: forall {p: N}, OpBin (natN p) (natN p) (natN (2 * p))
  | EGetVec : forall {X}, OpBin (VECTOR X) N (option X)
  | EAddVec : forall {X}, OpBin (VECTOR X) X (VECTOR X).

  Inductive OpUna : Type -> Type -> Type :=
  | EVal : forall {len}, OpUna (natN len) N
  | ENot : OpUna bool bool
  | EStringLen : OpUna string N
  | EFst : forall {X Y}, OpUna (X * Y) X
  | ESnd : forall {X Y}, OpUna (X * Y) Y
  | ESome : forall {X}, OpUna X (option X)
  | EInl : forall {X Y}, OpUna X (X + Y)
  | EInr : forall {X Y}, OpUna Y (X + Y)
  | ELen : OpUna span N
  | EMake : forall {X}, OpUna N (VECTOR X).

  Inductive Literal : Type -> Type :=
  | ENat : N -> Literal N
  | ENatN : forall {len}, natN len -> Literal (natN len)
  | EBool : bool -> Literal bool
  | EString : string -> Literal string
  | ENone : forall {X}, Literal (option X)
  | EUnit : Literal unit.


  Inductive VAL : Type -> Type :=
  | Var : forall {X}, var X -> VAL X
  | EBin : forall {X Y Z}, OpBin X Y Z -> VAL X -> VAL Y -> VAL Z
  | EUna : forall {X Y}, OpUna X Y -> VAL X -> VAL Y
  | Const : forall {X}, Literal X -> VAL X.

  Inductive LIST :=
  | NIL : LIST
  | CONS : forall {X}, VAL X -> LIST -> LIST.

  Inductive PHOAS : Type -> Type :=
  | Cstruct : string -> string -> LIST -> forall {X}, PHOAS X
  | Val : forall {X}, VAL X -> PHOAS X
  | LetIn : forall {X}, PHOAS X -> forall {Y}, (var X -> PHOAS Y) -> PHOAS Y

  | IfThenElse : VAL bool -> forall {X}, PHOAS X -> PHOAS X -> PHOAS X
  | CaseOption : forall {X}, VAL (option X)  -> forall {Y}, PHOAS Y -> (var X -> PHOAS Y) -> PHOAS Y
  | Switch : VAL N -> forall {X}, case_switch X -> PHOAS X

  | Fail : forall {X}, PHOAS X
  | Take : VAL N -> PHOAS span
  | Length : PHOAS N
  | Read : VAL span -> VAL N -> PHOAS nat8
  | Alt : forall {X}, PHOAS X -> PHOAS X -> PHOAS X
  | Local : VAL (option span) -> forall {X}, PHOAS X -> PHOAS X
  | Repeat  : VAL (option N) -> forall {X}, (var X -> PHOAS X) -> VAL X -> PHOAS X

  with case_switch : Type -> Type :=
  | LSnil : forall {X}, PHOAS X -> case_switch X
  | LScons : N -> forall {X}, PHOAS X -> case_switch X -> case_switch X.

End Syntax.

Notation "'let%' v ':=' e 'in' k" := (LetIn e (fun v => k))(at level 50).
Notation "'If' b 'Then' et 'Else' ef" := (IfThenElse b et ef)(at level 50).
Notation "b0 '<!' b1" := (EBin ELt b0 b1)(at level 30).
Notation "b0 '<=!' b1" := (EBin ELe b0 b1)(at level 30).
Notation "n0 '+!' n1" := (EBin EAdd n0 n1)(at level 25, left associativity).
Notation "n0 '-!' n1" := (EBin ESub n0 n1)(at level 25, left associativity).
Notation "'(!' a ',' b ')'" := (EBin EPair a b)(at level 25, left associativity).
Notation "↓ n" := (SizeNat.val n)(at level 20).

Section sem_PHOAS.

  Fixpoint lengthN {X} (l : list X) : N :=
    match l with
    | [] => 0
    | _ :: t => N.succ (lengthN t)
    end.

  Inductive val : Type -> Type :=
  | VNat : N -> val N
  | VNatN : forall {len}, natN len -> val (natN len)
  | VBool : bool -> val bool
  | VString : string -> val string
  | VSpan : span -> val span
  | VUnit : val unit
  | VVec : forall {X}, VECTOR X -> val (VECTOR X)
  | VPair : forall {X Y}, val X -> val Y -> val (X * Y)
  | VFst : forall {X Y}, val (X * Y) -> val X
  | VSnd : forall {X Y}, val (X * Y) -> val Y
  | VSome : forall {X}, val X -> val (option X)
  | VNone : forall {X}, val (option X)
  | VInl : forall {X Y}, val X -> val (X + Y)
  | VInr : forall {X Y}, val Y -> val (X + Y)
  | VGetVec : forall {X}, val (VECTOR X) -> val N -> val (option X).

  (* Inductive sem_val : forall {X}, val X -> X -> Prop := *)
  (* | RVString : forall v, sem_val (VString v) v *)
  (* | RVSpan : forall v, sem_val (VSpan v) v *)
  (* | RVBool : forall v, sem_val (VBool v) v *)
  (* | RVNatN : forall len (v : natN len), sem_val (VNatN v) v *)
  (* | RVNat : forall v, sem_val (VNat v) v *)
  (* | RVPair : forall X Y vf (f : X) vs (s : Y), *)
  (*     sem_val vf f -> *)
  (*     sem_val vs s -> *)
  (*     sem_val (VPair vf vs) (f,s) *)
  (* | RVFst : forall X Y vf (f : X * Y), *)
  (*     sem_val vf f -> *)
  (*     sem_val (VFst vf) f.1 *)
  (* | RVSnd : forall X Y vf (f : X * Y), *)
  (*     sem_val vf f -> *)
  (*     sem_val (VSnd vf) f.2 *)
  (* | RVSome : forall X vf (f : X), *)
  (*     sem_val vf f -> *)
  (*     sem_val (VSome vf) (Some f) *)
  (* | RVNone : forall X, sem_val VNone (None :option X) *)
  (* | RVInl : forall X Y vf f, *)
  (*     sem_val vf f -> *)
  (*     sem_val (VInl vf) (inl f : X + Y) *)
  (* | RVInr : forall X Y vf f, *)
  (*     sem_val vf f -> *)
  (*     sem_val (VInr vf) (inr f : X + Y) *)
  (* . *)

  Fixpoint sem_val {X} (v : val X) : X :=
    match v with
    | VVec v | VString v | VSpan v | VBool v | VNatN v | VNat v => v
    | VUnit => tt
    | VPair x y => (sem_val x, sem_val y)
    | VFst x => (sem_val x).1
    | VSnd x => (sem_val x).2
    | VSome x => Some (sem_val x)
    | VNone => None
    | VInl x => inl (sem_val x)
    | VInr x => inr (sem_val x)
    | VGetVec vec n => Vector.get (sem_val vec) (sem_val n)
    end.

  Definition PHOASV : Type -> Type := @PHOAS val.

  Lemma zero_is_u8 : 0 < 2 ^ 8. simpl. lia. Qed.

  Lemma sub_natN : forall len (n0 n1 : natN len), ↓ n0 - ↓ n1 < 2 ^ len.
  Proof. intros len [v0 P0] [v1 P1]. simpl. lia. Qed.

  Lemma div_natN : forall len (n0 n1 : natN len), ↓ n1 > 0 -> ↓ n0 / ↓ n1 < 2 ^ len.
  Proof.
    intros len [v0 P0] [v1 P1] LT. simpl in *. eapply (N.le_lt_trans _ v0); auto.
    transitivity (v1 * v0 `div` v1). 2 : eapply N.mul_div_le; lia.
    rewrite <- (N.mul_1_l (v0 `div` v1)) at 1. eapply N.mul_le_mono_r. lia.
  Qed.

  Lemma mod_natN : forall len (n0 n1 : natN len), ↓ n1 > 0 -> ↓ n0 `mod` ↓ n1 < 2 ^ len.
  Proof.
    intros len [v0 P0] [v1 P1] LT. simpl in *. transitivity v1; auto.
    eapply N.mod_lt. lia.
  Qed.

  (* 12 rules *)
  Inductive sem_bin : forall {X Y} Z, OpBin X Y Z -> val X -> val Y -> val Z -> Prop :=
  | SAdd : forall vn0 n0 vn1 n1,
      sem_val vn0 = n0 ->
      sem_val vn1 = n1 ->
      sem_bin N EAdd vn0 vn1 (VNat (n0 + n1))
  | SSub : forall vn0 n0 vn1 n1,
      sem_val vn0 = n0 ->
      sem_val vn1 = n1 ->
      sem_bin N ESub vn0 vn1 (VNat (n0 - n1))
  | SMult :  forall vn0 n0 vn1 n1,
      sem_val vn0 = n0 ->
      sem_val vn1 = n1 ->
      sem_bin N EMult vn0 vn1 (VNat (n0 * n1))
  | SDiv : forall vn0 n0 vn1 n1,
      sem_val vn0 = n0 ->
      sem_val vn1 = n1 ->
      sem_bin N EDiv vn0 vn1 (VNat (n0 / n1))
  | SMod : forall vn0 n0 vn1 n1,
      sem_val vn0 = n0 ->
      sem_val vn1 = n1 ->
      sem_bin N EMod vn0 vn1 (VNat (n0 `mod` n1))
  | SEq : forall vn0 n0 vn1 n1,
      sem_val vn0 = n0 ->
      sem_val vn1 = n1 ->
      sem_bin bool EEq vn0 vn1 (VBool (n0 =? n1))
  | SLe : forall vn0 n0 vn1 n1,
      sem_val vn0 = n0 ->
      sem_val vn1 = n1 ->
      sem_bin bool ELe vn0 vn1 (VBool (n0 <=? n1))
  | SLt : forall vn0 n0 vn1 n1,
      sem_val vn0 = n0 ->
      sem_val vn1 = n1 ->
      sem_bin bool ELt vn0 vn1 (VBool (n0 <? n1))
  | SAnd : forall vb0 b0 vb1 b1,
      sem_val vb0 = b0 ->
      sem_val vb1 = b1 ->
      sem_bin bool EAnd vb0 vb1 (VBool (b0 && b1))
  | SOr :forall vb0 b0 vb1 b1,
      sem_val vb0 = b0 ->
      sem_val vb1 = b1 ->
      sem_bin bool EOr vb0 vb1 (VBool (b0 || b1))
  | SStringGet : forall vs s vn n r,
      sem_val vn = n ->
      sem_val vs = s ->
      string_get n s = Some r ->
      sem_bin nat8 EStringGet vn vs (VNatN r)
  | SPair : forall X Y n0 n1,
      sem_bin (X * Y) EPair n0 n1 (VPair n0 n1)
  | SpTo2p: forall len vn0 vn1 (n0 n1 : natN len),
      sem_val vn0 = n0 ->
      sem_val vn1 = n1 ->
      sem_bin (natN (2 * len)) EpTo2p vn0 vn1 (VNatN (n0 ↑ n1))
  | SGetVec : forall X vvec vn,
      sem_bin (option X) EGetVec vvec vn (VGetVec vvec vn)
  | SAddVec : forall X vvec vec vx x,
      sem_val vvec = vec ->
      sem_val vx = x ->
      sem_bin (VECTOR X) EAddVec vvec vx (VVec (Vector.add vec x)).

  (* 10 rules *)
  Inductive sem_unary : forall {X} Y, OpUna X Y -> val X -> val Y -> Prop :=
  | SEVal : forall len vn (n : natN len),
      sem_val vn = n ->
      sem_unary N EVal vn (VNat (↓ n))
  | SNot : forall vb b,
      sem_val vb = b ->
      sem_unary bool ENot vb (VBool (negb b))
  | SStringLenOK : forall (vs : val string) s,
      sem_val vs = s ->
      sem_unary _ EStringLen vs (VNat (string_length s))
  | SFst : forall X Y (v : val (X * Y)),
      sem_unary X EFst v (VFst v)
  | SSnd : forall X Y (v : val (X * Y)),
      sem_unary Y ESnd v (VSnd v)
  | SSome : forall X n,
      sem_unary (option X) ESome n (VSome n)
  | SInl : forall X Y v,
      sem_unary (X + Y) EInl v (VInl v)
  | SInr : forall X Y v,
      sem_unary (X + Y) EInr v (VInr v)
  | SLen : forall vs s,
      sem_val vs = s ->
      sem_unary N ELen vs (VNat (len s))
  | SMake : forall X vn n,
      sem_val vn = n ->
      sem_unary (VECTOR X)EMake vn (VVec (Vector.make X n)).

  (* 4 rules *)
  Inductive sem_literal : forall {X : Type}, Literal X -> val X -> Prop :=
  | SNat : forall n,
        sem_literal (ENat n) (VNat n)
  | SNatN : forall len (n : natN len),
      sem_literal (ENatN n) (VNatN n)
  | SBool : forall b,
      sem_literal (EBool b) (VBool b)
  | SString : forall s,
      sem_literal (EString s) (VString s)
  | SNone : forall X,
      sem_literal (ENone : Literal (option X)) VNone
  | SUnit : sem_literal EUnit VUnit.

  (* 4 rules *)
  Inductive sem_VAL: forall {X}, @VAL val X -> val X -> Prop :=
  | SVar : forall X (v : val X), sem_VAL (Var v) v
  | SBin : forall X Y Z (ob : OpBin X Y Z) (vv0 : VAL X) (vv1 : VAL Y) v0 v1 res,
      sem_VAL vv0 v0 ->
      sem_VAL vv1 v1 ->
      sem_bin Z ob v0 v1 res ->
      sem_VAL (EBin ob vv0 vv1) res
  | SUna : forall X Y (ou : OpUna X Y) (vv0 : VAL X) v0 res,
      sem_VAL vv0 v0 ->
      sem_unary Y ou v0 res ->
      sem_VAL (EUna ou vv0) res
  | SConst : forall X (lit : Literal X) v,
      sem_literal lit v ->
      sem_VAL (Const lit) v.

  (* 20 rules *)
  Inductive sem_PHOAS (data : list nat8):
      forall {X : Type}, span -> PHOASV X  -> option (val X * span) -> Prop :=
  | SCstruct : forall X ty f l v s,
      sem_PHOAS data s (Cstruct ty f l : PHOAS X) (Some (v, s))

  | SVal : forall X (vv : VAL X) v s,
      sem_VAL vv v ->
      sem_PHOAS data s (Val vv) (Some (v,s))

  | SLetInS : forall (X Y : Type) (e : PHOASV X) (f : val X -> PHOASV Y)  v res p0 p1,
      sem_PHOAS data p0 e (Some (v,p1)) ->
      sem_PHOAS data p1 (f v) res ->
      sem_PHOAS data p0 (LetIn e f) res
  | SLetInF : forall (X Y : Type) (e : PHOASV X) (f : val X -> PHOASV Y) p0,
      sem_PHOAS data p0 e None ->
      sem_PHOAS data p0 (LetIn e f) None

  | sem_IfThenElseT : forall vb X (et ee : PHOASV X) res s,
      sem_VAL vb (VBool true) ->
      sem_PHOAS data s et res ->
      sem_PHOAS data s (IfThenElse vb et ee) res
  | sem_IfThenElseF : forall vb X (et ee : PHOASV X) res s,
      sem_VAL vb (VBool false) ->
      sem_PHOAS data s ee res ->
      sem_PHOAS data s (IfThenElse vb et ee) res

  | SCaseOptionNone : forall X (vo : VAL (option X)) Y (eN : PHOASV Y) eOpt res p,
      sem_VAL vo VNone ->
      sem_PHOAS data p eN res ->
      sem_PHOAS data p (CaseOption vo eN eOpt) res
  | SCaseOptionSome : forall X (vo : VAL (option X)) Y (eN : PHOASV Y) eOpt v res p,
      sem_VAL vo (VSome v) ->
      sem_PHOAS data p (eOpt v) res ->
      sem_PHOAS data p (CaseOption vo eN eOpt) res

  | sem_Switch : forall vn p n X (cases : case_switch X) res,
      sem_VAL vn (VNat n) ->
      sem_switch_cases data p n cases res ->
      sem_PHOAS data p (Switch vn cases) res

  | SFail : forall p0 X, sem_PHOAS data p0 (Fail : PHOAS X) None

  | STake : forall (hn : VAL N) s n,
      sem_VAL hn (VNat n) ->
      sem_PHOAS data s (Take hn)
        (Some (VSpan (mk_span (pos s) n), mk_span (pos s + n) (len s - n)))

  | SLength: forall s,
      sem_PHOAS data s Length (Some (VNat (len s), s))

  | SRead : forall s hs hn range n v default,
      sem_VAL hs (VSpan range) ->
      sem_VAL hn (VNat n) ->
      nth (N.to_nat (pos range + n)) data default = v ->
      sem_PHOAS data s (Read hs hn) (Some (VNatN v,s))

  | SAlt1 : forall p0 X (e0 e1 : PHOASV X) v0 p1,
      sem_PHOAS data p0 e0 (Some (v0, p1)) ->
      sem_PHOAS data p0 (Alt e0 e1) (Some (v0, p1))
  | SAlt2 : forall p0 X (e0 e1 : PHOAS X) res,
      sem_PHOAS data p0 e0 None ->
      sem_PHOAS data p0 e1 res ->
      sem_PHOAS data p0 (Alt e0 e1) res

  | SScopeF : forall hs X (ex : PHOAS X) p s,
      sem_VAL hs (VSome (VSpan s)) ->
      sem_PHOAS data s ex None ->
      sem_PHOAS data p (Local hs ex) None
  | SScopeS : forall hs X (ex : PHOAS X) p s v p0,
      sem_VAL hs (VSome (VSpan s)) ->
      sem_PHOAS data s ex (Some (v, p0)) ->
      sem_PHOAS data p (Local hs ex) (Some (v, p))

  | SPeekF : forall hs X (ex : PHOAS X) p,
      sem_VAL hs VNone ->
      sem_PHOAS data p ex None ->
      sem_PHOAS data p (Local hs ex) None
  | SPeekS : forall hs X (ex : PHOAS X) p v p0,
      sem_VAL hs VNone ->
      sem_PHOAS data p ex (Some (v, p0)) ->
      sem_PHOAS data p (Local hs ex) (Some (v, p))

  | SRepeatN : forall von X (vb : VAL X) p ex base res,
      sem_VAL von VNone ->
      sem_VAL vb base ->
      sem_repeat_None data p ex base res ->
      sem_PHOAS data p (Repeat von ex vb) res

  | SRepeatS : forall p von n X ex (vb : VAL X) base res,
      sem_VAL von (VSome (VNat n)) ->
      sem_VAL vb base ->
      sem_repeat_Some data p n ex base res ->
      sem_PHOAS data p (Repeat von ex vb) res


  (* 2 rules *)
  with sem_repeat_None (data : list nat8) :
    forall {X}, span -> (val X -> PHOAS X) -> val X -> option (val X * span) -> Prop :=
  | SRepeatNF : forall X p e (base : val X),
    sem_PHOAS data p (e base) None ->
    sem_repeat_None data p e base (Some (base, p))
  | SRepeatNS : forall X p0 p1 e ve (base : val X) res,
      sem_PHOAS data p0 (e base) (Some (ve, p1)) ->
      sem_repeat_None data p1 e ve res ->
      sem_repeat_None data p0 e base res

  (* 3 rules *)
  with sem_repeat_Some (data : list nat8) :
    forall {X}, span -> N -> (val X -> PHOAS X) -> val X -> option (val X * span) -> Prop :=
  | SRepeatSO : forall X p e (base : val X),
      sem_repeat_Some data p 0 e base (Some (base, p))
  | SRepeatSS : forall X p0 p1 n e ve (base : val X) res,
      sem_PHOAS data p0 (e base) (Some (ve, p1)) ->
      sem_repeat_Some data p1 n e ve res ->
      sem_repeat_Some data p0 (N.succ n) e base res
  | SRepeatSF : forall X p n e (base : val X),
      sem_PHOAS data p (e base) None ->
      sem_repeat_Some data p (N.succ n) e base None


  (* 3 règles *)
  with sem_switch_cases (data : list nat8) : forall {X},
      span -> N -> case_switch X -> option (val X * span) -> Prop :=
  | SLSnil : forall (X : Type) (e : PHOAS X) res n p0,
      sem_PHOAS data p0 e res ->
      sem_switch_cases data p0 n (LSnil e) res
  | SLSconsEq : forall (X : Type) val (e : PHOAS X) n cases res p0,
      val = n ->
      sem_PHOAS data p0 e res ->
      sem_switch_cases data p0 val (LScons n e cases) res
  | SLSconsNEq : forall (X : Type) val n (e : PHOAS X) cases res p0,
      val <> n ->
      sem_switch_cases data p0 val cases res ->
      sem_switch_cases data p0 val (LScons n e cases) res.


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

  Lemma sem_val_inj : forall X (v : val X) res0 res1,
      sem_val v = res0 ->
      sem_val v = res1 ->
      res0 = res1.
  Proof.
    Local Ltac ind_val_inj IH :=
    match goal with
    | H : sem_val ?t _ |- _ =>
        head_constructor t; next_step H
    | H0 : sem_val ?t _, H1 : sem_val ?t _ |- _ =>
        injection (IH _ t _ _ H0 H1); clear H0; clear H1
    | H0 : sem_val ?t _, H1 : sem_val ?t _ |- _ =>
        eapply (IH _ t _ _ H0) in H1
    end.
    fix IH 2.
    destruct v; intros; repeat ind_val_inj IH; subst; try reflexivity.
  Qed.

  Lemma sem_bin_inj : forall X (v0 : val X) Y (v1 : val Y) Z o res1 res2,
      sem_bin Z o v0 v1 res1 ->
      sem_bin Z o v0 v1 res2 ->
      res1 = res2.
  Proof.
    Local Ltac ind_bin_inj IH :=
    match goal with
    | H : sem_bin _ ?t _ _ _ |- _ =>
        head_constructor t; next_step H
    | H0 : sem_bin _ ?t _ _ _, H1 : sem_bin _ ?t _ _ _ |- _ =>
        injection (IH _ t _ _ H0 H1); clear H0; clear H1
    | H0 : sem_bin _ ?t _ _ _, H1 : sem_bin _ ?t _ _ _ |- _ =>
        eapply (IH _ t _ _ H0) in H1
    end.
    fix IH 6.
    destruct o; intros; repeat ind_bin_inj IH; intros; simpl_existT; subst; try reflexivity.
    rewrite H6 in H5. injection H5; intro; subst; reflexivity.
  Qed.

  Lemma sem_unary_inj : forall X (v0 : val X) Y o res1 res2,
      sem_unary Y o v0 res1 ->
      sem_unary Y o v0 res2 ->
      res1 = res2.
  Proof.
    Local Ltac ind_unary_inj IH :=
    match goal with
    | H : sem_unary _ ?t _ _ |- _ =>
        head_constructor t; next_step H
    | H0 : sem_unary _ ?t _ _, H1 : sem_unary _ ?t _ _ |- _ =>
        injection (IH _ t _ _ H0 H1); clear H0; clear H1
    | H0 : sem_unary _ ?t _ _, H1 : sem_unary _ ?t _ _ |- _ =>
        eapply (IH _ t _ _ H0) in H1
    end.
    fix IH 4.
    destruct o; intros; repeat ind_unary_inj IH;
      repeat ind_val_inj sem_val_inj;  intros; simpl_existT; subst; try reflexivity.
  Qed.


  Lemma sem_literal_inj : forall X (v : Literal X) res1 res2,
      sem_literal v res1 ->
      sem_literal v res2 ->
      res1 = res2.
  Proof.
    Local Ltac ind_lit_inj IH :=
    match goal with
    | H : sem_literal ?t _ |- _ =>
        head_constructor t; next_step H
    | H0 : sem_literal ?t _, H1 : sem_literal ?t _ |- _ =>
        injection (IH _ t _ _ H0 H1); clear H0; clear H1
    | H0 : sem_literal ?t _, H1 : sem_literal ?t _ |- _ =>
        eapply (IH _ t _ _ H0) in H1
    end.
    fix IH 2.
    destruct v; intros; repeat ind_lit_inj IH; intros; simpl_existT; subst; try reflexivity.
  Qed.

  Lemma sem_VAL_inj : forall X (v : VAL X) res1 res2,
      sem_VAL v res1 ->
      sem_VAL v res2 ->
      res1 = res2.
  Proof.
    Local Ltac ind_inj IH :=
    match goal with
    | H : sem_VAL ?t _ |- _ =>
        head_constructor t; next_step H
    | H0 : sem_VAL ?t _, H1 : sem_VAL ?t _ |- _ =>
        injection (IH _ t _ _ H0 H1); clear H0; clear H1
    | H0 : sem_VAL ?t _, H1 : sem_VAL ?t _ |- _ =>
        eapply (IH _ t _ _ H0) in H1
    end.
    fix IH 2.
    destruct v; intros; repeat ind_inj IH; intros; simpl_existT; subst.
    - reflexivity.
    - eapply sem_bin_inj; eauto.
    - eapply sem_unary_inj; eauto.
    - eapply sem_literal_inj; eauto.
  Qed.

End sem_PHOAS.

Section PHOAS_equiv.

  Context {var1 var2 : Type -> Type}.

  Inductive Env :=
  | Nil : Env
  | Cons : forall {X}, var1 X -> var2 X -> Env -> Env.

  Inductive In {X} (v1 : var1 X) (v2 : var2 X) : Env -> Prop :=
  | Here : forall env, In v1 v2 (Cons v1 v2 env)
  | Later : forall X (t1 : var1 X) (t2 : var2 X) env,
      In v1 v2 env ->
      In v1 v2 (Cons t1 t2 env).

  Inductive equiv_VAL : Env -> forall X, @VAL var1 X -> @VAL var2 X -> Prop :=
  | EquivVar : forall X env v1 v2,
      In v1 v2 env ->
      equiv_VAL env X (Var v1) (Var v2)
  | EquivBin : forall X Y Z env o v1 v2 v3 v4,
      equiv_VAL env X v1 v3 ->
      equiv_VAL env Y v2 v4 ->
      equiv_VAL env Z (EBin o v1 v2) (EBin o v3 v4)
  | EquivUna : forall X Y env o v1 v3,
      equiv_VAL env X v1 v3 ->
      equiv_VAL env Y (EUna o v1) (EUna o v3)
  | EquivConst : forall X env c,
      equiv_VAL env X (Const c) (Const c).

  Inductive equiv_LIST : Env -> @LIST var1 -> @LIST var2 -> Prop :=
  | EquivNIL : forall env,
      equiv_LIST env NIL NIL
  | EquivCONS : forall env X v1 v2 l1 l2,
      equiv_VAL env X v1 v2 ->
      equiv_LIST env l1 l2 ->
      equiv_LIST env (CONS v1 l1) (CONS v2 l2).

  Inductive equiv_prog : Env -> forall X, @PHOAS var1 X -> @PHOAS var2 X -> Prop :=
  | EquivCstruct : forall env X ty constr l1 l2,
    equiv_LIST env l1 l2 ->
    equiv_prog env X (Cstruct ty constr l1) (Cstruct ty constr l2)
  | EquivVal : forall X env v1 v2,
      equiv_VAL env X v1 v2 ->
      equiv_prog env X (Val v1) (Val v2)
  | EquivLetIn : forall X Y env e0 e1 k0 k1,
      equiv_prog env X e0 e1 ->
      (forall v0 v1, equiv_prog (Cons v0 v1 env) Y (k0 v0) (k1 v1)) ->
      equiv_prog env Y (LetIn e0 k0) (LetIn e1 k1)
  | EquivIfThenElse : forall X env vb1 vb2 et1 et2 ef1 ef2,
      equiv_VAL env bool vb1 vb2 ->
      equiv_prog env X et1 et2 ->
      equiv_prog env X ef1 ef2 ->
      equiv_prog env X (IfThenElse vb1 et1 ef1) (IfThenElse vb2 et2 ef2)
  | EquivCaseOption : forall X Y env vo1 vo2 en1 en2 es1 es2,
      equiv_VAL env (option X) vo1 vo2 ->
      equiv_prog env Y en1 en2 ->
      (forall v0 v1, equiv_prog (Cons v0 v1 env) Y (es1 v0) (es2 v1)) ->
      equiv_prog env Y (CaseOption vo1 en1 es1) (CaseOption vo2 en2 es2)
  | EquivSwitch : forall Y env vn1 vn2 c1 c2,
      equiv_VAL env N vn1 vn2 ->
      equiv_branch env Y c1 c2 ->
      equiv_prog env Y (Switch vn1 c1) (Switch vn2 c2)
  | EquivFail : forall Y env,
      equiv_prog env Y Fail Fail
  | EquivTake : forall env vn1 vn2,
      equiv_VAL env N vn1 vn2 ->
      equiv_prog env span (Take vn1) (Take vn2)
  | EquivLength : forall env,
      equiv_prog env N Length Length
  | EquivRead : forall env vs1 vs2 vn1 vn2,
      equiv_VAL env span vs1 vs2 ->
      equiv_VAL env N vn1 vn2 ->
      equiv_prog env nat8 (Read vs1 vn1) (Read vs2 vn2)
  | EquivAlt : forall X env e1 e2 e3 e4,
      equiv_prog env X e1 e3 ->
      equiv_prog env X e2 e4 ->
      equiv_prog env X (Alt e1 e2) (Alt e3 e4)
  | EquivLocal : forall X env vo1 vo2 e1 e2,
      equiv_VAL env (option span) vo1 vo2 ->
      equiv_prog env X e1 e2 ->
      equiv_prog env X (Local vo1 e1) (Local vo2 e2)
  | EquivRepeat : forall X env on1 on2 k1 k2 b1 b2,
      equiv_VAL env (option N) on1 on2 ->
      (forall v1 v2, equiv_prog (Cons v1 v2 env) X (k1 v1) (k2 v2)) ->
      equiv_VAL env X b1 b2 ->
      equiv_prog env X (Repeat on1 k1 b1) (Repeat on2 k2 b2)

  with equiv_branch : Env -> forall X, @case_switch var1 X -> @case_switch var2 X -> Prop :=
  | EquivLSNil : forall X env e1 e2,
      equiv_prog env X e1 e2 ->
      equiv_branch env X (LSnil e1) (LSnil e2)
  | EquivLSCons : forall X env n e1 e2 cs1 cs2,
      equiv_prog env X e1 e2 ->
      equiv_branch env X cs1 cs2 ->
      equiv_branch env X (LScons n e1 cs1) (LScons n e2 cs2).

End PHOAS_equiv.

Definition exotic_term : @PHOAS val N :=
  let% v := Take (Const (ENat 2)) in
  match v with
  | VSpan s => Val (Const (ENat (pos s)))
  | _ => Val (Const (ENat 0))
  end.

Definition equiv_exotic :
  {code : @PHOAS (fun _ => string) N | equiv_prog Nil N exotic_term code}.
  eapply exist. repeat econstructor. intros. Abort.


Definition Expr X := forall (var : Type -> Type), @PHOAS var X.

Section flatten.

  Context {var : Type -> Type}.

  Fixpoint flatten_VAL {X} (p : @VAL (@VAL var) X) {struct p}: @VAL var X :=
    match p with
    | Var v => v
    | EBin o v0 v1 => EBin o (flatten_VAL v0) (flatten_VAL v1)
    | EUna u v0 => EUna u (flatten_VAL v0)
    | Const l => Const l
    end.

  Fixpoint flatten_LIST (l : @LIST (@VAL var)) : @LIST var :=
    match l with
    | NIL => NIL
    | CONS v l => CONS (flatten_VAL v) (flatten_LIST l)
    end.

  Fixpoint flatten {X} (e : @PHOAS (@VAL var) X) {struct e}: @PHOAS var X :=
    match e with
    | Cstruct ty constr l => Cstruct ty constr (flatten_LIST l)
    | Val v => Val (flatten_VAL v)
    | LetIn e k => LetIn (flatten e) (fun v => flatten (k (Var v)))
    | IfThenElse vb et ef => IfThenElse (flatten_VAL vb) (flatten et) (flatten ef)
    | CaseOption eo en es =>
        CaseOption (flatten_VAL eo) (flatten en) (fun v => flatten (es (Var v)))
    | Switch en c => Switch (flatten_VAL en) (flatten_cases c)
    | Fail => Fail
    | Take en => Take (flatten_VAL en)
    | Length => Length
    | Read es en => Read (flatten_VAL es) (flatten_VAL en)
    | Alt ef es => Alt (flatten ef) (flatten es)
    | Local eo ex => Local (flatten_VAL eo) (flatten ex)
    | Repeat on k eb => Repeat (flatten_VAL on) (fun v => flatten (k (Var v))) (flatten_VAL eb)
    end
  with flatten_cases {X} (cs : @case_switch (@VAL var) X) {struct cs}: @case_switch var X :=
         match cs with
         | LSnil e => LSnil (flatten e)
         | LScons n e cs => LScons n (flatten e) (flatten_cases cs)
         end.

End flatten.

Close Scope N_scope.
