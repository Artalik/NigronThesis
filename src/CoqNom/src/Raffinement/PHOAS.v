From Formalisation Require Import String SizeNat Vector Span.
From stdpp Require Import numbers.

Open Scope N_scope.

Section Syntax.

(* =type= *)
Inductive type : Type :=
| Nat
| NatN : N -> type
| Bool
| Vector : type -> type
| String
| Unit
| Span
| Unknown : string -> type
| Option : type -> type
| Pair : type -> type -> type
| Sum : type -> type -> type.
(* =end= *)

(* =type_to_Type= *)
Fixpoint type_to_Type (ty : type) : Type :=
  match ty with
  | Nat => N
  | NatN n => natN n
  | Bool => bool
  | Vector ty => VECTOR (type_to_Type ty)
  | String => string
  | Unit => unit
  | Span => span
  | Option ty => option (type_to_Type ty)
  | Pair ty0 ty1 => type_to_Type ty0 * type_to_Type ty1
  | Sum ty0 ty1 => type_to_Type ty0 + type_to_Type ty1
  | Unknown s => True
  end.
(* =end= *)

Fixpoint type_eq_dec (x y : type) : {x = y} + {x ≠ y}.
  Local Ltac type_eq_dec_tac :=
    match goal with
    | |- {?l = ?l} + {_ ≠ _} => eapply left; reflexivity
    | |- {?l = ?r} + {_ ≠ _} => eapply right; intro H; inversion H; done
    end.
  destruct x,y; try type_eq_dec_tac.
  destruct (N.eq_dec n n0).
  left. subst. reflexivity.
  right. intro. eapply n1. inversion H. reflexivity.
  destruct (type_eq_dec x y).
  left. subst. reflexivity.
  right. intro. eapply n. inversion H. reflexivity.
  destruct (string_dec s s0).
  left. subst. reflexivity.
  right. intro. eapply n. inversion H. reflexivity.
  destruct (type_eq_dec x y).
  left. subst. reflexivity.
  right. intro. eapply n. inversion H. reflexivity.
  destruct (type_eq_dec x1 y1).
  destruct (type_eq_dec x2 y2).
  left. subst. reflexivity.
  right. intro. eapply n. inversion H. reflexivity.
  right. intro. eapply n. inversion H. reflexivity.
  destruct (type_eq_dec x1 y1).
  destruct (type_eq_dec x2 y2).
  left. subst. reflexivity.
  right. intro. eapply n. inversion H. reflexivity.
  right. intro. eapply n. inversion H. reflexivity.
Defined.

  Context {var : type -> Type}.

  Inductive OpBin : type -> type -> type -> Type :=
  | EAdd : OpBin Nat Nat Nat
  | ESub : OpBin Nat Nat Nat
  | EMult : OpBin Nat Nat Nat
  | EDiv : OpBin Nat Nat Nat
  | EMod : OpBin Nat Nat Nat
  | EEq : OpBin Nat Nat Bool
  | ELe : OpBin Nat Nat Bool
  | ELt : OpBin Nat Nat Bool
  | EAnd : OpBin Bool Bool Bool
  | EOr : OpBin Bool Bool Bool
  | EStringGet : OpBin Nat String (NatN 8)
  | EPair : forall {X Y}, OpBin X Y (Pair X Y)
  | EpTo2p: forall {p: N}, OpBin (NatN p) (NatN p) (NatN (2 * p))
  | EGetVec : forall {X}, OpBin (Vector X) Nat (Option X)
  | EAddVec : forall {X}, OpBin (Vector X) X (Vector X).

  Inductive OpUna : type -> type -> Type :=
  | EVal : forall {len}, OpUna (NatN len) Nat
  | ENot : OpUna Bool Bool
  | EStringLen : OpUna String Nat
  | EFst : forall {X Y}, OpUna (Pair X Y) X
  | ESnd : forall {X Y}, OpUna (Pair X Y) Y
  | ESome : forall {X}, OpUna X (Option X)
  | EInl : forall {X Y}, OpUna X (Sum X Y)
  | EInr : forall {X Y}, OpUna Y (Sum X Y)
  | ELen : OpUna Span Nat
  | EMake : forall {X}, OpUna Nat (Vector X).

  Inductive Literal : type -> Type :=
  | ENat : N -> Literal Nat
  | ENatN : forall {len}, natN len -> Literal (NatN len)
  | EBool : bool -> Literal Bool
  | EString : string -> Literal String
  | ENone : forall {X}, Literal (Option X)
  | EUnit : Literal Unit.

  Inductive VAL : type -> Type :=
  | Var : forall {X}, var X -> VAL X
  | EBin : forall {X Y Z}, OpBin X Y Z -> VAL X -> VAL Y -> VAL Z
  | EUna : forall {X Y}, OpUna X Y -> VAL X -> VAL Y
  | Const : forall {X}, Literal X -> VAL X.

  Inductive LIST :=
  | NIL : LIST
  | CONS : forall {X}, VAL X -> LIST -> LIST.

  Inductive PHOAS : type -> Type :=
  | ExternStruct : forall (ty : string), string -> LIST -> PHOAS (Unknown ty)
  | Val : forall {X}, VAL X -> PHOAS X
  | LetIn : forall {X}, PHOAS X -> forall {Y}, (var X -> PHOAS Y) -> PHOAS Y

  | IfThenElse : VAL Bool -> forall {X}, PHOAS X -> PHOAS X -> PHOAS X
  | CaseOption : forall {X}, VAL (Option X)  -> forall {Y}, PHOAS Y -> (var X -> PHOAS Y) -> PHOAS Y
  | Switch : VAL Nat -> forall {X}, case_switch X -> PHOAS X

  | Fail : forall {X}, PHOAS X
  | Take : VAL Nat -> PHOAS Span
  | Length : PHOAS Nat
  | Read : VAL Span -> VAL Nat -> PHOAS (NatN 8)
  | Alt : forall {X}, PHOAS X -> PHOAS X -> PHOAS X
  | Local : VAL (Option Span) -> forall {X}, PHOAS X -> PHOAS X
  | Repeat  : VAL (Option Nat) -> forall {X}, (var X -> PHOAS X) -> VAL X -> PHOAS X

  with case_switch : type -> Type :=
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

  Definition val := type_to_Type.

  Definition PHOASV : type -> Type := @PHOAS val.

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
  | SAdd : forall n0 n1,
      (* sem_val vn0 = n0 -> *)
      (* sem_val vn1 = n1 -> *)
      sem_bin Nat EAdd n0 n1 (n0 + n1)
  | SSub : forall n0 n1,
      sem_bin Nat ESub n0 n1 (n0 - n1)
  | SMult :  forall n0 n1,
      sem_bin Nat EMult n0 n1 (n0 * n1)
  | SDiv : forall n0 n1,
      sem_bin Nat EDiv n0 n1 (n0 / n1)
  | SMod : forall n0 n1,
      sem_bin Nat EMod n0 n1 (n0 `mod` n1)
  | SEq : forall n0 n1,
      sem_bin Bool EEq n0 n1 (n0 =? n1)
  | SLe : forall n0 n1,
      sem_bin Bool ELe n0 n1 (n0 <=? n1)
  | SLt : forall n0 n1,
      sem_bin Bool ELt n0 n1 (n0 <? n1)
  | SAnd : forall b0 b1,
      sem_bin Bool EAnd b0 b1 (b0 && b1)
  | SOr :forall b0 b1,
      sem_bin Bool EOr b0 b1 (b0 || b1)
  | SStringGet : forall s n r,
      string_get n s = Some r ->
      sem_bin (NatN 8) EStringGet n s r
  | SPair : forall X Y n0 n1,
      sem_bin (Pair X Y) EPair n0 n1 (n0, n1)
  | SpTo2p: forall len n0 n1,
      sem_bin (NatN (2 * len)) EpTo2p n0 n1 (n0 ↑ n1)
  | SGetVec : forall X vec n,
      sem_bin (Option X) EGetVec vec n (get vec n)
  | SAddVec : forall ty (vec : VECTOR (type_to_Type ty)) x,
      sem_bin (Vector ty) EAddVec vec x (Vector.add vec x).

  (* 10 rules *)
  Inductive sem_unary : forall {X} Y, OpUna X Y -> val X -> val Y -> Prop :=
  | SEVal : forall len (n : val (NatN len)),
      sem_unary Nat EVal n (↓ n)
  | SNot : forall b,
      sem_unary Bool ENot b (negb b)
  | SStringLenOK : forall s,
      sem_unary Nat EStringLen s (string_length s)
  | SFst : forall X Y (v : val (Pair X Y)),
      sem_unary X EFst v (v.1)
  | SSnd : forall X Y (v : val (Pair X Y)),
      sem_unary Y ESnd v (v.2)
  | SSome : forall X n,
      sem_unary (Option X) ESome n (Some n)
  | SInl : forall X Y v,
      sem_unary (Sum X Y) EInl v (inl v)
  | SInr : forall X Y v,
      sem_unary (Sum X Y) EInr v (inr v)
  | SLen : forall s,
      sem_unary Nat ELen s (len s)
  | SMake : forall ty n,
      sem_unary (Vector ty) EMake n (Vector.make (type_to_Type ty) n).

  (* 4 rules *)
  Inductive sem_literal : forall {X : type}, Literal X -> val X -> Prop :=
  | SNat : forall n,
        sem_literal (ENat n) n
  | SNatN : forall len (n : natN len),
      sem_literal (ENatN n) n
  | SBool : forall b,
      sem_literal (EBool b) b
  | SString : forall s,
      sem_literal (EString s) s
  | SNone : forall X,
      sem_literal (ENone : Literal (Option X)) None
  | SUnit : sem_literal EUnit tt.

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
      forall {X : type}, span -> PHOASV X  -> option (val X * span) -> Prop :=
  | SExternStruct : forall ty f l v s,
      sem_PHOAS data s (ExternStruct ty f l) (Some (v, s))

  | SVal : forall X (vv : VAL X) v s,
      sem_VAL vv v ->
      sem_PHOAS data s (Val vv) (Some (v,s))

  | SLetInS : forall (X Y : type) (e : PHOASV X) (f : val X -> PHOASV Y)  v res p0 p1,
      sem_PHOAS data p0 e (Some (v,p1)) ->
      sem_PHOAS data p1 (f v) res ->
      sem_PHOAS data p0 (LetIn e f) res
  | SLetInF : forall (X Y : type) (e : PHOASV X) (f : val X -> PHOASV Y) p0,
      sem_PHOAS data p0 e None ->
      sem_PHOAS data p0 (LetIn e f) None

  | sem_IfThenElseT : forall vb X (et ee : PHOASV X) res s (b : val Bool),
      b = true ->
      sem_VAL vb b ->
      sem_PHOAS data s et res ->
      sem_PHOAS data s (IfThenElse vb et ee) res

  | sem_IfThenElseF : forall vb X (et ee : PHOASV X) res s (b : val Bool),
      b = false ->
      sem_VAL vb b ->
      sem_PHOAS data s ee res ->
      sem_PHOAS data s (IfThenElse vb et ee) res

  | SCaseOptionNone : forall X (vo : VAL (Option X)) Y (eN : PHOASV Y) eOpt res p,
      sem_VAL vo None ->
      sem_PHOAS data p eN res ->
      sem_PHOAS data p (CaseOption vo eN eOpt) res
  | SCaseOptionSome : forall X (vo : VAL (Option X)) Y (eN : PHOASV Y) eOpt v res p,
      sem_VAL vo (Some v) ->
      sem_PHOAS data p (eOpt v) res ->
      sem_PHOAS data p (CaseOption vo eN eOpt) res

  | sem_Switch : forall vn p (n : val Nat) X (cases : case_switch X) res,
      sem_VAL vn n ->
      sem_switch_cases data p n cases res ->
      sem_PHOAS data p (Switch vn cases) res

  | SFail : forall p0 X, sem_PHOAS data p0 (Fail : PHOAS X) None

  | STake : forall (hn : VAL Nat) s n,
      sem_VAL hn n ->
      sem_PHOAS data s (Take hn)
        (Some (mk_span (pos s) n, mk_span (pos s + n) (len s - n)))

  | SLength: forall s,
      sem_PHOAS data s Length (Some ((len s : val Nat), s))

  | SRead : forall s hs hn (range : val Span) (n : val Nat) v default,
      sem_VAL hs range ->
      sem_VAL hn n ->
      nth (N.to_nat (pos range + n)) data default = v ->
      sem_PHOAS data s (Read hs hn) (Some (v,s))

  | SAlt1 : forall p0 X (e0 e1 : PHOASV X) v0 p1,
      sem_PHOAS data p0 e0 (Some (v0, p1)) ->
      sem_PHOAS data p0 (Alt e0 e1) (Some (v0, p1))
  | SAlt2 : forall p0 X (e0 e1 : PHOAS X) res,
      sem_PHOAS data p0 e0 None ->
      sem_PHOAS data p0 e1 res ->
      sem_PHOAS data p0 (Alt e0 e1) res

  | SScopeF : forall hs X (ex : PHOAS X) p s (res : val (Option Span)),
      res = Some s ->
      sem_VAL hs res ->
      sem_PHOAS data s ex None ->
      sem_PHOAS data p (Local hs ex) None
  | SScopeS : forall hs X (ex : PHOAS X) p s v p0 (res : val (Option Span)),
      res = Some s ->
      sem_VAL hs res ->
      sem_PHOAS data s ex (Some (v, p0)) ->
      sem_PHOAS data p (Local hs ex) (Some (v, p))

  | SPeekF : forall hs X (ex : PHOAS X) p (res : val (Option Span)),
      res = None ->
      sem_VAL hs res ->
      sem_PHOAS data p ex None ->
      sem_PHOAS data p (Local hs ex) None
  | SPeekS : forall hs X (ex : PHOAS X) p v p0 (res : val (Option Span)),
      res = None ->
      sem_VAL hs res ->
      sem_PHOAS data p ex (Some (v, p0)) ->
      sem_PHOAS data p (Local hs ex) (Some (v, p))

  | SRepeatN : forall von X (vb : VAL X) p ex base res,
      sem_VAL von (None : val (Option Nat)) ->
      sem_VAL vb base ->
      sem_repeat_None data p ex base res ->
      sem_PHOAS data p (Repeat von ex vb) res

  | SRepeatS : forall p von n X ex (vb : VAL X) base res,
      sem_VAL von (Some n : val (Option Nat)) ->
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
  | SLSnil : forall (X : type) (e : PHOAS X) res n p0,
      sem_PHOAS data p0 e res ->
      sem_switch_cases data p0 n (LSnil e) res
  | SLSconsEq : forall (X : type) val (e : PHOAS X) n cases res p0,
      val = n ->
      sem_PHOAS data p0 e res ->
      sem_switch_cases data p0 val (LScons n e cases) res
  | SLSconsNEq : forall (X : type) val n (e : PHOAS X) cases res p0,
      val <> n ->
      sem_switch_cases data p0 val cases res ->
      sem_switch_cases data p0 val (LScons n e cases) res.


  Ltac simpl_existT :=
    repeat match goal with
      | H : existT _ _ = existT _ _ |- _ =>
          eapply Eqdep_dec.inj_pair2_eq_dec in H; [idtac | intros; eapply type_eq_dec]
      | H : existT _ _ = existT _ _ |- _ =>
          eapply Eqdep_dec.inj_pair2_eq_dec in H; [idtac | intros; eapply N.eq_dec]
      end.

  Ltac next_step H := inversion H; subst; simpl_existT; subst; clear H.


  Ltac head t :=
    match t with
    | ?t' _ => head t'
    | _ => t
    end.

  Ltac head_constructor t :=
    let t' := head t in is_constructor t'.

  (* Lemma sem_val_inj : forall X (v : val X) res0 res1, *)
  (*     sem_val v = res0 -> *)
  (*     sem_val v = res1 -> *)
  (*     res0 = res1. *)
  (* Proof. *)
  (*   Local Ltac ind_val_inj IH := *)
  (*   match goal with *)
  (*   | H : sem_val ?t _ |- _ => *)
  (*       head_constructor t(* ; next_step H *) *)
  (*   | H0 : sem_val ?t _, H1 : sem_val ?t _ |- _ => *)
  (*       injection (IH _ t _ _ H0 H1); clear H0; clear H1 *)
  (*   | H0 : sem_val ?t _, H1 : sem_val ?t _ |- _ => *)
  (*       eapply (IH _ t _ _ H0) in H1 *)
  (*   end. *)
  (*   fix IH 2. *)
  (*   destruct v; intros; repeat ind_val_inj IH; subst; try reflexivity. *)
  (* Qed. *)

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
        eapply (IH _ _ _ _ _ t _ _ H0) in H1
    end.
    fix IH 6.
    destruct o; intros; repeat ind_bin_inj IH; try reflexivity.
    match goal with
    | H0 : string_get v0 v1 = _,
        H1 : string_get v0 v1 = _ |- _ => rewrite H0 in H1; injection H1
    end. intro. auto.
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
    destruct o; intros; repeat ind_unary_inj IH; auto.
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

  Context {var1 var2 : type -> Type}.

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
  | EquivCstruct : forall env ty constr l1 l2,
    equiv_LIST env l1 l2 ->
    equiv_prog env (Unknown ty) (ExternStruct ty constr l1) (ExternStruct ty constr l2)
  | EquivVal : forall X env v1 v2,
      equiv_VAL env X v1 v2 ->
      equiv_prog env X (Val v1) (Val v2)
  | EquivLetIn : forall X Y env e0 e1 k0 k1,
      equiv_prog env X e0 e1 ->
      (forall v0 v1, equiv_prog (Cons v0 v1 env) Y (k0 v0) (k1 v1)) ->
      equiv_prog env Y (LetIn e0 k0) (LetIn e1 k1)
  | EquivIfThenElse : forall X env vb1 vb2 et1 et2 ef1 ef2,
      equiv_VAL env Bool vb1 vb2 ->
      equiv_prog env X et1 et2 ->
      equiv_prog env X ef1 ef2 ->
      equiv_prog env X (IfThenElse vb1 et1 ef1) (IfThenElse vb2 et2 ef2)
  | EquivCaseOption : forall X Y env vo1 vo2 en1 en2 es1 es2,
      equiv_VAL env (Option X) vo1 vo2 ->
      equiv_prog env Y en1 en2 ->
      (forall v0 v1, equiv_prog (Cons v0 v1 env) Y (es1 v0) (es2 v1)) ->
      equiv_prog env Y (CaseOption vo1 en1 es1) (CaseOption vo2 en2 es2)
  | EquivSwitch : forall Y env vn1 vn2 c1 c2,
      equiv_VAL env Nat vn1 vn2 ->
      equiv_branch env Y c1 c2 ->
      equiv_prog env Y (Switch vn1 c1) (Switch vn2 c2)
  | EquivFail : forall Y env,
      equiv_prog env Y Fail Fail
  | EquivTake : forall env vn1 vn2,
      equiv_VAL env Nat vn1 vn2 ->
      equiv_prog env Span (Take vn1) (Take vn2)
  | EquivLength : forall env,
      equiv_prog env Nat Length Length
  | EquivRead : forall env vs1 vs2 vn1 vn2,
      equiv_VAL env Span vs1 vs2 ->
      equiv_VAL env Nat vn1 vn2 ->
      equiv_prog env (NatN 8) (Read vs1 vn1) (Read vs2 vn2)
  | EquivAlt : forall X env e1 e2 e3 e4,
      equiv_prog env X e1 e3 ->
      equiv_prog env X e2 e4 ->
      equiv_prog env X (Alt e1 e2) (Alt e3 e4)
  | EquivLocal : forall X env vo1 vo2 e1 e2,
      equiv_VAL env (Option Span) vo1 vo2 ->
      equiv_prog env X e1 e2 ->
      equiv_prog env X (Local vo1 e1) (Local vo2 e2)
  | EquivRepeat : forall X env on1 on2 k1 k2 b1 b2,
      equiv_VAL env (Option Nat) on1 on2 ->
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

Definition exotic_term : @PHOAS val Unit :=
  let% v := Val (Const (EBool true)) in
  if (v : bool)
  then Val (Const EUnit)
  else Fail.

Definition equiv_exotic :
  {code : @PHOAS (fun _ => string) Unit | equiv_prog Nil Unit exotic_term code}.
  eapply exist. repeat econstructor. intros. Abort.

Definition Expr X := forall (var : type -> Type), @PHOAS var X.

Close Scope N_scope.
