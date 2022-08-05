From Equations Require Import Equations.
Require Import Ascii String.
Require Import FunctionalExtensionality.
From stdpp Require Import numbers.
Import N.

Open Scope N_scope.

Definition octet := N.

Definition data := list octet.

Definition Decodeur X := data -> option (X * data).

Definition decode {X} (d : Decodeur X) (l : data) : option X :=
 match d l with
 | None => None
 | Some (v, _) => Some v
 end.

Definition decode_pair : Decodeur (octet * octet) :=
  fun d =>
    match d with
    | [_] | [] => None
    | e0 :: e1 :: t => Some ((e0, e1), t)
    end.

Definition fmap {X Y} (f : X -> Y) (e : Decodeur X) : Decodeur Y :=
  fun d => match e d with
        | None => None
        | Some (v, s) => Some (f v, s)
        end.

Definition decode_add : Decodeur N :=
 fmap (fun v => fst v + snd v) decode_pair.

Definition decode_mult : Decodeur N :=
  fmap (fun v => fst v * snd v) decode_pair.

Reset decode_pair.


Definition fmap {X Y} (f : X -> Y) (e : Decodeur X) : Decodeur Y :=
  fun d => match e d with
        | None => None
        | Some (v, s) => Some (f v, s)
        end.


Lemma fmap_id : forall X (d : Decodeur X), fmap id d = d.
Proof.
  intros. unfold fmap. eapply FunctionalExtensionality.functional_extensionality.
  intros. destruct (d x) as [[v s]|]; reflexivity.
Qed.

Lemma fmap_comp : forall X Y Z (f: X -> Y) (g : Y -> Z), fmap (g ∘ f) = fmap g ∘ fmap f.
Proof.
  unfold fmap. unfold compose.
  intros. eapply FunctionalExtensionality.functional_extensionality.
  intros. eapply FunctionalExtensionality.functional_extensionality.
  intros. destruct (x x0) as [[v s]|]; reflexivity.
Qed.

Definition app {X Y} (f : Decodeur (X -> Y)) (x : Decodeur X) : Decodeur Y :=
  fun s => match f s with
        | None => None
        | Some (f,s) => fmap f x s
        end.

Notation " f '<*>' g" := (app f g)(at level 50).

Definition pure {X} : X -> Decodeur X := fun x s => Some (x,s).


Lemma app_id : forall X (v : Decodeur X), pure id <*> v = v.
Proof. intros. unfold app, pure. eapply fmap_id. Qed.

Lemma app_homo : forall X Y (f : X -> Y) x, pure f <*> pure x = pure (f x).
Proof.
  intros. unfold pure, app. eapply FunctionalExtensionality.functional_extensionality.
  intros. reflexivity.
Qed.

Lemma app_interchance : forall X Y (u : Decodeur (X -> Y)) y, u <*> pure y = pure (fun f => f y) <*> u.
Proof.
  intros. unfold app, pure, fmap. eapply FunctionalExtensionality.functional_extensionality.
  intros. reflexivity.
Qed.

Lemma app_composition : forall X Y Z (u : Decodeur (Y -> Z)) (v : Decodeur (X -> Y)) (w : Decodeur X),
    (pure (fun f g => f ∘ g)) <*> u <*> v <*> w = u <*> (v <*> w).
Proof.
  intros. unfold app, pure, fmap. eapply FunctionalExtensionality.functional_extensionality.
  intros. destruct (u x) as [[v0 s0]|]; auto. destruct (v s0) as [[v1 s1]|]; auto.
  destruct (w s1) as [[v2 s2]|]; auto.
Qed.

Definition decode_next : Decodeur octet :=
  fun d =>
    match d with
    | [] => None
    | h :: t => Some (h, t)
    end.

Definition decode_pair : Decodeur (octet * octet) :=
  pure (fun a b => (a,b)) <*> decode_next <*> decode_next.

Definition bind {X Y} (d : Decodeur X) (f : X -> Decodeur Y) : Decodeur Y :=
  fun s => match d s with
        | None => None
        | Some (v,s) => f v s
        end.

Notation "'let!' v ':=' f 'in' g" := (bind f (fun v => g))(at level 50).
Notation "'ret!' v" := (pure v)(at level 50).

Definition ret_bind : forall X Y v (f : X -> Decodeur Y), bind (ret! v) f = f v.
Proof.
  intros. unfold bind, pure. eapply FunctionalExtensionality.functional_extensionality.
  intros. reflexivity.
Qed.

Definition bind_ret : forall X (v : Decodeur X), bind v pure = v.
Proof.
  intros. unfold bind, pure. eapply FunctionalExtensionality.functional_extensionality.
  intros. destruct (v x) as [[v0 s]|]; reflexivity.
Qed.

Definition bind_assoc : forall X Y Z (v : Decodeur X) f (g : Y -> Decodeur Z),
    bind (bind v f) g = bind v (fun x => bind (f x) g).
Proof.
  intros. unfold bind, pure. eapply FunctionalExtensionality.functional_extensionality.
  intros. destruct (v x) as [[v0 s]|]; reflexivity.
Qed.

Definition to_u32 (a0 a1 a2 a3 : octet) : N :=
 a0 * (N.pow 2 32) + a1 * (N.pow 2 16) + a2  * (N.pow 2 8) + a3.

Definition decode_packet_length : Decodeur N :=
  pure to_u32 <*> decode_next <*> decode_next <*> decode_next <*> decode_next.

Equations take (n : N) (l : list N): option (list octet * list N) by wf (N.to_nat n) Nat.lt :=
  take 0 l := (ret! []) l;
  take n l :=
    match decode_next l with
    | None => None
    | Some (v, l) =>
        match take (N.pred n) l with
        | None => None
        | Some (vs, l) => Some (v :: vs, l)
        end
    end.
Next Obligation.
  lia.
Defined.

Equations take (n : N) : Decodeur data by wf (N.to_nat n) Nat.lt :=
 take 0 := ret! [];
 take n :=
   let! v := decode_next in
   let! vs := take (pred n) in
   ret! (v :: vs).
Next Obligation.
Abort.

Definition fail {X} : Decodeur X := fun _ => None.

Definition decode_payload_SSH : Decodeur data :=
  let! packet_length := decode_packet_length in
  let! padding_length := decode_next in
  if padding_length + 1 <=? packet_length
  then
    let! payload := take (packet_length - padding_length - 1) in
    let! padding := take padding_length in
    ret! payload
  else
    fail.

Definition test := [0;0;0;5;1;0;1;2;15].

Compute (decode decode_payload_SSH test).

Reset Decodeur.

From Formalisation Require Export Span.

Definition Decodeur (X : Type) := data -> span -> option (X * span).

Equations length (l: data) : N :=
  length nil := 0;
  length (_ :: t) := N.succ (length t).

Definition decode {X} (d : Decodeur X) (l : data) : option X :=
  match d l (mk_span 0 (length l)) with
  | None => None
  | Some (v, _) => Some v
  end.

Definition pure {X} (v : X) : Decodeur X := fun data l => Some (v,l).

Definition bind {X Y} (d : Decodeur X) (k : X -> Decodeur Y) : Decodeur Y :=
 fun data l =>
  match d data l with
  | None => None
  | Some (v, s) => k v data s
  end.

Notation "'let!' v ':=' f 'in' g" := (bind f (fun v => g))(at level 50).
Notation "'ret!' v" := (pure v)(at level 50).

Definition app {X Y} (a : Decodeur (X -> Y)) (d : Decodeur X) : Decodeur Y :=
  let! f := a in
  let! x := d in
  ret! (f x).

Notation " f '<*>' g" := (app f g)(at level 50).

Definition take (n : N) : Decodeur span :=
  fun _ s =>
   if n <=? len s
   then
    let res := mk_span (pos s) n in
    let sres := mk_span (pos s + n) (len s - n) in
    Some (res, sres)
   else
    None.

Equations lookup (n : N) (l : data) : option N by wf (N.to_nat n) Nat.lt :=
  lookup n [] := None;
  lookup 0 (h :: t) := Some h;
  lookup pos (h :: t) := lookup (N.pred pos) t.
Next Obligation.
  lia.
Defined.

Definition read (s : span) (n : N) : Decodeur N :=
  fun d t =>
    if n <? len s
    then
      match lookup (pos s + n) d with
      | None => None
      | Some v => Some (v,t)
      end
    else
      None.

Definition decode_first : Decodeur N :=
  let! s := take 1 in
  read s 0.

Definition fail {X} : Decodeur X := fun _ _ => None.

Definition to_u32 (a0 a1 a2 a3 : octet) : N :=
 a0 * (N.pow 2 32) + a1 * (N.pow 2 16) + a2  * (N.pow 2 8) + a3.

Definition decode_packet_length : Decodeur N :=
  pure to_u32 <*> decode_first <*> decode_first <*> decode_first <*> decode_first.

Definition decode_payload_SSH : Decodeur span :=
  let! packet_length := decode_packet_length in
  let! padding_length := decode_first in
  let! payload := take (packet_length - padding_length - 1) in
  let! padding := take padding_length in
  ret! payload.

Definition test := [0;0;0;5;1;0;1;2;15].

Compute (decode decode_payload_SSH test).

Definition Bit := bool.
