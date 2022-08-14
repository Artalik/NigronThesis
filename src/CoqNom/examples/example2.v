From Equations Require Import Equations.
Require Import Ascii String.
Require Import FunctionalExtensionality.
From stdpp Require Import numbers.
Import N.

From Formalisation Require Export Span.
From FreeMonad Require Import FreeMonad.
From SepLogic Require Import SepSet.
From Formalisation Require Import IsFresh Inject.

Open Scope N_scope.

Definition octet := N.

Definition data := list octet.

(* =DecodeurM= *)
Definition DecodeurM (X : Type) := data -> span -> option (X * span).
(* =end= *)

Equations length (l: data) : N :=
  length nil := 0;
  length (_ :: t) := N.succ (length t).

Section decodeM.

  Context {X : Type}.

(* =decodeM= *)
Definition decodeM (d : DecodeurM X) (l : data) : option X :=
  match d l (mk_span 0 (length l)) with
  | None => None
  | Some (v, _) => Some v
  end.
(* =end= *)

End decodeM.

Section pure.

  Context {X : Type}.
(* =pure= *)
Definition pure (v : X) : DecodeurM X := fun data l => Some (v,l).
(* =end= *)

End pure.

Section bind.

  Context {X Y : Type}.

(* =bind= *)
Definition bind (d : DecodeurM X) (k : X -> DecodeurM Y) : DecodeurM Y :=
  fun data l =>
    match d data l with
    | None => None
    | Some (v, s) => k v data s
    end.
(* =end= *)

End bind.

Notation "'let!' v ':=' f 'in' g" := (bind f (fun v => g)) (v name, at level 50).
Notation "'ret!' v" := (pure v) (at level 50).

(* =app= *)
Definition app {X Y} (a : DecodeurM (X -> Y)) (d : DecodeurM X) : DecodeurM Y :=
  let! f := a in
  let! x := d in
  ret! (f x).
(* =end= *)

Notation " f '<*>' g" := (app f g)(at level 50).

(* =takeM= *)
Definition takeM (n : N) : DecodeurM span :=
  fun _ s =>
    if n <=? len s
    then
      let res := mk_span (pos s) n in
      let sres := mk_span (pos s + n) (len s - n) in
      Some (res, sres)
    else
      None.
(* =end= *)

Equations lookup (n : N) (l : data) : option N by wf (N.to_nat n) Nat.lt :=
  lookup n [] := None;
  lookup 0 (h :: t) := Some h;
  lookup pos (h :: t) := lookup (N.pred pos) t.
Next Obligation.
  lia.
Defined.

(* =readM= *)
Definition readM (s : span) (n : N) : DecodeurM N :=
  fun d t =>
    if n <? len s
    then
      match lookup (pos s + n) d with
      | None => None
      | Some v => Some (v,t)
      end
    else
      None.
(* =end= *)

(* =decode_next= *)
Definition decode_next : DecodeurM N :=
  let! s := takeM 1 in
  readM s 0.
(* =end= *)

(* =failM= *)
Definition failM {X} : DecodeurM X := fun _ _ => None.
(* =end= *)

Definition to_u32 (a0 a1 a2 a3 : octet) : N :=
  a0 * (N.pow 2 32) + a1 * (N.pow 2 16) + a2  * (N.pow 2 8) + a3.

(* =decode_packet_length= *)
Definition decode_packet_length : DecodeurM N :=
  pure to_u32 <*> decode_next <*> decode_next <*> decode_next <*> decode_next.
(* =end= *)

(* =decode_payload_SSH= *)
Definition decode_payload_SSH : DecodeurM span :=
  let! packet_length := decode_packet_length in
  let! padding_length := decode_next in
  if padding_length + 1 <=? packet_length
  then
    let! payload := takeM (packet_length - padding_length - 1) in
    let! padding := takeM padding_length in
    ret! payload
  else
    failM.
(* =end= *)
