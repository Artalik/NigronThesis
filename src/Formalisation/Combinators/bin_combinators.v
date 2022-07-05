From Equations Require Import Equations.
From Formalisation Require Import Nom combinator String.

Definition NomB := @NomG nat8.

Definition be_u8 : NomB nat8 :=
  let! s := take 1 in
  read s 0.


Definition be_u16 : NomB nat16 :=
  let! v0 := be_u8 in
  let! v1 := be_u8 in
  ret (natp_to_nat2p v0 v1).

Definition be_u32 : NomB nat32 :=
  let! v0 := be_u16 in
  let! v1 := be_u16 in
  ret (natp_to_nat2p v0 v1).

Definition be_u64 : NomB nat64 :=
  let! v0 := be_u32 in
  let! v1 := be_u32 in
  ret (natp_to_nat2p v0 v1).

Definition get_ipv4 : NomB Ipv4 :=
  let! a := be_u8 in
  let! b := be_u8 in
  let! c := be_u8 in
  let! d := be_u8 in
  ret (mk_ipv4 a b c d).

Definition get_ipv6 : NomB Ipv6 :=
  let! a := be_u16 in
  let! b := be_u16 in
  let! c := be_u16 in
  let! d := be_u16 in
  let! e := be_u16 in
  let! f := be_u16 in
  let! g := be_u16 in
  let! h := be_u16 in
  ret (mk_ipv6 a b c d e f g h).

(** Basic elements **)
Definition char (n : nat8) : NomB nat8 :=
  let! u := be_u8 in
  if SizeNat.eqb u n then ret n else fail.

Definition ascii_to_nat8 (a : ascii) : nat8 :=
  mk_natN 8 (N_of_ascii a) (N_ascii_bounded a).


Definition value_in_string (v : nat8) (str : string) : NomB bool :=
  repeat_compt (Some (string_length str))
         (fun n b =>
            match string_get n str with
            | None => fail
            | Some a =>
                ret (b || SizeNat.eqb v a)
            end)
         false.


Definition value_not_in_string (v : nat8) (str : string) : NomB bool :=
  repeat_compt (Some (string_length str))
         (fun n b =>
            match string_get n str with
            | None => fail
            | Some a =>
                ret (b && negb (SizeNat.eqb v a))
            end)
         true.

Definition value_in_span (v : nat8) (s : span) : NomB bool:=
  repeat_compt (Some (len s)) (fun n b =>
                           let! r := read s n in
                           ret (b || SizeNat.eqb v r)) false.

Definition value_not_in_span (v : nat8) (s : span) : NomB bool:=
  repeat_compt (Some (len s)) (fun n b =>
                           let! r := read s n in
                           ret (b && negb (SizeNat.eqb v r))) true.

Declare Scope combinator_scope.

Local Notation "v ∈ s" := (value_in_span v s) : combinator_scope.

Local Notation "v ∉ s" := (value_not_in_span v s) : combinator_scope.

Open Scope combinator_scope.

Definition is_a_span (s : span) : NomB span :=
  recognize (repeat None (fun _ =>
                            let! v := be_u8 in
                            let! b := v ∈ s in
                            if b then ret tt else fail) tt).

Definition is_a (s : string) : NomB span :=
  recognize (repeat None (fun _ =>
                            let! v := be_u8 in
                            let! b := value_in_string v s in
                            if b then ret tt else fail) tt).

Definition is_not_span (s : span) : NomB span :=
  recognize (repeat None (fun _ =>
                            let! v := be_u8 in
                            let! b := v ∉ s in
                            if b then ret tt else fail) tt).

Definition is_not (s : string) : NomB span :=
  recognize (repeat None (fun _ =>
                            let! v := be_u8 in
                            let! b := value_not_in_string v s in
                            if b then ret tt else fail) tt).

(* Si ça échoue, le pointeur n'avance pas en nom, j'ai essayé d'être fidèle. *)
Definition one_of_span (s: span) : NomB nat8 :=
  let! v := peek be_u8 in
  let! b := v ∈ s in
  if b then be_u8 else fail.

Definition one_of (s: string) : NomB nat8 :=
  let! v := peek be_u8 in
  let! b := value_in_string v s in
  if b then be_u8 else fail.

Definition none_of_span (s: span) : NomB nat8 :=
  let! v := peek be_u8 in
  let! b := v ∉ s in
  if b then be_u8 else fail.

Definition none_of (s: string) : NomB nat8 :=
  let! v := peek be_u8 in
  let! b := value_not_in_string v s in
  if b then be_u8 else fail.

Definition tag_span (s1 : span) : NomB span :=
  let! s2 := take (len s1) in
  let! b := repeat_compt (Some (len s1)) (fun n b =>
                                      let! r1 := read s1 n in
                                      let! r2 := read s2 n in
                                      ret (b && (SizeNat.eqb r1 r2))) true in
  if b then ret s2 else fail.

Definition tag (str : string) : NomB span :=
  let len := string_length str in
  let! s := take len in
  let! b := repeat_compt (Some len) (fun n b =>
                                 let! r := read s n in
                                 match string_get n str with
                                 | None => fail
                                 | Some a =>
                                     ret (b && SizeNat.eqb r a)
                                 end) true in
  if b then ret s else fail.

Definition tag_while (cond : nat8 -> bool) : NomB span :=
  recognize (repeat None (fun s =>
                            let! v := be_u8 in
                            if cond v then ret tt else fail) tt).

Definition tag_till (cond : nat8 -> bool) : NomB span :=
  recognize (repeat None (fun s =>
                            let! v := be_u8 in
                            if cond v then fail else ret tt) tt).

Definition tag_until_span (s : span) : NomB span :=
  recognize (repeat None (fun _ =>
                            let! b := alt (let! _ := tag_span s in
                                           ret true)
                                        (let! _ := take 1 in
                                         ret false) in
                            if b then fail else ret tt) tt).

Definition tag_until (s : string) : NomB span :=
  recognize (repeat None (fun _ =>
                            let! b := alt (let! _ := tag s in
                                           ret true)
                                          (let! _ := take 1 in
                                           ret false) in
                            if b then fail else ret tt) tt).

Close Scope combinator_scope.
