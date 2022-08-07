From Formalisation Require Import Nom combinator String.

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
