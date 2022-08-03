From FreeMonad Require Import SizeNat radius_attr_HOAS radius Nom HOAS IpAddr.
From Classes Require Import Foldable.
Require Import BinNums.
Import BinNat.

(* https://github.com/rusticata/radius-parser/blob/master/src/radius_attr.rs *)

Definition sizeu16 : HOAS N := ret (VNat 16).

Definition parse_radius_data : HOAS RadiusData :=
  let! v_code := be_u8 in
  let! identifier := be_u8 in
  let! length := be_u16 in
  let! len_authenticator := sizeu16 in
  let! authenticator := take len_authenticator in
  let! attributes :=
     cond ((VNat 20) << ↓ length)
          (map_parser
             (take (↓ length -! VNat 20))
             (many1 parse_radius_attribute)) in
  ret (mk_radiusdata (mk_code v_code) identifier length authenticator attributes).
