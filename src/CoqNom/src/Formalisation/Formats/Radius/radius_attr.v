From stdpp Require Import numbers.
From Classes Require Import Foldable.
From Formalisation Require Import Span SizeNat IpAddr.
From Formalisation Require Import Nom combinator bin_combinators.


(* https://github.com/rusticata/radius-parser/blob/master/src/radius_attr.rs *)

(* Attributes *)
Record RadiusAttributeType := mk_attrType { type : nat8 }.

Record ServiceType := mk_service { service : nat32 }.

Record FramedRouting := mk_routing { routing : nat32 }.

Record FramedProtocol := mk_protocol { protocol : nat32 }.

Record FramedCompression := mk_compression { compression : nat32 }.

Variant RadiusAttributeS {S : Type} : Type :=
| UserName (_ : S)
| UserPassword (_ : S)
| ChapPassword (_ : nat8) (_ : S)
| NasIPAddress (_ : Ipv4)
| NasPort (_ : nat32)
| Service (s : ServiceType)
| Protocol (_ : FramedProtocol)
| FramedIPAddress (_ : Ipv4)
| FramedIPNetmask (_ : Ipv4)
| Routing (_ : FramedRouting)
| FilterId (_ : S)
| FramedMTU (_ : nat32)
| Compression (_ : FramedCompression)
| VendorSpecific (_ : nat32) (_ : S)
| CalledStationId (_ : S)
| CallingStationId (_ : S)
| Unknown (_ : nat8) (_ : S).

Global Instance RadiusAttribute_Foldable : Foldable (@RadiusAttributeS).
constructor. intros. inversion X0; try apply (X s); destruct H; apply mempty.
Defined.

Definition RadiusAttribute := @RadiusAttributeS span.

Definition size4u : N := 4.

Open Scope N_scope.

Definition parse_attribute_content (t : nat8) : NomG RadiusAttribute :=
  match val t with
  | 1 => let! i := rest in ret (UserName i)
  | 2 => let! i := rest in ret (UserPassword i)
  | 3 =>
    let! len := length in
    if len <? 2
    then
      fail
    else
      let! v := be_u8 in
      let! i := rest in
      ret (ChapPassword v i)
  | 4 => map_parser (take size4u) (let! ip := get_ipv4 in ret (NasIPAddress ip))
  | 5 => map be_u32 NasPort
  | 6 => map be_u32 (fun v => Service (mk_service v))
  | 7 => map be_u32 (fun v => Protocol (mk_protocol v))
  | 8 => map_parser (take size4u) (let! ip := get_ipv4 in ret (FramedIPAddress ip))
  | 9 => map_parser (take size4u) (let! ip := get_ipv4 in ret (FramedIPNetmask ip))
  | 10 => map be_u32 (fun v => Routing (mk_routing v))
  | 11 => let! i := rest in ret (FilterId i)
  | 12 => map be_u32 FramedMTU
  | 13 => map be_u32 (fun v => Compression (mk_compression v))
  | 26 =>
    let! len := length in
    if len <? 5
    then
      fail
    else
      let! vendorid := be_u32 in
      let! vendordata := rest in
      ret (VendorSpecific vendorid vendordata)
  | 30 =>
    let! i := rest in
    ret (CalledStationId i)
  | 31 =>
    let! i := rest in
    ret (CallingStationId i)
  | _ =>
    let! i := rest in
    ret (Unknown t i)
  end.

Definition parse_radius_attribute : NomG RadiusAttribute :=
  let! t := be_u8 in
  let! l := verify be_u8 (fun n => 2 <=? val n) in
  map_parser (take (val l - 2)) (parse_attribute_content t).

Close Scope N_scope.
