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

#[tactic="NSize"] Equations test_attribute_invalid : list nat8 :=
  test_attribute_invalid :=
    [ (_8 255); (_8 0); (_8 2); (_8 2) ].

Definition result_test_attribute_invalid :=
  Eval vm_compute in parse parse_radius_attribute 100 test_attribute_invalid.

Lemma result_test_attribute_invalid_ok :
  result_test_attribute_invalid = None.
  reflexivity.
Qed.

#[tactic="NSize"] Equations test_attribute_empty : list nat8 :=
  test_attribute_empty :=
    [ (_8 255); (_8 2); (_8 2); (_8 2) ].

Definition result_test_attribute_empty :=
  Eval vm_compute in parse parse_radius_attribute 100 test_attribute_empty.

Lemma result_test_attribute_empty_ok :
  match result_test_attribute_empty with
  | Some (Unknown i s) => val i = 255%N /\ s = mk_span 2 0
  | _ => False
  end.
  cbv. repeat split.
Qed.

#[tactic="NSize"] Equations test_attribute : list nat8 :=
  test_attribute :=
    [ (_8 255); (_8 4); (_8 2); (_8 2) ].

Definition result_test_attribute :=
  Eval vm_compute in parse parse_radius_attribute 100 test_attribute.

Lemma result_test_attribute_ok :
  match result_test_attribute with
  | Some (Unknown i s) => val i = 255%N /\ s = mk_span 2 2
  | _ => False
  end.
  cbv. repeat split.
Qed.

#[tactic="NSize"] Equations test_parse_vendor_specific : list nat8 :=
  test_parse_vendor_specific :=
    [ (_8 26); (_8 7); (_8 0); (_8 1); (_8 2); (_8 3); (_8 120) ].

Definition result_test_parse_vendor_specific :=
  Eval vm_compute in parse parse_radius_attribute 100 test_parse_vendor_specific.

Lemma result_test_parse_vendor_specific_ok :
  match result_test_parse_vendor_specific with
  | Some (VendorSpecific i s) => val i = 66051%N /\ s = mk_span 6 1
  | _ => False
  end.
  cbv. repeat split.
Qed.

#[tactic="NSize"] Equations test_parse_called_station_id : list nat8 :=
  test_parse_called_station_id :=
    [ (_8 30); (_8 19); (_8 97); (_8 97); (_8 45); (_8 98); (_8 98);
      (_8 45); (_8 99); (_8 99); (_8 45); (_8 100); (_8 100); (_8 45);
      (_8 101); (_8 101); (_8 45); (_8 102); (_8 102) ].

Definition result_test_parse_called_station_id :=
  Eval vm_compute in parse parse_radius_attribute 100 test_parse_called_station_id.

Lemma result_test_parse_called_station_id_ok :
  match result_test_parse_called_station_id with
  | Some (CalledStationId s) => s = mk_span 2 (lengthN test_parse_called_station_id - 2)
  | _ => False
  end.
  cbv. repeat split.
Qed.


#[tactic="NSize"] Equations test_parse_calling_station_id : list nat8 :=
  test_parse_calling_station_id :=
    [ (_8 31); (_8 19); (_8 97); (_8 97); (_8 45); (_8 98); (_8 98);
      (_8 45); (_8 99); (_8 99); (_8 45); (_8 100); (_8 100); (_8 45);
      (_8 101); (_8 101); (_8 45); (_8 102); (_8 102) ].

Definition result_test_parse_calling_station_id :=
  Eval vm_compute in parse parse_radius_attribute 100 test_parse_calling_station_id.

Lemma result_test_parse_calling_station_id_ok :
  match result_test_parse_calling_station_id with
  | Some (CallingStationId s) => s = mk_span 2 (lengthN test_parse_called_station_id - 2)
  | _ => False
  end.
  cbv. repeat split.
Qed.
