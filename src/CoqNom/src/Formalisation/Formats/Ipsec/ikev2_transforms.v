From Formalisation Require Import Nom SizeNat.

Open Scope N_scope.

Record IkeTransformType := mk_transform {iketransformtype : nat8}.

Record IkeTransformEncType :=
  mk_transformEnc {
      iketransformenctype : nat16;
      is_aead : bool :=
      match val iketransformenctype with
      | 14 | 15 | 16 | 18 | 19 | 20 | 25 | 26 | 27 | 28 => true
      | _ => false
      end;
      is_unassigned_enc : bool :=
        let v := val iketransformenctype in
        (23 <=? v) && (v <=? 1023);
      is_private_use_enc : bool :=
        1024 <=? val iketransformenctype
    }.

Record IkeTransformPRFType :=
  mk_transformprf {
      iketransformprftype : nat16;
      is_unassigned_prf :=
        let v := val iketransformprftype in
        (23 <=? v) && (v <=? 1023);
      is_private_use_prf :=
        val iketransformprftype <=? 1024
    }.


Record IkeTransformAuthType :=
  mk_transformauth {
      iketransformauthtype : nat16;
      is_unassigned_auth :=
        let v := val iketransformauthtype in
        (15 <=? v) && (v <=? 1023);
      is_private_use_auth :=
        let v := val iketransformauthtype in
        v <=? 1024
    }.

Record IkeTransformDHType :=
  mk_transformdh {
      iketransformdhtype : nat16;
      is_unassigned_dh :=
        let v := val iketransformdhtype in
        (15 <=? v) && (v <=? 1023);
      is_private_use_dh :=
        val iketransformdhtype <=? 1024
    }.

Record IkeTransformESNType :=
  mk_transformesn { iketransformesntype : nat16 }.

Record IkeV2RawTransformS (S : Type) :=
  mk_raw {
      last : nat8;
      reserved1 : nat8;
      transform_length : nat16;
      transform_type : IkeTransformType;
      reserved2 : nat8;
      transform_id : nat16;
      attributes : option S
    }.

Definition IkeV2RawTransform := @IkeV2RawTransformS span.

Local Definition foldr_transform A B (f : A -> B -> B) (b : B) ta : B :=
  match attributes _ ta with
  | Some v => f v b
  | None => b
  end.

Global Instance Foldable_IkeV2GenericPayload : Foldable (@IkeV2RawTransformS) :=
  Build_Foldable _ foldr_transform.
