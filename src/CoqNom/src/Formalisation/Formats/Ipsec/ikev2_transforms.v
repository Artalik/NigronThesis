From Formalisation Require Import Nom SizeNat.

Open Scope N_scope.

Definition IkeTransformType := nat8.

Definition IkeTransformEncType := nat16.

Definition is_aead (n : IkeTransformEncType) : bool :=
  match val n with
  | 14 | 15 | 16 | 18 | 19 | 20 | 25 | 26 | 27 | 28 => true
  | _ => false
  end.

Definition is_unassigned_enc (n : IkeTransformEncType): bool :=
  let v := val n in
  (23 <=? v) && (v <=? 1023).

Definition is_private_use_enc (n : IkeTransformEncType): bool :=
  1024 <=? val n.

Definition IkeTransformPRFType := nat16.

Definition is_unassigned_prf (n : IkeTransformPRFType) : bool :=
  let v := val n in
  (23 <=? v) && (v <=? 1023).

Definition is_private_use_prf (n : IkeTransformPRFType) : bool :=
  val n <=? 1024.


Definition IkeTransformAuthType := nat16.

Definition is_unassigned_auth (n : IkeTransformAuthType) : bool :=
  let v := val n in
  (15 <=? v) && (v <=? 1023).

Definition is_private_use_auth (n : IkeTransformAuthType) : bool :=
  let v := val n in
  v <=? 1024.

Definition IkeTransformDHType := nat16.

Definition is_unassigned_dh (n : IkeTransformDHType) : bool :=
  let v := val n in
  (15 <=? v) && (v <=? 1023).

Definition is_private_use_dh (n : IkeTransformDHType) : bool :=
  val n <=? 1024.

Definition IkeTransformESNType := nat16.

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

Global Instance Foldable_IkeV2Transform : Foldable (@IkeV2RawTransformS).
econstructor.
intros.
destruct (attributes _ X0). eapply (X a). eapply Monoid.mempty.
Defined.
