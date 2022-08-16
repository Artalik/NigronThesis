From Formalisation Require Import SizeNat Nom.

Definition NotifyType := nat16.

Definition is_error (n : NotifyType): bool := val n <? 16384.

Definition is_status (n : NotifyType) : bool := 16384 <? val n.
