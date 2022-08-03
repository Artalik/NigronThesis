From Formalisation Require Import Nom SizeNat ikev2_transforms.

Record NotifyType :=
  mk_notify {
      val_noti : nat16;
      is_error : bool := val val_noti <? 16384;
      is_status : bool := 16384 <? val val_noti
    }.
