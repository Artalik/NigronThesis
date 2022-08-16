open BinPos
open PHOAS
open Compiler (* <- Ajouté manuellement *)

(** val equiv_parse_radius_data_rel : 'a1 coq_PHOAS **)

let equiv_parse_radius_data_rel =
  LetIn ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v1 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v1)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v1 -> Read ((Var (Span, v1)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (fun v1 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v1)))))), (Unknown
    "radius_data"), (fun v1 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v3 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const (Nat,
    (ENat 1))), (Var (Nat, v3)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v3 -> Read ((Var (Span, v3)), (Const (Nat, (ENat 0))))))), (Unknown
    "radius_data"), (fun v3 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v5 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v5)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v5 -> Read ((Var (Span, v5)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v5 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v7 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const (Nat,
    (ENat 1))), (Var (Nat, v7)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v7 -> Read ((Var (Span, v7)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v7 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v5)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v7)))))))))), (Unknown
    "radius_data"), (fun v5 -> LetIn (Span, (LetIn (Nat, Length, Span, (fun v7 ->
    IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const (Nat, (ENat ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))), (Var (Nat, v7)))), Span, (Take
    (Const (Nat, (ENat ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    1)))))))), (Fail Span))))), (Unknown "radius_data"), (fun v7 -> LetIn ((Option
    (Vector (Unknown "radius_attribute"))), (IfThenElse ((EBin (Nat, Nat, Bool, ELt,
    (Const (Nat, (ENat ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
    1))))))), (EUna ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), Nat,
    (EVal (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v5)))))), (Option (Vector (Unknown "radius_attribute"))), (LetIn ((Vector (Unknown
    "radius_attribute")), (LetIn (Span, (LetIn (Nat, Length, Span, (fun v9 ->
    IfThenElse ((EBin (Nat, Nat, Bool, ELe, (EBin (Nat, Nat, Nat, ESub, (EUna ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), Nat,
    (EVal (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), v5)))),
    (Const (Nat, (ENat ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
    1))))))))), (Var (Nat, v9)))), Span, (Take (EBin (Nat, Nat, Nat, ESub, (EUna ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), Nat,
    (EVal (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), v5)))),
    (Const (Nat, (ENat ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
    1)))))))))), (Fail Span))))), (Vector (Unknown "radius_attribute")), (fun v9 ->
    Local ((EUna (Span, (Option Span), (ESome Span), (Var (Span, v9)))), (Vector
    (Unknown "radius_attribute")), (LetIn (Nat, Length, (Vector (Unknown
    "radius_attribute")), (fun v11 -> LetIn ((Unknown "radius_attribute"), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v13 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v13)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v13 -> Read ((Var (Span, v13)), (Const (Nat, (ENat 0))))))), (Unknown
    "radius_attribute"), (fun v13 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v15 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v15)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v15 -> Read ((Var (Span, v15)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (fun v15 -> IfThenElse
    ((EBin (Nat, Nat, Bool, ELe, (Const (Nat, (ENat ((fun p->2*p) 1)))), (EUna ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), Nat, (EVal
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v15)))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v15)))), (Fail (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1))))))), (Unknown
    "radius_attribute"), (fun v15 -> LetIn (Span, (LetIn (Nat, Length, Span,
    (fun v17 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (EBin (Nat, Nat, Nat, ESub,
    (EUna ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), Nat,
    (EVal (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v15)))), (Const (Nat,
    (ENat ((fun p->2*p) 1)))))), (Var (Nat, v17)))), Span, (Take (EBin (Nat, Nat, Nat,
    ESub, (EUna ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    Nat, (EVal (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v15)))), (Const (Nat,
    (ENat ((fun p->2*p) 1))))))), (Fail Span))))), (Unknown "radius_attribute"),
    (fun v17 -> Local ((EUna (Span, (Option Span), (ESome Span), (Var (Span, v17)))),
    (Unknown "radius_attribute"), (Switch ((EUna ((NatN ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) 1)))), Nat, (EVal ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))),
    (Var ((NatN ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))), v13)))), (Unknown
    "radius_attribute"), (LScons (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) 1)))), (Unknown "radius_attribute"), (LetIn (Span, (LetIn (Nat,
    Length, Span, (fun v19 -> Take (Var (Nat, v19))))), (Unknown "radius_attribute"),
    (fun v19 -> ExternStruct ("radius_attribute", "create_CallingStationId", (CONS
    (Span, (Var (Span, v19)), NIL)))))), (LScons (((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) 1))), (Unknown "radius_attribute"), (LetIn (Span, (LetIn (Nat,
    Length, Span, (fun v19 -> Take (Var (Nat, v19))))), (Unknown "radius_attribute"),
    (fun v19 -> ExternStruct ("radius_attribute", "create_FilterId", (CONS (Span, (Var
    (Span, v19)), NIL)))))), (LScons (((fun p->1+2*p) ((fun p->1+2*p) 1)), (Unknown
    "radius_attribute"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v19 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v19)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v19 -> Read ((Var (Span, v19)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v19 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v21 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v19)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v19 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v21 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v23 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v23)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v23 -> Read ((Var (Span, v23)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v23 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v21 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EBin ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v19)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v21)))))))))), (Unknown "radius_attribute"), (fun v19 -> ExternStruct
    ("radius_attribute", "create_Protocol", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), v19)), NIL)))))), (LScons (((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
    1))), (Unknown "radius_attribute"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v19 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v19)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v19 -> Read ((Var (Span, v19)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v19 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v21 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v19)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v19 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v21 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v23 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v23)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v23 -> Read ((Var (Span, v23)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v23 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v21 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EBin ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v19)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v21)))))))))), (Unknown "radius_attribute"), (fun v19 -> ExternStruct
    ("radius_attribute", "create_Compression", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), v19)), NIL)))))), (LScons (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    1))), (Unknown "radius_attribute"), (LetIn (Span, (LetIn (Nat, Length, Span,
    (fun v19 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const (Nat, (ENat
    ((fun p->2*p) ((fun p->2*p) 1))))), (Var (Nat, v19)))), Span, (Take (Const (Nat,
    (ENat ((fun p->2*p) ((fun p->2*p) 1)))))), (Fail Span))))), (Unknown
    "radius_attribute"), (fun v19 -> Local ((EUna (Span, (Option Span), (ESome Span),
    (Var (Span, v19)))), (Unknown "radius_attribute"), (LetIn ((Unknown "ipv4"), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v21 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v23 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v23)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v23 -> Read ((Var (Span, v23)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v23 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v25 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v25)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v25 -> Read ((Var (Span, v25)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v25 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v27 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v27)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v27 -> Read ((Var (Span, v27)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v27 -> ExternStruct ("ipv4", "create_ipv4", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v25)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v27)),
    NIL)))))))))))))))))), (Unknown "radius_attribute"), (fun v21 -> ExternStruct
    ("radius_attribute", "create_FramedIPNetmask", (CONS ((Unknown "ipv4"), (Var
    ((Unknown "ipv4"), v21)), NIL)))))))))), (LScons (((fun p->1+2*p) ((fun p->2*p)
    1)), (Unknown "radius_attribute"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v19 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v19)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v19 -> Read ((Var (Span, v19)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v19 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v21 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v19)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v19 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v21 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v23 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v23)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v23 -> Read ((Var (Span, v23)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v23 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v21 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EBin ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v19)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v21)))))))))), (Unknown "radius_attribute"), (fun v19 -> ExternStruct
    ("radius_attribute", "create_NasPort", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), v19)), NIL)))))), (LScons (((fun p->1+2*p) 1), (Unknown
    "radius_attribute"), (LetIn (Nat, Length, (Unknown "radius_attribute"), (fun v19 ->
    IfThenElse ((EBin (Nat, Nat, Bool, ELt, (Var (Nat, v19)), (Const (Nat, (ENat
    ((fun p->2*p) 1)))))), (Unknown "radius_attribute"), (Fail (Unknown
    "radius_attribute")), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (Unknown
    "radius_attribute"), (fun v21 -> LetIn (Span, (LetIn (Nat, Length, Span,
    (fun v23 -> Take (Var (Nat, v23))))), (Unknown "radius_attribute"), (fun v23 ->
    ExternStruct ("radius_attribute", "create_ChapPassword", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)), (CONS (Span,
    (Var (Span, v23)), NIL)))))))))))))), (LScons (((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))), (Unknown "radius_attribute"), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v19 -> Take (Var (Nat, v19))))), (Unknown
    "radius_attribute"), (fun v19 -> ExternStruct ("radius_attribute",
    "create_CalledStationId", (CONS (Span, (Var (Span, v19)), NIL)))))), (LScons
    (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))), (Unknown
    "radius_attribute"), (LetIn (Nat, Length, (Unknown "radius_attribute"), (fun v19 ->
    IfThenElse ((EBin (Nat, Nat, Bool, ELt, (Var (Nat, v19)), (Const (Nat, (ENat
    ((fun p->1+2*p) ((fun p->2*p) 1))))))), (Unknown "radius_attribute"), (Fail
    (Unknown "radius_attribute")), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v21 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v23 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v23)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v23 -> Read ((Var (Span, v23)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v23 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v21 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v23 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v23)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v23 -> Read ((Var (Span, v23)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v23 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v25 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v25)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v25 -> Read ((Var (Span, v25)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v25 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v25)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v23 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EBin ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v21)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v23)))))))))), (Unknown "radius_attribute"), (fun v21 -> LetIn (Span, (LetIn (Nat,
    Length, Span, (fun v23 -> Take (Var (Nat, v23))))), (Unknown "radius_attribute"),
    (fun v23 -> ExternStruct ("radius_attribute", "create_VendorSpecific", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), v21)), (CONS (Span, (Var (Span, v23)), NIL)))))))))))))), (LScons
    (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))), (Unknown "radius_attribute"),
    (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v19 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v19)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v19 -> Read ((Var (Span, v19)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v19 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v21 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v19)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v19 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v21 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v23 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v23)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v23 -> Read ((Var (Span, v23)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v23 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v21 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EBin ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v19)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v21)))))))))), (Unknown "radius_attribute"), (fun v19 -> ExternStruct
    ("radius_attribute", "create_Routing", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), v19)), NIL)))))), (LScons (((fun p->2*p) ((fun p->1+2*p) 1)), (Unknown
    "radius_attribute"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v19 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v19)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v19 -> Read ((Var (Span, v19)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v19 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v21 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v19)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v19 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v21 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v23 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v23)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v23 -> Read ((Var (Span, v23)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v23 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v21 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EBin ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v19)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v21)))))))))), (Unknown "radius_attribute"), (fun v19 -> ExternStruct
    ("radius_attribute", "create_Service", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), v19)), NIL)))))), (LScons (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    1))), (Unknown "radius_attribute"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v19 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v19)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v19 -> Read ((Var (Span, v19)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v19 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v21 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v19)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v19 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v21 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v23 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v23)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v23 -> Read ((Var (Span, v23)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v23 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v21 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EBin ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v19)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v21)))))))))), (Unknown "radius_attribute"), (fun v19 -> ExternStruct
    ("radius_attribute", "create_FramedMTU", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), v19)), NIL)))))), (LScons (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))),
    (Unknown "radius_attribute"), (LetIn (Span, (LetIn (Nat, Length, Span, (fun v19 ->
    IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const (Nat, (ENat ((fun p->2*p)
    ((fun p->2*p) 1))))), (Var (Nat, v19)))), Span, (Take (Const (Nat, (ENat
    ((fun p->2*p) ((fun p->2*p) 1)))))), (Fail Span))))), (Unknown "radius_attribute"),
    (fun v19 -> Local ((EUna (Span, (Option Span), (ESome Span), (Var (Span, v19)))),
    (Unknown "radius_attribute"), (LetIn ((Unknown "ipv4"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v21 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v23 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v23)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v23 -> Read ((Var (Span, v23)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v23 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v25 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v25)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v25 -> Read ((Var (Span, v25)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v25 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v27 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v27)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v27 -> Read ((Var (Span, v27)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v27 -> ExternStruct ("ipv4", "create_ipv4", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v25)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v27)),
    NIL)))))))))))))))))), (Unknown "radius_attribute"), (fun v21 -> ExternStruct
    ("radius_attribute", "create_FramedIPAddress", (CONS ((Unknown "ipv4"), (Var
    ((Unknown "ipv4"), v21)), NIL)))))))))), (LScons (((fun p->2*p) ((fun p->2*p) 1)),
    (Unknown "radius_attribute"), (LetIn (Span, (LetIn (Nat, Length, Span, (fun v19 ->
    IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const (Nat, (ENat ((fun p->2*p)
    ((fun p->2*p) 1))))), (Var (Nat, v19)))), Span, (Take (Const (Nat, (ENat
    ((fun p->2*p) ((fun p->2*p) 1)))))), (Fail Span))))), (Unknown "radius_attribute"),
    (fun v19 -> Local ((EUna (Span, (Option Span), (ESome Span), (Var (Span, v19)))),
    (Unknown "radius_attribute"), (LetIn ((Unknown "ipv4"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v21 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v23 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v23)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v23 -> Read ((Var (Span, v23)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v23 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v25 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v25)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v25 -> Read ((Var (Span, v25)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v25 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v27 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v27)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v27 -> Read ((Var (Span, v27)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v27 -> ExternStruct ("ipv4", "create_ipv4", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v21)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v25)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v27)),
    NIL)))))))))))))))))), (Unknown "radius_attribute"), (fun v21 -> ExternStruct
    ("radius_attribute", "create_NasIPAddress", (CONS ((Unknown "ipv4"), (Var ((Unknown
    "ipv4"), v21)), NIL)))))))))), (LScons (((fun p->2*p) 1), (Unknown
    "radius_attribute"), (LetIn (Span, (LetIn (Nat, Length, Span, (fun v19 -> Take (Var
    (Nat, v19))))), (Unknown "radius_attribute"), (fun v19 -> ExternStruct
    ("radius_attribute", "create_UserPassword", (CONS (Span, (Var (Span, v19)),
    NIL)))))), (LScons (1, (Unknown "radius_attribute"), (LetIn (Span, (LetIn (Nat,
    Length, Span, (fun v19 -> Take (Var (Nat, v19))))), (Unknown "radius_attribute"),
    (fun v19 -> ExternStruct ("radius_attribute", "create_UserName", (CONS (Span, (Var
    (Span, v19)), NIL)))))), (LSnil ((Unknown "radius_attribute"), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v19 -> Take (Var (Nat, v19))))), (Unknown
    "radius_attribute"), (fun v19 -> ExternStruct ("radius_attribute",
    "create_Unknown", (CONS ((NatN ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))),
    (Var ((NatN ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))), v13)), (CONS (Span,
    (Var (Span, v19)), NIL)))))))))))))))))))))))))))))))))))))))))))))))))))), (Vector
    (Unknown "radius_attribute")), (fun v13 -> LetIn (Nat, Length, (Vector (Unknown
    "radius_attribute")), (fun v15 -> IfThenElse ((EBin (Nat, Nat, Bool, EEq, (Var
    (Nat, v11)), (Var (Nat, v15)))), (Vector (Unknown "radius_attribute")), (Fail
    (Vector (Unknown "radius_attribute"))), (Repeat ((Const ((Option Nat), (ENone
    Nat))), (Vector (Unknown "radius_attribute")), (fun v17 -> LetIn (Nat, Length,
    (Vector (Unknown "radius_attribute")), (fun v19 -> LetIn ((Unknown
    "radius_attribute"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v21 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v21)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v21 -> Read ((Var (Span, v21)), (Const (Nat, (ENat 0))))))), (Unknown
    "radius_attribute"), (fun v21 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v23 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v23)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v23 -> Read ((Var (Span, v23)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (fun v23 -> IfThenElse
    ((EBin (Nat, Nat, Bool, ELe, (Const (Nat, (ENat ((fun p->2*p) 1)))), (EUna ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), Nat, (EVal
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)))), (Fail (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1))))))), (Unknown
    "radius_attribute"), (fun v23 -> LetIn (Span, (LetIn (Nat, Length, Span,
    (fun v25 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (EBin (Nat, Nat, Nat, ESub,
    (EUna ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), Nat,
    (EVal (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)))), (Const (Nat,
    (ENat ((fun p->2*p) 1)))))), (Var (Nat, v25)))), Span, (Take (EBin (Nat, Nat, Nat,
    ESub, (EUna ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    Nat, (EVal (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v23)))), (Const (Nat,
    (ENat ((fun p->2*p) 1))))))), (Fail Span))))), (Unknown "radius_attribute"),
    (fun v25 -> Local ((EUna (Span, (Option Span), (ESome Span), (Var (Span, v25)))),
    (Unknown "radius_attribute"), (Switch ((EUna ((NatN ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) 1)))), Nat, (EVal ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))),
    (Var ((NatN ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))), v21)))), (Unknown
    "radius_attribute"), (LScons (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) 1)))), (Unknown "radius_attribute"), (LetIn (Span, (LetIn (Nat,
    Length, Span, (fun v27 -> Take (Var (Nat, v27))))), (Unknown "radius_attribute"),
    (fun v27 -> ExternStruct ("radius_attribute", "create_CallingStationId", (CONS
    (Span, (Var (Span, v27)), NIL)))))), (LScons (((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) 1))), (Unknown "radius_attribute"), (LetIn (Span, (LetIn (Nat,
    Length, Span, (fun v27 -> Take (Var (Nat, v27))))), (Unknown "radius_attribute"),
    (fun v27 -> ExternStruct ("radius_attribute", "create_FilterId", (CONS (Span, (Var
    (Span, v27)), NIL)))))), (LScons (((fun p->1+2*p) ((fun p->1+2*p) 1)), (Unknown
    "radius_attribute"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v27 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v27)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v27 -> Read ((Var (Span, v27)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v27 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v29 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v27)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v27 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v29 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v31 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v31)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v31 -> Read ((Var (Span, v31)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v31 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v31)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v29 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EBin ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v27)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v29)))))))))), (Unknown "radius_attribute"), (fun v27 -> ExternStruct
    ("radius_attribute", "create_Protocol", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), v27)), NIL)))))), (LScons (((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
    1))), (Unknown "radius_attribute"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v27 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v27)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v27 -> Read ((Var (Span, v27)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v27 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v29 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v27)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v27 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v29 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v31 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v31)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v31 -> Read ((Var (Span, v31)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v31 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v31)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v29 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EBin ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v27)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v29)))))))))), (Unknown "radius_attribute"), (fun v27 -> ExternStruct
    ("radius_attribute", "create_Compression", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), v27)), NIL)))))), (LScons (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    1))), (Unknown "radius_attribute"), (LetIn (Span, (LetIn (Nat, Length, Span,
    (fun v27 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const (Nat, (ENat
    ((fun p->2*p) ((fun p->2*p) 1))))), (Var (Nat, v27)))), Span, (Take (Const (Nat,
    (ENat ((fun p->2*p) ((fun p->2*p) 1)))))), (Fail Span))))), (Unknown
    "radius_attribute"), (fun v27 -> Local ((EUna (Span, (Option Span), (ESome Span),
    (Var (Span, v27)))), (Unknown "radius_attribute"), (LetIn ((Unknown "ipv4"), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v29 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v31 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v31)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v31 -> Read ((Var (Span, v31)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v31 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v33 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v33)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v33 -> Read ((Var (Span, v33)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v33 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v35 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v35)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v35 -> Read ((Var (Span, v35)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v35 -> ExternStruct ("ipv4", "create_ipv4", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v31)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v33)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v35)),
    NIL)))))))))))))))))), (Unknown "radius_attribute"), (fun v29 -> ExternStruct
    ("radius_attribute", "create_FramedIPNetmask", (CONS ((Unknown "ipv4"), (Var
    ((Unknown "ipv4"), v29)), NIL)))))))))), (LScons (((fun p->1+2*p) ((fun p->2*p)
    1)), (Unknown "radius_attribute"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v27 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v27)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v27 -> Read ((Var (Span, v27)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v27 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v29 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v27)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v27 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v29 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v31 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v31)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v31 -> Read ((Var (Span, v31)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v31 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v31)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v29 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EBin ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v27)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v29)))))))))), (Unknown "radius_attribute"), (fun v27 -> ExternStruct
    ("radius_attribute", "create_NasPort", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), v27)), NIL)))))), (LScons (((fun p->1+2*p) 1), (Unknown
    "radius_attribute"), (LetIn (Nat, Length, (Unknown "radius_attribute"), (fun v27 ->
    IfThenElse ((EBin (Nat, Nat, Bool, ELt, (Var (Nat, v27)), (Const (Nat, (ENat
    ((fun p->2*p) 1)))))), (Unknown "radius_attribute"), (Fail (Unknown
    "radius_attribute")), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (Unknown
    "radius_attribute"), (fun v29 -> LetIn (Span, (LetIn (Nat, Length, Span,
    (fun v31 -> Take (Var (Nat, v31))))), (Unknown "radius_attribute"), (fun v31 ->
    ExternStruct ("radius_attribute", "create_ChapPassword", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)), (CONS (Span,
    (Var (Span, v31)), NIL)))))))))))))), (LScons (((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))), (Unknown "radius_attribute"), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v27 -> Take (Var (Nat, v27))))), (Unknown
    "radius_attribute"), (fun v27 -> ExternStruct ("radius_attribute",
    "create_CalledStationId", (CONS (Span, (Var (Span, v27)), NIL)))))), (LScons
    (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))), (Unknown
    "radius_attribute"), (LetIn (Nat, Length, (Unknown "radius_attribute"), (fun v27 ->
    IfThenElse ((EBin (Nat, Nat, Bool, ELt, (Var (Nat, v27)), (Const (Nat, (ENat
    ((fun p->1+2*p) ((fun p->2*p) 1))))))), (Unknown "radius_attribute"), (Fail
    (Unknown "radius_attribute")), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v29 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v31 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v31)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v31 -> Read ((Var (Span, v31)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v31 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v31)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v29 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v31 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v31)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v31 -> Read ((Var (Span, v31)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v31 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v33 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v33)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v33 -> Read ((Var (Span, v33)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v33 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v31)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v33)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v31 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EBin ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v29)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v31)))))))))), (Unknown "radius_attribute"), (fun v29 -> LetIn (Span, (LetIn (Nat,
    Length, Span, (fun v31 -> Take (Var (Nat, v31))))), (Unknown "radius_attribute"),
    (fun v31 -> ExternStruct ("radius_attribute", "create_VendorSpecific", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), v29)), (CONS (Span, (Var (Span, v31)), NIL)))))))))))))), (LScons
    (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))), (Unknown "radius_attribute"),
    (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v27 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v27)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v27 -> Read ((Var (Span, v27)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v27 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v29 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v27)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v27 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v29 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v31 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v31)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v31 -> Read ((Var (Span, v31)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v31 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v31)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v29 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EBin ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v27)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v29)))))))))), (Unknown "radius_attribute"), (fun v27 -> ExternStruct
    ("radius_attribute", "create_Routing", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), v27)), NIL)))))), (LScons (((fun p->2*p) ((fun p->1+2*p) 1)), (Unknown
    "radius_attribute"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v27 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v27)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v27 -> Read ((Var (Span, v27)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v27 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v29 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v27)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v27 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v29 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v31 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v31)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v31 -> Read ((Var (Span, v31)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v31 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v31)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v29 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EBin ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v27)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v29)))))))))), (Unknown "radius_attribute"), (fun v27 -> ExternStruct
    ("radius_attribute", "create_Service", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), v27)), NIL)))))), (LScons (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    1))), (Unknown "radius_attribute"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v27 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v27)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v27 -> Read ((Var (Span, v27)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v27 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v29 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v27)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v27 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (LetIn
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span,
    (LetIn (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe,
    (Const (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))),
    (Fail Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v29 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v31 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v31)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v31 -> Read ((Var (Span, v31)), (Const (Nat, (ENat 0))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    (fun v31 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EBin
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v31)))))))))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (fun v29 -> Val ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EBin ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (EpTo2p
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v27)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v29)))))))))), (Unknown "radius_attribute"), (fun v27 -> ExternStruct
    ("radius_attribute", "create_FramedMTU", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) ((fun p->2*p)
      1)))), v27)), NIL)))))), (LScons (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))),
    (Unknown "radius_attribute"), (LetIn (Span, (LetIn (Nat, Length, Span, (fun v27 ->
    IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const (Nat, (ENat ((fun p->2*p)
    ((fun p->2*p) 1))))), (Var (Nat, v27)))), Span, (Take (Const (Nat, (ENat
    ((fun p->2*p) ((fun p->2*p) 1)))))), (Fail Span))))), (Unknown "radius_attribute"),
    (fun v27 -> Local ((EUna (Span, (Option Span), (ESome Span), (Var (Span, v27)))),
    (Unknown "radius_attribute"), (LetIn ((Unknown "ipv4"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v29 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v31 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v31)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v31 -> Read ((Var (Span, v31)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v31 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v33 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v33)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v33 -> Read ((Var (Span, v33)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v33 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v35 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v35)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v35 -> Read ((Var (Span, v35)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v35 -> ExternStruct ("ipv4", "create_ipv4", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v31)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v33)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v35)),
    NIL)))))))))))))))))), (Unknown "radius_attribute"), (fun v29 -> ExternStruct
    ("radius_attribute", "create_FramedIPAddress", (CONS ((Unknown "ipv4"), (Var
    ((Unknown "ipv4"), v29)), NIL)))))))))), (LScons (((fun p->2*p) ((fun p->2*p) 1)),
    (Unknown "radius_attribute"), (LetIn (Span, (LetIn (Nat, Length, Span, (fun v27 ->
    IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const (Nat, (ENat ((fun p->2*p)
    ((fun p->2*p) 1))))), (Var (Nat, v27)))), Span, (Take (Const (Nat, (ENat
    ((fun p->2*p) ((fun p->2*p) 1)))))), (Fail Span))))), (Unknown "radius_attribute"),
    (fun v27 -> Local ((EUna (Span, (Option Span), (ESome Span), (Var (Span, v27)))),
    (Unknown "radius_attribute"), (LetIn ((Unknown "ipv4"), (LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v29 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v29)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v29 -> Read ((Var (Span, v29)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v29 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v31 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v31)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v31 -> Read ((Var (Span, v31)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v31 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v33 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v33)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v33 -> Read ((Var (Span, v33)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v33 -> LetIn ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v35 -> IfThenElse ((EBin (Nat, Nat, Bool, ELe, (Const
    (Nat, (ENat 1))), (Var (Nat, v35)))), Span, (Take (Const (Nat, (ENat 1)))), (Fail
    Span))))), (NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)),
    (fun v35 -> Read ((Var (Span, v35)), (Const (Nat, (ENat 0))))))), (Unknown "ipv4"),
    (fun v35 -> ExternStruct ("ipv4", "create_ipv4", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v29)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v31)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v33)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v35)),
    NIL)))))))))))))))))), (Unknown "radius_attribute"), (fun v29 -> ExternStruct
    ("radius_attribute", "create_NasIPAddress", (CONS ((Unknown "ipv4"), (Var ((Unknown
    "ipv4"), v29)), NIL)))))))))), (LScons (((fun p->2*p) 1), (Unknown
    "radius_attribute"), (LetIn (Span, (LetIn (Nat, Length, Span, (fun v27 -> Take (Var
    (Nat, v27))))), (Unknown "radius_attribute"), (fun v27 -> ExternStruct
    ("radius_attribute", "create_UserPassword", (CONS (Span, (Var (Span, v27)),
    NIL)))))), (LScons (1, (Unknown "radius_attribute"), (LetIn (Span, (LetIn (Nat,
    Length, Span, (fun v27 -> Take (Var (Nat, v27))))), (Unknown "radius_attribute"),
    (fun v27 -> ExternStruct ("radius_attribute", "create_UserName", (CONS (Span, (Var
    (Span, v27)), NIL)))))), (LSnil ((Unknown "radius_attribute"), (LetIn (Span, (LetIn
    (Nat, Length, Span, (fun v27 -> Take (Var (Nat, v27))))), (Unknown
    "radius_attribute"), (fun v27 -> ExternStruct ("radius_attribute",
    "create_Unknown", (CONS ((NatN ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))),
    (Var ((NatN ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))), v21)), (CONS (Span,
    (Var (Span, v27)), NIL)))))))))))))))))))))))))))))))))))))))))))))))))))), (Vector
    (Unknown "radius_attribute")), (fun v21 -> LetIn (Nat, Length, (Vector (Unknown
    "radius_attribute")), (fun v23 -> IfThenElse ((EBin (Nat, Nat, Bool, EEq, (Var
    (Nat, v19)), (Var (Nat, v23)))), (Vector (Unknown "radius_attribute")), (Fail
    (Vector (Unknown "radius_attribute"))), (Val ((Vector (Unknown
    "radius_attribute")), (EBin ((Vector (Unknown "radius_attribute")), (Unknown
    "radius_attribute"), (Vector (Unknown "radius_attribute")), (EAddVec (Unknown
    "radius_attribute")), (Var ((Vector (Unknown "radius_attribute")), v17)), (Var
    ((Unknown "radius_attribute"), v21)))))))))))))), (EBin ((Vector (Unknown
    "radius_attribute")), (Unknown "radius_attribute"), (Vector (Unknown
    "radius_attribute")), (EAddVec (Unknown "radius_attribute")), (EUna (Nat, (Vector
    (Unknown "radius_attribute")), (EMake (Unknown "radius_attribute")), (Const (Nat,
    (ENat ((fun p->2*p) 1)))))), (Var ((Unknown "radius_attribute"),
    v13)))))))))))))))))), (Option (Vector (Unknown "radius_attribute"))), (fun v9 ->
    Val ((Option (Vector (Unknown "radius_attribute"))), (EUna ((Vector (Unknown
    "radius_attribute")), (Option (Vector (Unknown "radius_attribute"))), (ESome
    (Vector (Unknown "radius_attribute"))), (Var ((Vector (Unknown
    "radius_attribute")), v9)))))))), (Val ((Option (Vector (Unknown
    "radius_attribute"))), (Const ((Option (Vector (Unknown "radius_attribute"))),
    (ENone (Vector (Unknown "radius_attribute"))))))))), (Unknown "radius_data"),
    (fun v9 -> ExternStruct ("radius_data", "create_RadiusData", (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v1)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), (Var ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) 1)), v3)), (CONS ((NatN
    (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))), (Var
    ((NatN (Pos.mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) ((fun p->2*p) 1))),
    v5)), (CONS (Span, (Var (Span, v7)), (CONS ((Option (Vector (Unknown
    "radius_attribute"))), (Var ((Option (Vector (Unknown "radius_attribute"))), v9)),
    NIL)))))))))))))))))))))

(* Cette fonction anonyme a été ajouté manuellement et permet d'appeler le compilateur.  *)
(* On indique que la bibliothèque est dans Datatypes.h. *)
(* Le fichier doit s'appeler parser_Radius.c. *)
(* La fonction principale s'appelle parse_radius. *)
(* Il faut déplacer ce fichier dans le dossier du compilateur et l'exécuter pour obtenir le code C. *)
(* Ne pas oublier de déplacer également les dépendances ! (BinPos seulement dans ce cas) *)

let _ = compile_to "Radius.h" "parser_Radius.c" "parse_radius" equiv_parse_radius_data_rel
