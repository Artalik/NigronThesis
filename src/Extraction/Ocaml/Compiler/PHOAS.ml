type natN = int

type coq_type =
| Nat
| NatN of int
| Bool
| Vector of coq_type
| String
| Unit
| Span
| Unknown of string
| Option of coq_type
| Pair of coq_type * coq_type
| Sum of coq_type * coq_type

type coq_OpBin =
| EAdd
| ESub
| EMult
| EDiv
| EMod
| EEq
| ELe
| ELt
| EAnd
| EOr
| EStringGet
| EPair of coq_type * coq_type
| EpTo2p of int
| EGetVec of coq_type
| EAddVec of coq_type

type coq_OpUna =
| EVal of int
| ENot
| EStringLen
| EFst of coq_type * coq_type
| ESnd of coq_type * coq_type
| ESome of coq_type
| EInl of coq_type * coq_type
| EInr of coq_type * coq_type
| ELen
| EMake of coq_type

type coq_Literal =
| ENat of int
| ENatN of int * natN
| EBool of bool
| EString of string
| ENone of coq_type
| EUnit

type 'var coq_VAL =
| Var of coq_type * 'var
| EBin of coq_type * coq_type * coq_type * coq_OpBin * 'var coq_VAL * 'var coq_VAL
| EUna of coq_type * coq_type * coq_OpUna * 'var coq_VAL
| Const of coq_type * coq_Literal

type 'var coq_LIST =
| NIL
| CONS of coq_type * 'var coq_VAL * 'var coq_LIST

type 'var coq_PHOAS =
| ExternStruct of string * string * 'var coq_LIST
| Val of coq_type * 'var coq_VAL
| LetIn of coq_type * 'var coq_PHOAS * coq_type * ('var -> 'var coq_PHOAS)
| IfThenElse of 'var coq_VAL * coq_type * 'var coq_PHOAS * 'var coq_PHOAS
| CaseOption of coq_type * 'var coq_VAL * coq_type * 'var coq_PHOAS
   * ('var -> 'var coq_PHOAS)
| Switch of 'var coq_VAL * coq_type * 'var case_switch
| Fail of coq_type
| Take of 'var coq_VAL
| Length
| Read of 'var coq_VAL * 'var coq_VAL
| Alt of coq_type * 'var coq_PHOAS * 'var coq_PHOAS
| Local of 'var coq_VAL * coq_type * 'var coq_PHOAS
| Repeat of 'var coq_VAL * coq_type * ('var -> 'var coq_PHOAS) * 'var coq_VAL
and 'var case_switch =
| LSnil of coq_type * 'var coq_PHOAS
| LScons of int * coq_type * 'var coq_PHOAS * 'var case_switch
