From Formalisation Require Import SizeNat.
From Coq Require Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlZInt ExtrOcamlNativeString.

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "None" "Some" ].

Extract Constant nat8 => uint8.
Extract Constant nat16 => uint16.
Extract Constant nat32 => uint32.
Extract Constant nat64 => uint64.
Extract Constant nat128 => uint128.
