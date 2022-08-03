From Formalisation Require Import Nom.

Open Scope N_scope.

Section combinator.

  Context {atom : Type}.

  Definition NomG := @NomG atom.

  Definition is_empty : NomG bool :=
    let! len := length in
    ret (len =? 0).

  Definition all_consuming {X} (p : NomG X) : NomG X :=
    let! v := p in
    let! b := is_empty in
    if b
    then ret v
    else fail.

  Definition cond {X} (b : bool) (c : NomG X) : NomG (option X) :=
    if b
    then
      let! v := c in
      ret (Some v)
    else
      ret None.

  Definition recognize {X} (c : NomG X) : NomG span :=
    let! len_before := length in
    let! len_after := peek (let! _ := c in length) in
    take (len_before - len_after).

  Definition consumed {X} (c: NomG X) : NomG (span * X) :=
    let! len_before := length in
    let! (v, len_after) := peek (let! v := c in
                                 let! len := length in
                                 ret (v, len)) in
    let! s := take (len_before - len_after) in
    ret (s, v).

  Definition eof : NomG unit :=
    let! b := is_empty in
    if b
    then ret ()
    else
      fail.

  Definition flat_map {X Y} := @bind X Y.

  Definition map {X Y} (c : NomG X) (f : X -> Y) : NomG Y :=
    let! v := c in
    ret (f v).

  Definition into {X Y} := @map X Y.

  Definition map_opt {X Y} (c : NomG X) (f : X -> option Y) : NomG Y :=
    let! v := c in
    match f v with
    | Some v => ret v
    | None => fail
    end.

  Definition map_parser {X} (c1 : NomG span) (c2 : NomG X) : NomG X :=
    let! s := c1 in
    scope s c2.

  Definition not {X} (c : NomG X): NomG unit :=
    let! b := alt (let! v := c in ret true) (ret false) in
    if b
    then
      fail
    else
      ret tt.

  Definition opt {X} (c : NomG X): NomG(option X) :=
    alt (let! v := c in ret (Some v)) (ret None).

  Definition rest : NomG span :=
    let! l := length in
    take l.

  Definition rest_len : NomG N := length.

  Definition success {X} : X -> NomG X := ret.

  Definition value {X Y} (val : X) (c : NomG Y) : NomG X :=
    let! _ := c in
    ret val.

  Definition verify {X} (c : NomG X) (b : X -> bool) : NomG X :=
    let! v := c in
    if b v
    then
      ret v
    else
      fail.

End combinator.

Close Scope N_scope.
