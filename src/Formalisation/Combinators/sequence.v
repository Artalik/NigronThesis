From Formalisation Require Import Nom.

Section sequence.

  Context {atom : Type}.

  Definition NomG := @NomG atom.

  Definition delimited {X Y Z} (first : NomG X) (second : NomG Y) (third : NomG Z) : NomG Y :=
    let! _ := first in
    let! v := second in
    let! _ := third in
    ret v.

  Definition pair {X Y} (first : NomG X) (second : NomG Y) : NomG (X * Y) :=
    let! f := first in
    let! s := second in
    ret (f,s).

  Definition preceded {X Y} (first : NomG X) (second : NomG Y) : NomG Y :=
    let! _ := first in
    second.

  Definition separated_pair {X Y Z} (first : NomG X) (sep : NomG Z) (second : NomG Y) : NomG (X * Y) :=
    let! f := first in
    let! _ := sep in
    let! s := second in
    ret (f,s).

  Definition terminated {X Y} (first : NomG X) (second : NomG Y) : NomG X :=
    let! v := first in
    let! _ := second in
    ret v.

End sequence.
