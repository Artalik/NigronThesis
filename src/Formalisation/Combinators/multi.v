From Formalisation Require Import Nom combinator.

Open Scope N_scope.

Section multi.

  Context {atom : Type}.

  Definition NomG := @NomG atom.


  Definition count (n : N) {X} (e : NomG X) : NomG (VECTOR X) :=
    repeat (Some n)
           (fun r =>
              let! v := e in
              ret (Vector.add r v)) (Vector.make X 2).

  Definition fold_many0 {X Y} (e : NomG X) (init : Y) (f : Y -> X -> Y) : NomG Y :=
    repeat None (fun b =>
                   let! v := e in
                   ret (f b v)) init.

  Definition fold_many1 {X Y} (e : NomG X) (init : Y) (f : Y -> X -> Y) : NomG Y :=
    let! v := e in
    repeat None (fun b =>
                   let! v := e in
                   ret (f b v)) (f init v).


  Definition fold_many_m_n {X Y} (min : N) (max : N) (e : NomG X) (init : Y) (f : Y -> X -> Y) : NomG Y :=
    let! v := repeat (Some min) (fun b =>
                                   let! v := e in
                                   ret (f b v)) init in
    let res := max - min in
    repeat_compt None (fun n b =>
                   if n <? res
                   then
                     let! v := e in
                     ret (f b v)
                   else
                     fail) v.

  Definition length_count {X} (c1 : NomG N) (c2 : NomG X) : NomG (VECTOR X) :=
    let! n := c1 in
    count n c2.

  Definition length_data (c : NomG N) : NomG span :=
    let! n := c in
    take n.

  Definition length_value {X} (c0 : NomG N) (c1 : NomG X) : NomG X :=
    map_parser (length_data c0) c1.

  Definition many0 {X} (c : NomG X) : NomG (VECTOR X) :=
    repeat None (fun r =>
                   let! len0 := length in
                   let! v := c in
                   let! len1 := length in
                   if len0 =? len1
                   then fail
                   else ret (Vector.add r v)) (Vector.make X 2).


  Definition many0_count {X} (c : NomG X) : NomG N :=
    repeat_compt None
           (fun n _ =>
              let! len0 := length in
              let! _ := c in
              let! len1 := length in
              if len0 =? len1
              then fail
              else ret n) 0.

  Definition many1 {X} (c : NomG X) : NomG (VECTOR X) :=
    let! len0 := length in
    let! v := c in
    let! len1 := length in
    if len0 =? len1
    then fail
    else
      repeat None (fun r =>
                     let! len0 := length in
                     let! v := c in
                     let! len1 := length in
                     if len0 =? len1
                     then fail
                     else ret (Vector.add r v)) (add (make X 2) v).

  Definition many1_count {X} (c : NomG X) : NomG N :=
    let! _ := c in
    let! n := many0_count c in
    ret (n + 1).


  Definition many_m_n {X} (min : N) (max : N) (c : NomG X) : NomG (VECTOR X) :=
    let! v := repeat_compt (Some min) (fun n b =>
                                   let! v := c in
                                   ret (set b n v)) (Vector.make X min) in
    let res := max - min in
    repeat_compt None (fun n b =>
                   if n <? res
                   then
                     let! v := c in
                     ret (add b v)
                   else
                     fail) v.

  Definition many_till {X Y} (c0 : NomG X) (c1 : NomG Y) : NomG (VECTOR X * Y) :=
    let! vec := repeat None (fun vec =>
                               let! b := alt (let! _ := peek c1 in
                                              ret true)
                                             (ret false) in
                               if b
                               then fail
                               else
                                 let! v := c0 in
                                 ret (add vec v)) (make X 1) in
    let! v := c1 in
    ret (vec,v).

  Definition separated_list0 {X Y} (sep : NomG X) (c : NomG Y) : NomG (VECTOR Y) :=
    let vec := make Y 2 in
    alt
      (let! v := c in
       repeat None (fun b =>
                      let! _ := sep in
                      let! v := c in
                      ret (add b v)) (add vec v))
      (ret vec).


  Definition separated_list1 {X Y} (sep : NomG X) (c : NomG Y) : NomG (VECTOR Y) :=
    let vec := make Y 2 in
    let! v := c in
    alt
      (repeat None (fun b =>
                      let! _ := sep in
                      let! v := c in
                      ret (add b v)) (add vec v))
      (ret vec).

End multi.

Close Scope N_scope.
