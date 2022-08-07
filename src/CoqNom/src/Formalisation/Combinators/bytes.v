From Formalisation Require Import String Nom combinator bin_combinators.

Local Open Scope N_scope.

Definition value_in_string (v : nat8) (str : string) : NomB bool :=
  repeat_compt (Some (string_length str))
         (fun n b =>
            match string_get n str with
            | None => fail
            | Some a =>
                ret (b || SizeNat.eqb v a)
            end)
         false.


Definition value_not_in_string (v : nat8) (str : string) : NomB bool :=
  repeat_compt (Some (string_length str))
         (fun n b =>
            match string_get n str with
            | None => fail
            | Some a =>
                ret (b && negb (SizeNat.eqb v a))
            end)
         true.

Definition value_in_span (v : nat8) (s : span) : NomB bool:=
  repeat_compt (Some (len s)) (fun n b =>
                           let! r := read s n in
                           ret (b || SizeNat.eqb v r)) false.

Definition value_not_in_span (v : nat8) (s : span) : NomB bool:=
  repeat_compt (Some (len s)) (fun n b =>
                           let! r := read s n in
                           ret (b && negb (SizeNat.eqb v r))) true.

Declare Scope combinator_scope.

Local Notation "v ∈ s" := (value_in_span v s) : combinator_scope.

Local Notation "v ∉ s" := (value_not_in_span v s) : combinator_scope.

Open Scope combinator_scope.

Definition is_a_span (s : span) : NomB span :=
  recognize (repeat None (fun _ =>
                            let! v := be_u8 in
                            let! b := v ∈ s in
                            if b then ret tt else fail) tt).

Definition is_a (s : string) : NomB span :=
  recognize (repeat None (fun _ =>
                            let! v := be_u8 in
                            let! b := value_in_string v s in
                            if b then ret tt else fail) tt).

Definition is_not_span (s : span) : NomB span :=
  recognize (repeat None (fun _ =>
                            let! v := be_u8 in
                            let! b := v ∉ s in
                            if b then ret tt else fail) tt).

Definition is_not (s : string) : NomB span :=
  recognize (repeat None (fun _ =>
                            let! v := be_u8 in
                            let! b := value_not_in_string v s in
                            if b then ret tt else fail) tt).

(* Si ça échoue, le pointeur n'avance pas en nom, j'ai essayé d'être fidèle. *)
Definition one_of_span (s: span) : NomB nat8 :=
  let! v := peek be_u8 in
  let! b := v ∈ s in
  if b then be_u8 else fail.

Definition one_of (s: string) : NomB nat8 :=
  let! v := peek be_u8 in
  let! b := value_in_string v s in
  if b then be_u8 else fail.

Definition none_of_span (s: span) : NomB nat8 :=
  let! v := peek be_u8 in
  let! b := v ∉ s in
  if b then be_u8 else fail.

Definition none_of (s: string) : NomB nat8 :=
  let! v := peek be_u8 in
  let! b := value_not_in_string v s in
  if b then be_u8 else fail.

Definition tag_span (s1 : span) : NomB span :=
  let! s2 := take (len s1) in
  let! b := repeat_compt (Some (len s1)) (fun n b =>
                                      let! r1 := read s1 n in
                                      let! r2 := read s2 n in
                                      ret (b && (SizeNat.eqb r1 r2))) true in
  if b then ret s2 else fail.

Definition tag (str : string) : NomB span :=
  let len := string_length str in
  let! s := take len in
  let! b := repeat_compt (Some len) (fun n b =>
                                 let! r := read s n in
                                 match string_get n str with
                                 | None => fail
                                 | Some a =>
                                     ret (b && SizeNat.eqb r a)
                                 end) true in
  if b then ret s else fail.

Definition take_till (cond : nat8 -> bool) : NomB span :=
  recognize (repeat None (fun s =>
                            let! v := be_u8 in
                            if cond v then fail else ret tt) tt).

Definition take_till1 (cond : nat8 -> bool) : NomB span :=
  let! s := recognize (repeat None (fun s =>
                                      let! v := be_u8 in
                                      if cond v then fail else ret tt) tt) in
  let! b := scope s is_empty in
  if b then fail else ret s.

Definition take_until_span (s : span) : NomB span :=
  recognize (repeat None (fun _ =>
                            let! b := alt (let! _ := tag_span s in
                                           ret true)
                                        (let! _ := take 1 in
                                         ret false) in
                            if b then fail else ret tt) tt).

Definition take_until (s : string) : NomB span :=
  recognize (repeat None (fun _ =>
                            let! b := alt (let! _ := tag s in
                                           ret true)
                                          (let! _ := take 1 in
                                           ret false) in
                            if b then fail else ret tt) tt).

Definition take_until1_span (s : span) : NomB span :=
  let! s := recognize (repeat None (fun _ =>
                                      let! b := alt (let! _ := tag_span s in
                                                     ret true)
                                                  (let! _ := take 1 in
                                                   ret false) in
                                      if b then fail else ret tt) tt) in
  let! b := scope s is_empty in
  if b then fail else ret s.

Definition take_until1 (s : string) : NomB span :=
  let! s := recognize (repeat None (fun _ =>
                                      let! b := alt (let! _ := tag s in
                                                     ret true)
                                                  (let! _ := take 1 in
                                                   ret false) in
                                      if b then fail else ret tt) tt) in
  let! b := scope s is_empty in
  if b then fail else ret s.

Definition take_while (cond : nat8 -> bool) : NomB span :=
  recognize (repeat None (fun s =>
                            let! v := be_u8 in
                            if cond v then ret tt else fail) tt).

Definition take_while1 (cond : nat8 -> bool) : NomB span :=
  let! s := recognize (repeat None (fun s =>
                            let! v := be_u8 in
                            if cond v then ret tt else fail) tt) in
  let! b := scope s is_empty in
  if b then fail else ret s.

Definition take_while_m_n (min max : N) (cond : nat8 -> bool) : NomB span :=
  recognize (
      let! _ := repeat (Some min) (fun s =>
                                let! v := be_u8 in
                                if cond v then ret tt else fail) tt in
      let res := max - min in
      repeat_compt None (fun n b =>
                           if n <? res
                           then
                             let! v := be_u8 in
                             if cond v then ret tt else fail
                           else
                             fail) tt).

Close Scope combinator_scope.
