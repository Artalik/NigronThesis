From Formalisation Require Import SizeNat Vector radius_attr Nom.
From Formalisation Require Import bin_combinators combinator multi.

(* https://github.com/rusticata/radius-parser/blob/master/src/radius.rs *)

(* Radius Packet *)

Record RadiusCode := mk_code {radiuscode : nat8}.

Record RadiusDataS (S : Type) : Type :=
  mk_radiusdata {
      code : RadiusCode;
      identifier : nat8;
      length : nat16;
      authenticator : S;
      attributes : option (VECTOR (@RadiusAttributeS S)) }.

Arguments code [S].
Arguments identifier [S].
Arguments length [S].
Arguments authenticator [S].
Arguments attributes [S].

Definition foldMap `{Monoid.Monoid M} {A} (fold : A -> M) (res : RadiusDataS A) : M :=
  Monoid.f (fold (authenticator res))
    match attributes res with
    | None => Monoid.mempty
    | Some arr => foldMap _ _ fold arr
    end.

Global Instance RadiusData_Foldable : Foldable RadiusDataS :=
  Build_Foldable _ (@foldMap).

Definition RadiusData := RadiusDataS span.

Definition sizeu16 : N := 16.

Definition parse_radius_data : NomG RadiusData :=
  let! code := map be_u8 mk_code in
  let! identifier := be_u8 in
  let! length := be_u16 in
  let! authenticator := take sizeu16 in
  let! attributes :=
     cond (20 <? val length)%N
          (map_parser
             (take (val length - 20))
             (many1 parse_radius_attribute)) in
  ret (mk_radiusdata _ code identifier length authenticator attributes).


Definition parse_radius : nat -> list nat8 -> option RadiusData :=
  parse parse_radius_data.

#[tactic="NSize"] Equations test : list nat8 :=
  test :=
    [(_8 1);(_8 103);(_8 0);(_8 87);(_8 64);(_8 182);(_8 100);(_8 219);(_8 245);(_8 214);
     (_8 129);(_8 178);(_8 173);(_8 189);(_8 23);(_8 105);(_8 81);(_8 81);(_8 24);(_8 200);
     (_8 1);(_8 7);(_8 115);(_8 116);(_8 101);(_8 118);(_8 101);(_8 2);(_8 18);(_8 219);
     (_8 198);(_8 196);(_8 183);(_8 88);(_8 190);(_8 20);(_8 240);(_8 5);(_8 179);(_8 135);
     (_8 124);(_8 158);(_8 47);(_8 182);(_8 1);(_8 4);(_8 6);(_8 192);(_8 168);(_8 0);
     (_8 28);(_8 5);(_8 6);(_8 0);(_8 0);(_8 0);(_8 123);(_8 80);(_8 18);(_8 95);
     (_8 15);(_8 134);(_8 71);(_8 232);(_8 200);(_8 155);(_8 216);(_8 129);(_8 54);(_8 66);
     (_8 104);(_8 252);(_8 208);(_8 69);(_8 50);(_8 79);(_8 12);(_8 2);(_8 102);(_8 0);
     (_8 10);(_8 1);(_8 115);(_8 116);(_8 101);(_8 118);(_8 101) ].

Definition result_test := Eval vm_compute in parse_radius 100 test.

(* Résultat de rusticata :
RadiusData { code: RadiusCode(1),
            identifier: 103,
            length: 87,
            authenticator: [64, 182, 100, 219, 245, 214, 129, 178, 173, 189, 23, 105, 81, 81, 24, 200],
            attributes: Some(
               [UserName([115, 116, 101, 118, 101]),
                UserPassword([219, 198, 196, 183, 88, 190, 20, 240, 5, 179, 135, 124, 158, 47, 182, 1]),
                NasIPAddress(192.168.0.28),
                NasPort(123),
                Unknown(80, [95, 15, 134, 71, 232, 200, 155, 216, 129, 54, 66, 104, 252, 208, 69, 50]),
                Unknown(79, [2, 102, 0, 10, 1, 115, 116, 101, 118, 101])]) }
 *)

Lemma radius_test_ok :
  match result_test with
  | None => False
  | Some v =>
      val (radiuscode (code v)) = 1%N /\
        val (identifier v) = 103%N /\
        val (length v) = 87%N /\
        match attributes v with
        | None => False
        | Some v =>
            Vector.get v 0%N = Some (UserName (mk_span 22%N 5%N)) /\
              Vector.get v 1%N = Some (UserPassword (mk_span 29%N 16%N)) /\
              match Vector.get v 2%N with
              | Some (NasIPAddress ip) =>
                  val (a4 ip) = 192%N /\
                    val (b4 ip) = 168%N /\
                    val (c4 ip) = 0%N /\
                    val (d4 ip) = 28%N
              | _ => False
              end /\
              match Vector.get v 3%N with
              | Some (NasPort n) => val n = 123%N
              | _ => False
              end /\
              match Vector.get v 4%N with
              | Some (Unknown n s) => val n = 80%N /\ s = mk_span 59%N 16%N
              | _ => False
              end /\
              match Vector.get v 5%N with
              | Some (Unknown n s) => val n = 79%N /\ s = mk_span 77%N 10%N
              | _ => False
              end
        end
  end.
  cbv. repeat split.
Qed.
