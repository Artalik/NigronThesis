From Formalisation Require Import SizeNat Vector radius_attr Nom.
From Formalisation Require Import bin_combinators combinator multi.

(* https://github.com/rusticata/radius-parser/blob/master/src/radius_attr.rs *)

(* Radius Packet *)

Record RadiusCode := mk_code {radiuscode : nat8}.

Record RadiusDataS (S : Type) : Type := mk_radiusdata
                       { code : RadiusCode;
                         identifier : nat8;
                         length : nat16;
                         authenticator : S;
                         attributes : option (VECTOR (@RadiusAttributeS S))
                       }.

Arguments code [S].
Arguments identifier [S].
Arguments length [S].
Arguments authenticator [S].
Arguments attributes [S].

Definition foldr {A B} (f : A -> B -> B) (base : B) (res : RadiusDataS A) : B :=
  f (authenticator res)
    match attributes res with
    | None => base
    | Some arr => List.fold_right (fun r l' => Foldable.foldr _ _ f l' r.2) base (values (`arr))
    end.

Definition foldMap {M} `{Monoid.Monoid M} {A} (fold : A -> M) (base : RadiusDataS A) : M :=
  Monoid.f (fold (authenticator base))
           match attributes base with
           | None => Monoid.mempty
           | Some arr =>
               List.fold_right (fun r l' => Monoid.f (foldMap _ _ fold r.2) l')
                               Monoid.mempty
                               (Vector.values (`arr))
           end.

Global Instance RadiusData_Foldable : Foldable RadiusDataS :=
  Build_Foldable _ (@foldr) (@foldMap).

Definition RadiusData := RadiusDataS span.

Definition sizeu16 : N := 16.

Definition parse_radius_data : NomG RadiusData :=
  let! code := map be_u8 mk_code  in
  let! identifier := be_u8 in
  let! length := be_u16 in
  let! authenticator := take sizeu16 in
  let! attributes :=
     cond (20 <? val length)%N
          (map_parser
             (take (val length - 20))
             (many1 parse_radius_attribute)) in
  ret (mk_radiusdata _ code identifier length authenticator attributes).
