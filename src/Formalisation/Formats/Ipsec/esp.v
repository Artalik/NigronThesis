From Formalisation Require Import Span SizeNat.
From Formalisation Require Import ikev2 Nom combinator bin_combinators ikev2_parser.

Record ESPHeaderS (S :Type) :=
  mk_espheader {
      spi_index : S;
      seq : nat32;
      data : S
    }.

Definition ESPHeader := ESPHeaderS span.

Arguments mk_espheader [_].
Arguments spi_index [_].
Arguments seq [_].
Arguments data [_].

Global Instance FOldable_ESPHeader : Foldable ESPHeaderS.
econstructor.
intros M sg m A f v. eapply Monoid.f. eapply (f (spi_index v)).
eapply (f (data v)).
Defined.

Inductive ESPData :=
| ESP (e : ESPHeader)
| IKE (i : IkeV2Header).

Definition parse_esp_header : NomG ESPHeader :=
  let! spi_index := take 4 in
  let! seq := be_u32 in
  let! data := rest in
  ret (mk_espheader spi_index seq data).

Definition parse_esp_encapsulated : NomG ESPData :=
  let! v := be_u32 in
  if val v =? 0
  then
    map parse_ikev2_header IKE
  else
    map parse_esp_header ESP.
