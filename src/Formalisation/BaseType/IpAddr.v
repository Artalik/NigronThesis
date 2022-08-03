From Formalisation Require Export SizeNat.

Record Ipv4 := mk_ipv4 {a4 : nat8 ; b4 : nat8; c4 : nat8; d4 : nat8}.

Record Ipv6 := mk_ipv6 {a6 : nat16 ; b6 : nat16; c6 : nat16; d6 : nat16;
                        e6 : nat16 ; f6 : nat16; g6 : nat16; h6 : nat16}.

Inductive IpAddr :=
| V4 : Ipv4 -> IpAddr
| V6 : Ipv6 -> IpAddr.
