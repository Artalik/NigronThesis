From Formalisation Require Import SizeNat String.
From Formalisation Require Import Nom bin_combinators combinator multi bytes sequence.

Open Scope N_scope.

(* https://github.com/rusticata/ssh-parser/blob/master/src/ssh.rs *)

Record SshVersionS (S : Type) :=
  mk_sshversion {
    proto : S;
    software : S;
    comments : option S
  }.

Definition SshVersion := SshVersionS span.

Arguments mk_sshversion [_].

Global Instance Foldable_SshVersion : Foldable SshVersionS.
econstructor.
intros M sg m A f v.
eapply Monoid.f. eapply (f (proto _ v)).
eapply Monoid.f. eapply (f (software _ v)).
destruct (comments _ v). eapply (f a). eapply Monoid.mempty.
Defined.

Definition space := String " " char_line_ending.

Definition parse_version : NomG SshVersion :=
  let! proto := take_until("-") in
  let! _ := tag "-" in
  let! software := is_not space in
  let! comments := opt (let! _ := tag " " in
                        let! comments := not_line_ending in
                        ret comments) in
  ret (mk_sshversion proto software comments).

Definition parse_ssh_identification : NomG (VECTOR span * SshVersion) :=
  many_till
    (terminated (take_until char_line_ending) crlf)
    (delimited (tag "SSH-") parse_version line_ending).

Definition parse_string : NomG span :=
  length_data (let! v := be_u32 in
               ret (val v)).

Definition is_us_ascii (c : nat8) : bool :=
  (32 <=? val c) && (val c <=? 126) && (negb (val c =? 44)).

Definition parse_name : NomG span :=
  take_while1 is_us_ascii.

Definition span_to_string (s : span)  : NomB string :=
  repeat_compt (Some (len s)) (fun n res =>
                                 let! v := read s (len s - (n + 1)) in
                                 ret (String (ascii_of_N (val v)) res)) EmptyString.

Definition parse_name_list : NomG (VECTOR string) :=
  separated_list1 (tag ",") (let! v := parse_name in
                             span_to_string v).

Record SshPacketDisconnectS (S : Type) :=
  mk_disconnect { reason_code : nat32; description : S; lang : S }.

Definition SshPacketDisconnect := SshPacketDisconnectS span.

Global Instance Foldable_SshPacketDisconnect : Foldable SshPacketDisconnectS.
econstructor.
intros M sg m A f v.
eapply Monoid.f. eapply (f (description _ v)).
eapply (f (lang _ v)).
Defined.

Record SshPacketKeyExchangeS (S : Type) :=
  mk_sshpacketkeyexchange {
      cookie : S;
      kex_algs : S;
      server_host_key_algs : S;
      encr_algs_client_to_server : S;
      encr_algs_server_to_client : S;
      mac_algs_client_to_server : S;
      mac_algs_server_to_client : S;
      comp_algs_client_to_server : S;
      comp_algs_server_to_client : S;
      langs_client_to_server : S;
      langs_server_to_client : S;
      first_kex_packet_follows : bool;
    }.

Definition SshPacketKeyExchange := SshPacketKeyExchangeS span.

Arguments mk_sshpacketkeyexchange [S].

Global Instance Foldable_SshPacketKeyExchange : Foldable SshPacketKeyExchangeS.
econstructor.
intros M sg m A f v.
eapply Monoid.f. eapply (f (cookie _ v)).
eapply Monoid.f. eapply (f (kex_algs _ v)).
eapply Monoid.f. eapply (f (server_host_key_algs _ v)).
eapply Monoid.f. eapply (f (encr_algs_client_to_server _ v)).
eapply Monoid.f. eapply (f (encr_algs_server_to_client _ v)).
eapply Monoid.f. eapply (f (mac_algs_client_to_server _ v)).
eapply Monoid.f. eapply (f (mac_algs_server_to_client _ v)).
eapply Monoid.f. eapply (f (comp_algs_client_to_server _ v)).
eapply Monoid.f. eapply (f (encr_algs_server_to_client _ v)).
eapply Monoid.f. eapply (f (langs_client_to_server _ v)).
eapply (f (langs_server_to_client _ v)).
Defined.


Record SshPacketDebugS (S : Type) :=
  mk_sshpacketdebug {
      always_display : bool;
      message : S;
      debug_lang : S;
    }.

Definition SshPacketDebug := SshPacketDebugS span.

Arguments mk_sshpacketdebug [S].

Global Instance Foldable_SshPacketDebug : Foldable SshPacketDebugS.
econstructor.
intros M sg m A f v.
eapply Monoid.f. eapply (f (message _ v)).
eapply (f (debug_lang _ v)).
Defined.

Record SshPacketDhReplyS (S : Type) :=
  mk_sshpacketdhreply {
      pubkey_and_cert : S;
      fr : S;
      signature : S;
    }.

Definition SshPacketDhReply := SshPacketDhReplyS span.

Arguments mk_sshpacketdhreply [S].

Global Instance Foldable_SshPacketDhReply : Foldable SshPacketDhReplyS.
econstructor.
intros M sg m A g v.
eapply Monoid.f. eapply (g (pubkey_and_cert _ v)).
eapply Monoid.f. eapply (g (fr _ v)).
eapply (g (signature _ v)).
Defined.

Inductive SshPacketS (S : Type) :=
| Disconnect (d : SshPacketDisconnectS S )
| Ignore (s : S)
| Unimplemented (n : nat32)
| Debug (d: SshPacketDebugS S)
| ServiceRequest (s : S)
| ServiceAccept (s : S)
| KeyExchange (d: SshPacketKeyExchangeS S)
| NewKeys
| DiffieHellmanInit (s : S)
| DiffieHellmanReply (d : SshPacketDhReplyS S).

Arguments Disconnect [_].
Arguments Ignore [_].
Arguments Unimplemented [_].
Arguments Debug [_].
Arguments ServiceRequest [_] _.
Arguments ServiceAccept [_] _.
Arguments KeyExchange [_].
Arguments NewKeys {_}.
Arguments DiffieHellmanInit [_].
Arguments DiffieHellmanReply  [_].

Definition SshPacket := SshPacketS span.

Definition usize_16 := 16.

Definition parse_packet_key_exchange : NomG SshPacket :=
  let! cookie := take usize_16 in
  let! kex_algs := parse_string in
  let! server_host_key_algs := parse_string in
  let! encr_algs_client_to_server := parse_string in
  let! encr_algs_server_to_client := parse_string in
  let! max_algs_client_to_server := parse_string in
  let! max_algs_server_to_client := parse_string in
  let! comp_algs_client_to_server := parse_string in
  let! comp_algs_server_to_client := parse_string in
  let! langs_client_to_server := parse_string in
  let! langs_server_to_client := parse_string in
  let! first_kex_packet_follows := be_u8 in
  let! _ := be_u32 in
  let packet := mk_sshpacketkeyexchange
                  cookie
                  kex_algs
                  server_host_key_algs
                  encr_algs_client_to_server
                  encr_algs_server_to_client
                  max_algs_client_to_server
                  max_algs_server_to_client
                  comp_algs_client_to_server
                  comp_algs_server_to_client
                  langs_client_to_server
                  langs_server_to_client
                  (0 <? val first_kex_packet_follows) in
  ret (KeyExchange packet).

Definition parse_packet_dh_init : NomG SshPacket :=
  map parse_string (fun v => DiffieHellmanInit v).

Definition parse_packet_dh_reply : NomG SshPacket :=
  let! pubkey_and_cert := parse_string in
  let! fr := parse_string in
  let! signature := parse_string in
  let reply := mk_sshpacketdhreply pubkey_and_cert fr signature in
  ret (DiffieHellmanReply reply).


(* nécessite la concaténation de span pour être équivalent à la version suricata *)

Definition get_ecdsa_signature (s : SshPacketDhReply) : NomG (VECTOR span) :=
  scope (signature _ s)
    (let! s := parse_string in
     let! identifier := span_to_string s in
     let! blob := map_parser parse_string (pair parse_string parse_string) in
     ret (add (add (make _ 2) blob.1) blob.2)).

Definition parse_packet_disconnect : NomG SshPacket :=
  let! reason_code := be_u32 in
  let! description := parse_string in
  let! lang := parse_string in
  let packet := mk_disconnect _ reason_code description lang in
  ret (Disconnect packet).

Definition get_description (p : SshPacketDisconnect) : NomG string :=
  span_to_string (description _ p).

Definition get_reason (p : SshPacketDisconnect) : nat32 :=
  (reason_code _ p).

Definition parse_packet_debug : NomG SshPacket :=
  let! display := be_u8 in
  let! message := parse_string in
  let! lang := parse_string in
  let packet := mk_sshpacketdebug (0 <? val display) message lang in
  ret (Debug packet).

Definition get_message (p : SshPacketDebug) : NomG string :=
  span_to_string (message _ p).

Definition parse_ssh_packet : NomG (SshPacket * span) :=
  let! packet_length := be_u32 in
  let! padding_length := be_u8 in
  if val packet_length <? val padding_length + 1
  then fail
  else
    let! payload := map_parser (take (val packet_length - val padding_length - 1))
                      (let! msg_type := be_u8 in
                       match val msg_type with
                       | 1 => parse_packet_disconnect
                       | 2 => map parse_string (@Ignore _)
                       | 3 => map be_u32 (@Unimplemented _)
                       | 4 => parse_packet_debug
                       | 5 => map parse_string (@ServiceRequest _)
                       | 6 => map parse_string (@ServiceAccept _)
                       | 20 => parse_packet_key_exchange
                       | 21 => ret NewKeys
                       | 30 => parse_packet_dh_init
                       | 31 => parse_packet_dh_reply
                       | _ => fail
                       end ) in
    let! padding := take (val padding_length) in
    ret (payload, padding).

Definition test_name : bool :=
  let res := list_ascii_of_string "ssh-rsa" in
  let res := List.map ascii_to_nat8 res in
  match run 1000 parse_name res {| pos := 0; len := lengthN res |} with
  | Res (s, v) => (len s =? 0) && (pos v =? 0) && (len v =? lengthN res)
  | _ => false
  end.

Compute test_name.

Definition test_empty_name_list : bool :=
  let res := list_ascii_of_string "" in
  let res := List.map ascii_to_nat8 res in
  match run 1000 parse_name res {| pos := 0; len := lengthN res |} with
  | Res _ | NoFuel => false
  | NoRes => true
  end.

Compute test_empty_name_list.

Definition test_one_name_list : bool :=
  let res := list_ascii_of_string "ssh-rsa" in
  let res := List.map ascii_to_nat8 res in
  match run 1000 parse_name_list res {| pos := 0; len := lengthN res |} with
  | Res (s, v) => (len s =? 0) && (Vector.size (`v) =? 1) && (match Vector.get v 0 with
                                                             | Some s => String.eqb s "ssh-rsa"
                                                             | None => false
                                                             end)
  | NoFuel => false
  | NoRes => false
  end.

Compute test_one_name_list.


Definition test_two_name_list : bool :=
  let res := list_ascii_of_string "ssh-rsa,ssh-ecdsa" in
  let res := List.map ascii_to_nat8 res in
  match run 1000 parse_name_list res {| pos := 0; len := lengthN res |} with
  | Res (s, v) => (len s =? 0) && (Vector.size (`v) =? 2) &&
                   (match Vector.get v 0 with
                    | Some s => String.eqb s "ssh-rsa"
                    | None => false
                    end) && (match Vector.get v 1 with
                             | Some s => String.eqb s "ssh-ecdsa"
                             | None => false
                             end)
  | NoFuel => false
  | NoRes => false
  end.

Compute test_two_name_list.
