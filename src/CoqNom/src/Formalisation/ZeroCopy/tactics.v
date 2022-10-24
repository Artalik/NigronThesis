From Formalisation Require Export ProgramLogic combinator_spec multi_spec bin_combinators_spec.


Ltac WpTac :=
  match goal with

  (* return *)
  | |- {{ _ }} ret _ {{ _; _ }} => eapply ret_rule

  (* Bind *)
  | |- {{ _ }} let! _ := _ in _ {{ _; _ }} => iBind

  (* Fail *)
  | |- {{ _ }} fail {{ _; _ }} => eapply fail_rule

  (* Length *)
  | |- {{ emp }} length {{ _; _ }} => eapply length_rule
  | |- {{ _ }} length {{ _; _ }} => Frame_emp length_rule


  (* Take *)
  | |- {{ emp }} take _ {{ _; _ }} => eapply take_rule
  | |- {{ _ }} take _ {{ _; _ }} => Frame_emp take_rule


  (* Alt *)
  | |- {{ _ }} alt _ _ {{ _; _ }} => eapply alt_rule

  (* Map_parser *)
  | |- {{ emp }} map_parser _ _ {{ _; _ }} => eapply map_parser_rule; [Frame | idtac]
  | |- {{ _ }} map_parser _ _ {{ _; _ }} => eapply map_parser_rule

  (* Many1 *)
  | |- {{ emp }} many1 _ {{ _; _ }} => eapply many1_rule
  | |- {{ _ }} many1 _ {{ _; _ }} => Frame_emp many1_rule

  (* rest *)
  | |- {{ emp }} rest {{ _; _ }} => eapply rest_rule
  | |- {{ _ }} rest {{ _; _ }} => Frame_emp rest_rule

  (* be_u8 *)
  | |- {{ emp }} be_u8 {{ _; _ }} => eapply u8_rule
  | |- {{ _ }} be_u8 {{ _; _ }} => Frame_emp u8_rule

  (* be_u16 *)
  | |- {{ emp }} be_u16 {{ _; _ }} => eapply u16_rule
  | |- {{ _ }} be_u16 {{ _; _ }} => Frame_emp u16_rule

  (* be_u32 *)
  | |- {{ emp }} be_u32 {{ _; _ }} => eapply u32_rule
  | |- {{ _ }} be_u32 {{ _; _ }} => Frame_emp u32_rule

  (* be_u64 *)
  | |- {{ emp }} be_u64 {{ _; _ }} => eapply u64_rule
  | |- {{ _ }} be_u64 {{ _; _ }} => Frame_emp u64_rule

  (* verify *)
  | |- {{ _ }} verify _ _ {{ _; _ }} => eapply verify_rule

  (* map *)
  | |- {{ _ }} combinator.map _ _ {{ _; _ }} => iBind(*eapply map_rule *)

  (* cond *)
  | |- {{ _ }} cond _ _ {{ _; _ }} => eapply cond_rule; [idtac | idtac]

  (* get_ipv4 *)
  | |- {{ emp }} get_ipv4 {{ _; _ }} => eapply get_ipv4_rule
  | |- {{ _ }} get_ipv4 {{ _; _ }} => Frame_emp get_ipv4_rule

  (* get_ipv6 *)
  | |- {{ emp }} get_ipv6 {{ _; _ }} => eapply get_ipv6_rule
  | |- {{ _ }} get_ipv6 {{ _; _ }} => Frame_emp get_ipv6_rule


  (* count *)
  | |- {{ emp }} count _ {{ _; _ }} => eapply count_rule
  | |- {{ _ }} count _ _ {{ _; _ }} => Frame_emp count_rule

  (* pattern matching*)
  | |- {{ _ }} match ?x with _ => _ end {{ _; _ }} => destruct x
  | |- {{ _ }} match ?x with _ => _ end _ {{ _; _ }} => destruct x
  | |- {{ _ }} match ?x with _ => _ end _ _ {{ _; _ }} => destruct x
  | |- {{ _ }} match ?x with _ => _ end _ _ _ {{ _; _ }} => destruct x
  | |- {{ _ }} match ?x with _ => _ end _ _ _ _ {{ _; _ }} => destruct x
  | |- {{ _ }} match ?x with _ => _ end _ _ _ _ _ {{ _; _ }} => destruct x
  | |- {{ _ }} match ?x with _ => _ end _ _ _ _ _ _ {{ _; _ }} => destruct x
  | |- {{ _ }} match ?x with _ => _ end _ _ _ _ _ _ _ {{ _; _ }} => destruct x
  end.
