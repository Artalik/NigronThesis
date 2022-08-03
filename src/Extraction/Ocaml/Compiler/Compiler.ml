open PHOAS

type manageValue =
  | ToFail
  | Value

module Env = Map.Make(String)

let string_fold_left f b s =
  let len = String.length s in
  let rec aux i b =
    if i = len
    then b
    else aux (i+1) (f b (String.get s i))
  in aux 0 b

let pre_existing_vectors =
  ["uint8_t"; "radius_attribute"; "IkeV2RawTransform"; "TrafficSelector"; "IkeV2Proposal"; "IkeV2Payload"]

module ExternFun =
  struct
    (* ligne à ajouter * fonction à ajouter * comment fournir la valeur * vecteurs existants * option existants * pairs existants ->
       valeur * lignes * fonctions * ou est la valeur * vecteurs existants * option existants * pairs existants *)
    type 'a t = (string Env.t * string list * string list * manageValue * string list * string list * (string * string) list) ->
                ('a * (string Env.t * string list * string list * manageValue * string list * string list * (string * string) list))
    let ret v = fun l -> (v,l)
    let bind m f = fun l ->
      let (v, l') = m l in
      f v l'
    let add_vector v = fun (env, l, f, m, vec, opt, p) ->
      if List.mem v pre_existing_vectors || List.mem v vec
      then
        (), (env, l, f, m, vec, opt, p)
      else
        (), (env, l, f, m, v :: vec, opt, p)
    let get_vectors () = fun (env, l, f, m, vec, opt, p) -> (vec, (env, l, f, m, vec, opt, p))
    let add_option o = fun (env, l, f, m, vec, opt, p) ->
      if List.mem o opt
      then
        (), (env, l, f, m, vec, opt, p)
      else
        (), (env, l, f, m, vec, o :: opt, p)
    let get_options () = fun (env, l, f, m, vec, opt, p) -> (opt, (env, l, f, m, vec, opt, p))
    let add_pair ty1 ty2 = fun (env, l, f, m, vec, opt, p) ->
      if List.mem (ty1, ty2) p
      then
        (), (env, l, f, m, vec, opt, p)
      else
        (), (env, l, f, m, vec, opt, (ty1, ty2) :: p)
    let get_pairs () = fun (env, l, f, m, vec, opt, p) -> (p, (env, l, f, m, vec, opt, p))
    let add_line s = fun (env, l, f, m, vec, opt, p) -> ((), (env, s :: l, f, m, vec, opt, p))
    let add_lines sl = fun (env, l, f, m, vec, opt, p) -> ((), (env, sl@l, f, m, vec, opt, p))
    let get_lines () = fun (env, l, f, m, vec, opt, p) -> (l, (env, [], f, m, vec, opt, p))
    let add_function s = fun (env, l, f, m, vec, opt, p) -> ((), (env, l, s :: f, m, vec, opt, p))
    let get_functions () = fun (env, l, f, m, vec, opt, p) -> (f, (env, l, f, m, vec, opt, p))
    let add_env key elem = fun (env, l, f, m, vec, opt, p) ->
      ((), (Env.add key elem env , l, f, m, vec, opt, p))
    let get_env () = fun (env, l, f, m, vec, opt, p) -> (env, (env, l, f, m, vec, opt, p))
    let get_manage () = fun (env, l, f, m, vec, opt, p) -> (m, (env, l, f, m, vec, opt, p))
    let set_manage m = fun (env, l, f, _, vec, opt, p) -> ((), (env, l, f, m, vec, opt, p))
    let scope_manage newm e = fun (env, l, f, oldm, vec, opt, p) ->
      let (v, (env, l, f, resm, vec, opt, p)) = e (env, l, f, newm, vec, opt, p) in
      ((resm,v), (env, l, f, oldm, vec, opt, p))
    let (let*) = bind
  end

open ExternFun

let gen_pos =
  let c = ref 0 in
  fun () -> incr c; "pos"^(string_of_int !c)

let gen_len =
  let c = ref 0 in
  fun () -> incr c; "len"^(string_of_int !c)

let gen_var =
  let c = ref 0 in
  fun () -> incr c; "var"^(string_of_int !c)

let gen_temp =
  let c = ref 0 in
  fun () -> incr c; "temp"^(string_of_int !c)

let gen_option =
  let c = ref 0 in
  fun () -> incr c; "option"^(string_of_int !c)

let construct_type_pair ty1 ty2 =
  let len_ty1 = String.length ty1 in
  let len_ty2 = String.length ty2 in
  if len_ty1 >= 100 || len_ty2 >= 100
  then assert false
  else
    "pair_"^
      (if len_ty1 < 10 then "0" else "")^
        string_of_int len_ty1^ty1^"_"^
            (if len_ty2 < 10 then "0" else "")^
              string_of_int len_ty2^ty2

let deconstruct_type_pair_fst ty =
  try
    let ty = String.sub ty 5 (String.length ty - 5) in
    let s_len_ty = String.sub ty 0 2 in
    let len_ty = int_of_string s_len_ty in
    String.sub ty 2 len_ty
  with _ -> print_string ("Probleme fst avec "^ty); assert false

let deconstruct_type_pair_snd ty =
  try
    let ty = String.sub ty 5 (String.length ty - 5) in
    let s_len_ty1 = String.sub ty 0 2 in
    let len_ty1 = int_of_string s_len_ty1 in
    let ty = String.sub ty (3 + len_ty1) (String.length ty - len_ty1 - 3) in
    let s_len_ty2 = String.sub ty 0 2 in
    let len_ty2 = int_of_string s_len_ty2 in
    String.sub ty 2 len_ty2
  with _ -> print_string ("Probleme snd avec "^ty); assert false

let construct_type_vector ty = "Vector_"^ty

let deconstruct_type_vector s =
  try
    String.sub s 7 (String.length s - 7)
  with _ -> print_string ("Probleme deconstruct vector avec "^s); assert false

let construct_type_option ty = "option_"^ty

let deconstruct_type_option s =
  try
    String.sub s 7 (String.length s - 7)
  with _ -> print_string ("Probleme deconstruct option avec "^s); assert false

let type_compteur_repeat = "uint64_t"

let int_to_uint (size : int) =
  let f = fun n k -> if size <= n then n else k in
  f 8 (f 16 (f 32 (f 64 128)))

let max_size_type ty1 ty2 =
  let ty1n = int_of_char (String.get ty1 4) in
  let ty2n = int_of_char (String.get ty2 4) in
  if ty1n < ty2n
  then ty2
  else ty1

let rec type_to_ctype : coq_type -> string = function
  | Nat -> "uint64_t"
  | NatN i -> "uint"^(string_of_int i)^"_t"
  | Bool -> "bool"
  | Vector ty -> construct_type_vector (type_to_ctype ty)
  | String -> "uint8_t*"
  | Unit -> "unit"
  | Span -> "span"
  | Unknown s -> s
  | Option ty -> construct_type_option (type_to_ctype ty)
  | Pair (tyl, tyr) -> construct_type_pair (type_to_ctype tyl) (type_to_ctype tyr)
  | Sum _ -> assert false

let type_of_VAL : type var. string coq_VAL -> string = function
  | Const (ty, _) | EUna (_, ty, _, _)
    | EBin (_, _, ty, _, _, _) | Var (ty, _) -> type_to_ctype ty

let rec type_of_PHOAS : string coq_PHOAS -> string = function
  | Cstruct (ty,_,_) -> type_to_ctype (Unknown ty)
  | Fail ty | CaseOption (_, _, ty, _, _) | IfThenElse (_, ty, _, _)
    | LetIn (_, _, ty, _) | Val (ty, _) | Switch (_, ty, _) | Alt (ty, _, _)
    | Local (_, ty, _) | Repeat (_, ty, _, _) ->
     type_to_ctype ty
  | Take _ -> type_to_ctype Span
  | Length -> type_to_ctype Nat
  | Read _ -> type_to_ctype (NatN 8)

module FV = Set.Make(String)

let fold_union (l : FV.t list) : FV.t =
  List.fold_left FV.union FV.empty l

(* free_variable_val v retourne l'ensemble des variables dans v *)
let rec free_variable_VAL : string coq_VAL -> FV.t =
  function
  | Var (_, v) -> FV.singleton v
  | EBin (_, _, _, _, v0, v1) -> FV.union (free_variable_VAL v0) (free_variable_VAL v1)
  | EUna (_, _, _, v) -> free_variable_VAL v
  | Const _ -> FV.empty

let rec free_variable_LIST : string coq_LIST -> FV.t =
  function
  | NIL -> FV.empty
  | CONS (_, v, l) -> FV.union (free_variable_VAL v) (free_variable_LIST l)

let rec free_variable_PHOAS : string coq_PHOAS -> FV.t =
  function
  | Cstruct (_,_,l) -> free_variable_LIST l
  | Val (_, v) -> free_variable_VAL v
  | LetIn (_, e, _, k) ->
     let fv_e = free_variable_PHOAS e in
     let var_name = gen_temp () in
     let fv_k = FV.remove var_name (free_variable_PHOAS (k var_name)) in
     FV.union fv_e fv_k
  | IfThenElse (b, _, e0, e1) ->
     let fv_b = free_variable_VAL b in
     let fv_e0 = free_variable_PHOAS e0 in
     let fv_e1 = free_variable_PHOAS e1 in
     FV.union fv_b (FV.union fv_e0 fv_e1)
  | CaseOption (_, o, _, e, k) ->
     let fv_o = free_variable_VAL o in
     let fv_e = free_variable_PHOAS e in
     let var_name = gen_temp () in
     let fv_k = FV.remove var_name (free_variable_PHOAS (k var_name)) in
     FV.union fv_o (FV.union fv_e fv_k)
  | Switch (v, _, c) ->
     let fv_v = free_variable_VAL v in
     let fv_c = free_variable_cases c in
     FV.union fv_v fv_c
  | Fail _ -> FV.empty
  | Take v -> free_variable_VAL v
  | Length -> FV.empty
  | Read (n, s) ->
     let fv_n = free_variable_VAL n in
     let fv_s = free_variable_VAL s in
     FV.union fv_n fv_s
  | Alt (_, e0, e1) ->
     let fv_e0 = free_variable_PHOAS e0 in
     let fv_e1 = free_variable_PHOAS e1 in
     FV.union fv_e0 fv_e1
  | Local (v, _, e) ->
     let fv_v = free_variable_VAL v in
     let fv_e = free_variable_PHOAS e in
     FV.union fv_v fv_e
  | Repeat (v, _, k, b) ->
     let fv_v = free_variable_VAL v in
     let fv_b = free_variable_VAL b in
     let tmp = gen_temp () in
     let fv_k = FV.remove tmp (free_variable_PHOAS (k tmp)) in
     FV.union fv_v (FV.union fv_b fv_k)

and free_variable_cases : string case_switch -> FV.t =
  function
  | LSnil (_, e) ->
     free_variable_PHOAS e
  | LScons (_, _, e, cases) ->
     let fv_e = free_variable_PHOAS e in
     let fv_cases = free_variable_cases cases in
     FV.union fv_e fv_cases

let rec is_var_or_add_line : string coq_VAL -> string ExternFun.t = function
  | Var (_,s) -> ret s
  | v ->
     let var_v = gen_var () in
     let type_v = type_of_VAL v in
     let* _ = add_env var_v type_v in
     let* s_v = string_of_VAL v in
     let* _ = add_line (type_v^" "^var_v^" = "^s_v^";") in
     ret var_v

and string_of_bin : string coq_VAL -> string coq_VAL -> coq_OpBin -> string ExternFun.t =
  fun v0 v1 ->
  let infix o =
    let* s_v0 = string_of_VAL v0 in
    let* s_v1 = string_of_VAL v1 in
    ret (s_v0 ^ o ^ s_v1) in
  function
  | EAdd -> infix " + "
  | ESub -> infix " - "
  | EMult -> infix " * "
  | EDiv -> infix " / "
  | EMod -> infix " % "
  | EEq -> infix " == "
  | ELe -> infix " <= "
  | ELt -> infix " < "
  | EAnd -> infix " && "
  | EOr -> infix " || "
  | EStringGet ->
     let* s_v0 = string_of_VAL v0 in
     let* s_v1 = string_of_VAL v1 in
     ret (s_v1^"["^s_v0^"]")
  | EPair (tyl, tyr) ->
     let ty_v0 = type_to_ctype tyl in
     let ty_v1 = type_to_ctype tyr  in
     let* _ = add_pair ty_v0 ty_v1 in
     let var = gen_var () in
     let* _ = add_line (type_to_ctype (Pair (tyl, tyr))^" "^var^";") in
     let* s_v0 = string_of_VAL v0 in
     let* s_v1 = string_of_VAL v1 in
     let* _ = add_line (var^".fst = "^s_v0^";") in
     let* _ = add_line (var^".snd = "^s_v1^";") in
     ret var
  | EpTo2p size ->
     let* s_v0 = string_of_VAL v0 in
     let* s_v1 = string_of_VAL v1 in
     let cast_first = "("^type_to_ctype (NatN (size* 2))^")"^s_v0 in
     ret ("((("^cast_first^") <<"^ string_of_int size ^") | ("^s_v1^"))")
  | EGetVec _ ->
     let* s_v0 = string_of_VAL v0 in
     let* s_v1 = string_of_VAL v1 in
     ret (s_v0^".data["^s_v1^"]")
  | EAddVec ty ->
     let ty_v0 = type_to_ctype (Vector ty) in
     let* s_v0 = is_var_or_add_line v0 in
     let* s_v1 = string_of_VAL v1 in
     let name_func = ty_v0^"_add" in
     let* _ = add_line (name_func^"(&"^s_v0^", "^s_v1^");") in
     ret s_v0

and string_of_una : string coq_VAL -> coq_OpUna -> string ExternFun.t = fun v ->
  function
  | EVal _ -> string_of_VAL v
  | ENot ->
     let* s_v = string_of_VAL v in
     ret ("!"^s_v)
  | EStringLen ->
     let* s_v = is_var_or_add_line v in
     ret ("strlen("^s_v^")")
  | EFst _ ->
     let* s_v = string_of_VAL v in
     ret (s_v^".fst")
  | ESnd _ ->
     let* s_v = string_of_VAL v in
     ret (s_v^".snd")
  | ESome ty ->
     let ty_opt = type_to_ctype (Option ty) in
     let ty_v = type_to_ctype ty in
     let* _ = add_option ty_v in
     let* s_v = string_of_VAL v in
     let var = gen_var () in
     let* _ = add_env var ty_opt in
     let* _ = add_line (ty_opt^" "^var^";") in
     let* _ = add_line (var^".ok = true;") in
     let* _ = add_line (var^".val = "^s_v^";") in
     ret var
  | EInl _ -> assert false
  | EInr _ -> assert false
  | ELen ->
     let* s_i = string_of_VAL v in
     ret (s_i^".length")
  | EMake ty ->
     let ty_vec = type_to_ctype (Vector ty) in
     let ty = type_to_ctype ty in
     let* _ = add_vector ty in
     let* s_v = string_of_VAL v in
     let name_func = ty_vec^"_make" in
     let var = gen_var () in
     let* _ = add_line (ty_vec^" "^var^";") in
     let* _ = add_env var ty_vec in
     let* _ = add_line (name_func^"("^s_v^", &"^var^");") in
     ret var

and string_of_literal : coq_Literal -> string ExternFun.t = function
  | ENat i -> ret (string_of_int i)
  | ENatN (_, i) -> ret (string_of_int i)
  | EBool b -> ret (if b then "true" else "false")
  | EString s -> ret ("\""^ s ^"\"")
  | ENone ty ->
     let ty_opt = type_to_ctype (Option ty) in
     let ty = type_to_ctype ty in
     let* _ = add_option ty in
     let var = gen_var () in
     let* _ = add_line (ty_opt^" "^var^";") in
     let* _ = add_line (var^".ok = false;") in
     let* _ = add_env var ty_opt in
     ret var
  | EUnit -> assert false

and string_of_VAL : string coq_VAL -> string ExternFun.t = function
  | Var (_, v) -> ret v
  | EBin (_, _, _, o, v0, v1) -> string_of_bin v0 v1 o
  | EUna (_, _, o, v) -> string_of_una v o
  | Const (_, v) -> string_of_literal v

let rec string_of_LIST : string coq_LIST -> string ExternFun.t = function
  | NIL -> ret ""
  | CONS (_, v, l) ->
     let* s_v = is_var_or_add_line v in
     let* s_l = string_of_LIST l in
     ret (s_v^","^s_l)


let new_lines (l : string list) : string =
  List.fold_left (fun all string -> string^"\n"^all) "" l

let extract_lines : unit -> string ExternFun.t = fun _ ->
  let* l = get_lines () in
  ret (new_lines l)

let string_of_signature (env : string Env.t) (arguments : FV.t) =
  try
    FV.fold (fun elt a ->
        let type_elt = Env.find elt env in
        a^", "^type_elt^" "^elt) arguments ""
  with _ -> print_endline "Problème signature FV"; assert false

let string_of_arguments (arguments : FV.t) =
  FV.fold (fun elt a -> a^", "^elt) arguments ""

let gen_fun_alt =
  let c = ref 0 in
  fun () -> incr c; "fun_alt"^(string_of_int !c)

let gen_local =
  let c = ref 0 in
  fun () -> incr c; "local"^(string_of_int !c)

let gen_repeat =
  let c = ref 0 in
  fun () -> incr c; "repeat"^(string_of_int !c)

let gen_fun_repeat =
  let c = ref 0 in
  fun () -> incr c; "fun_repeat"^(string_of_int !c)

let corps_repeat fun_repeat repeat i b res =
  "int "^repeat^"{
  if("^i^".ok){
          for(int v = 0; v < "^i^".val; v++){
                   "^b^" = *"^res^";
                   if(!"^fun_repeat^") return 0;
                 }
               *"^res^" = "^b^";
          }else{
          while(true){
                   "^b^" = *"^res^";
                   if(!"^fun_repeat^"){
                        *"^res^" = "^b^";
                        return 1;
                   }
          }
      }
      return 1;
   }\n"


let rec string_of_PHOAS : string coq_PHOAS -> string ExternFun.t = function
  | Cstruct (ty, constr, l) ->
     let* s_l = string_of_LIST l in
     let var = gen_var () in
     let* _ = add_env var ty in
     let* _ = add_line (ty^" "^var^";") in
     let* _ = add_line (constr^"("^s_l^"&"^var^");") in
     ret var
  | Val (ty, v) -> is_var_or_add_line v
  | LetIn (_, e, _, k) ->
     let* s_e = string_of_PHOAS e in
     let* m = get_manage () in
     begin
       match m with
       | ToFail -> ret "0"
       | _ -> string_of_PHOAS (k s_e)
     end

  | IfThenElse (b, ty, e0, e1) ->
     let* env = get_env () in
     let* m = get_manage () in
     let ty = type_to_ctype ty in
     let var = gen_var () in
     let* _ = add_env var ty in
     let* _ = add_line (ty^" "^var^";") in
     let* s_b = string_of_VAL b in
     let* _ = add_line ("if ("^s_b^"){") in
     let* (is_fail_e0, s_e0) = scope_manage m (string_of_PHOAS e0) in
     let* _ = if is_fail_e0 = ToFail then ret () else add_line (var^" = "^s_e0^";") in
     let* _ = add_line ("}else{") in
     let* (is_fail_e1, s_e1) = scope_manage m (string_of_PHOAS e1) in
     let* _ = if is_fail_e1 = ToFail then ret () else add_line (var^" = "^s_e1^";") in
     let* _ = add_line "}" in
     begin
       match is_fail_e0, is_fail_e1 with
       | ToFail, ToFail ->
          let* _ = get_lines () in
          let* _ = set_manage ToFail in
          let* _ = add_line "return 0;" in
          ret "0"
       | _ ->
          ret var
     end

  | CaseOption (_, o, _, e, k) -> assert false
  | Switch (n, ty, cases) ->
     let* s_n = string_of_VAL n in
     let* pre_assign = extract_lines () in
     let name_result = gen_var () in
     let* env = get_env () in
     let ty = type_to_ctype ty in
     let* s_cases = cases_to_string name_result cases in
     let v = pre_assign^ty^" "^name_result^";\n"^"switch ("^s_n^"){\n\n"^s_cases^"\n}\n" in
     let* _ = add_line v in
     ret name_result
  | Fail _ ->
     let* _ = add_line "return 0;" in
     let* _ = set_manage ToFail in
     ret "0"
  | Take n ->
     let var = gen_var () in
     let ty = type_of_PHOAS (Take n) in
     let* _ = add_env var ty in
     let* _ = add_line (ty^" "^var^";") in
     let* s_n = string_of_VAL n in
     let* _ = add_line ("take(bin, "^s_n^", &"^var^");") in
     ret var
  | Length ->
     let var = gen_var () in
     let ty = type_of_PHOAS Length in
     let* _ = add_env var ty in
     let* _ = add_line (ty^" "^var^" = bin->length;") in
     ret var
  | Read (s, n) ->
     let* s_s = string_of_VAL s in
     let* s_n = string_of_VAL n in
     let var = gen_var () in
     let ty = type_of_PHOAS (Read (s, n)) in
     let* _ = add_env var ty in
     let* _ = add_line (ty^" "^var^";") in
     let* _ = add_line (var^" = "^s_s^".pos["^s_n^"];") in
     ret var

  | Alt (ty, e0, e1) ->
     let* m = get_manage () in
     let* lines = get_lines () in
     let* env = get_env () in
     let fv_e0 = free_variable_PHOAS e0 in
     let name_result = gen_var () in
     let name_save = gen_var () in
     let name_fun_e0 = gen_fun_alt () in
     let name_fun_e1 = gen_fun_alt () in
     let ty = type_to_ctype ty in
     let ty_e0 = ty in
     let ty_e1 = ty in
     let* (is_fail_e0, s_e0) = scope_manage m (string_of_PHOAS e0) in
     let* lines_e0 = extract_lines () in
     let* (is_fail_e1, s_e1) = scope_manage m (string_of_PHOAS e1) in
     let* lines_e1 = extract_lines () in
     let call_e0 = name_fun_e0^"(bin, &"^name_result^string_of_arguments fv_e0^")" in
     let func_e0 =
       "int "^name_fun_e0
       ^"(span* bin, "^ty_e0^"* "^name_result^string_of_signature env fv_e0^"){\n"
       ^lines_e0^
         "*"^name_result^" = "^s_e0^";\n"^"return 1;\n"^
           "}\n\n" in
     let fv_e1 = free_variable_PHOAS e1 in
     let call_e1 = name_fun_e1^"(bin, &"^name_result^string_of_arguments fv_e1^")" in
     let func_e1 =
       "int "^name_fun_e1
       ^"(span* bin, "^ty_e1^"* "^name_result^string_of_signature env fv_e1^"){\n"
       ^lines_e1^
         "*"^name_result^" = "^s_e1^";\n"^"return 1;\n"^
           "}\n\n" in
     begin
       match is_fail_e0, is_fail_e1 with
       | ToFail, ToFail ->
          let* _ = set_manage ToFail in
          let* _ = add_line "return 0;" in
          ret "0"
       | ToFail, _ ->
          let* _ = add_lines lines in
          let* _ = add_env name_result ty_e1 in
          let* _ = add_line (ty_e1^" "^name_result^";") in
          let* _ = add_function func_e1 in
          let* _ = add_line ("if(!"^call_e1^") return 0;") in
          ret name_result
       | _, ToFail ->
          let* _ = add_lines lines in
          let* _ = add_env name_result ty_e0 in
          let* _ = add_line (ty_e0^" "^name_result^";") in
          let* _ = add_function func_e0 in
          let* _ = add_line ("if(!"^call_e0^") return 0;") in
          ret name_result
       | _, _ ->
          let* _ = add_lines lines in
          let* _ = add_env name_result ty_e0 in
          let* _ = add_line (ty_e0^" "^name_result^";") in
          let* _ = add_function func_e0 in
          let* _ = add_function func_e1 in
          let* _ = add_line ("span "^name_save^";") in
          let* _ = add_line ("get(bin, &"^name_save^");") in
          let* _ = add_line ("if (!"^call_e0^"){\nset(bin,"^name_save^");\n"^"if(!"^call_e1^") return 0;}") in
          ret name_result
     end

  | Local (s, ty, e) ->
     let ty_e = type_to_ctype ty in
     let* lines = get_lines () in
     let* env = get_env () in
     let* s_e = string_of_PHOAS e in
     let* lines_e = extract_lines () in
     let* is_fail = get_manage () in
     let* _ = add_lines lines in
     if is_fail = ToFail
     then
       let* _ = add_line ("return 0;") in
       ret "0"
     else
       let* s_s = string_of_VAL s in
       let* lines = get_lines () in
       let name_local = gen_local () in
       let fv_e = free_variable_PHOAS e in
       let name_result = gen_var () in
       let func =
         "int  "^name_local
         ^"(span* bin, "^ty_e^"* "^name_result^string_of_signature env fv_e^"){\n"
         ^lines_e^
           "*"^name_result^" = "^s_e^";\n"^"return 1;\n"^
             "}\n\n" in
       let* _ = add_lines lines in
       let* _ = add_env name_result ty_e in
       let* _ = add_line (ty_e^" "^name_result^";") in
       let* _ = add_function func in
       let local_some = name_local^"(&("^s_s^".val), &"^name_result^string_of_arguments fv_e^")" in
       let save =  gen_var () in
       let call_some = "if(!"^local_some^") return 0;" in
       let* _ = add_line ("if("^s_s^".ok){") in
       let* _ = add_line ("span "^save^" = "^s_s^".val"^";") in
       let* _ = add_line call_some in
       let* _ = add_line (s_s^".val"^" = "^save^";") in
       let* _ = add_line "}else{" in
       let* _ = add_line ("span "^save^";") in
       let* _ = add_line ("get(bin, &"^save^");") in
       let local_none = name_local^"(bin, &"^name_result^string_of_arguments fv_e^")" in
       let call_none = "if(!"^local_none^") return 0;" in
       let* _ = add_line call_none in
       let* _ = add_line ("set(bin, "^save^");\n}") in
       ret name_result

  | Repeat (on, ty, k, b) ->
     let ty = type_to_ctype ty in
     let* s_on = string_of_VAL on in
     let* s_b = is_var_or_add_line b in
     let fun_repeat = gen_fun_repeat () in
     let repeat = gen_repeat () in
     let name_result = gen_var () in
     let* _ = add_env name_result ty in
     let* env = get_env () in
     let exec_k = k s_b in
     let fv_k = FV.remove s_b (free_variable_PHOAS exec_k) in
     let var_fv_signature = string_of_signature env fv_k in
     let s_arguments = string_of_arguments fv_k in
     let s_fun_repeat = fun_repeat^"(bin, "^s_b^", "^name_result^s_arguments^")" in
     let s_repeat = repeat^"(bin, "^s_on^", "^s_b^", &"^name_result^s_arguments^")" in
     let sign_fun_repeat = fun_repeat^"(span* bin, "^ty^" "^s_b^", "^ty^"* "^name_result^var_fv_signature^")" in
     let sign_repeat = repeat^"(span* bin, option_uint64_t "^s_on^", "^ty^" "^s_b^", "^ty^"* "^name_result^var_fv_signature^")" in
     let* lines = get_lines () in
     let* m = get_manage () in
     let* (is_fail_k, s_k) = scope_manage m (string_of_PHOAS exec_k) in
     let* lines_k = extract_lines () in
     let* _ = add_function ("int "^sign_fun_repeat^"{\n"^lines_k^(if is_fail_k = ToFail then "" else "*"^name_result^" = "^s_k^";\nreturn 1;")^"\n}\n") in
     let* _ = add_function (corps_repeat s_fun_repeat sign_repeat s_on s_b name_result) in
     let* _ = add_lines lines in
     let* _ = add_line (ty^" "^name_result^" = "^s_b^";") in
     let* _ = add_line ("if(!"^s_repeat^") return 0;") in
     ret name_result

and cases_to_string : string -> string case_switch -> string ExternFun.t =
  fun var ->
  function
  | LSnil (_, e) ->
     let* m = get_manage () in
     let* (is_fail, s_e) = scope_manage m (string_of_PHOAS e) in
     let* _ = if is_fail = ToFail then ret () else add_line (var^" = "^s_e^";") in
     let* pre_assign = extract_lines () in
     ret ("default :\n{\n"^pre_assign^(if is_fail = ToFail then "" else "break;")^"\n}")
  | LScons (i, _, e, cases) ->
     let* m = get_manage () in
     let* (is_fail, s_e) = scope_manage m (string_of_PHOAS e) in
     let* _ = if is_fail = ToFail then ret () else add_line (var^" = "^s_e^";") in
     let* pre_assign = extract_lines () in
     let* s_cases = cases_to_string var cases in
     ret ("case "^string_of_int i^" :\n{\n" ^pre_assign^(if is_fail = ToFail then "" else "break;")^"\n}"^"\n"^s_cases)



let string_of_expr : string -> string -> string coq_PHOAS -> string ExternFun.t =
  fun name_parser name_result e ->
  let* v = string_of_PHOAS e in
  let* m = get_manage () in
  let* _ = if m = ToFail then ret () else add_line ("*"^name_result^" = "^v^";") in
  let* lines = extract_lines () in
  let* f_extern = get_functions () in
  let ty_e = type_of_PHOAS e in
  let ty_e = if ty_e = "fail" then "int" else ty_e in
  let v = "int "^name_parser^"(span* bin, "^ty_e^"* "^name_result^"){\n"^lines^(if m = ToFail then "" else "return 1;")^"\n}" in
  let* vectors = get_vectors () in
  let* options = get_options () in
  let* pairs = get_pairs () in
  let res = List.fold_left (fun a b -> b^"\n"^a) v f_extern in
  let res = List.fold_left (fun a b -> "DEFINE_VECTOR("^b^");\n"^a) res vectors in
  let res = List.fold_left (fun a b -> "DEFINE_OPTION("^b^");\n"^a) res options in
  let res = List.fold_left
              (fun a (ty1, ty2) ->
                let len_ty1 = String.length ty1 in
                let len_ty2 = String.length ty2 in
                let s_len_ty1 = (if len_ty1 < 10 then "0" else "")^string_of_int len_ty1 in
                let s_len_ty2 = (if len_ty2 < 10 then "0" else "")^string_of_int len_ty2 in
                "DEFINE_PAIR("^s_len_ty1^", "^ty1^", "^s_len_ty2^", "^ty2^");\n"^a) res pairs in
  ret res

let compile : string -> string -> string coq_PHOAS -> string = fun header name e ->
  let name_result =  gen_var () in
  let code = fst (string_of_expr name name_result e (Env.empty, [], [], Value, [], [], [])) in
  let entete = "#include \""^header^"\"\n" in
  entete^code

let compile_to : string -> string -> string -> string coq_PHOAS -> unit =
  fun header s name e ->
  let out_file = open_out s in
  Printf.fprintf out_file "%s" (compile header name e);
  close_out out_file;
  ignore (Sys.command ("clang-format -i "^s))
