(* Evaluator over the typed AST. Names are pre-resolved (VarLocal /
   VarField / VarTag), so the only runtime ambiguity is whether a field
   was provided in the test's `given` block — handled via VMissing. *)

open Typed

type value =
  | VInt    of int
  | VFloat  of float
  | VBool   of bool
  | VString of string
  | VMoney  of float
  | VDate   of string
  | VDuration of int          (* days *)
  | VList   of value list
  | VObject of (string * value) list
  | VTag    of string
  | VMissing
  | VWildcard

type outcome = string * value list


exception Eval_error of string
let err fmt = Printf.ksprintf (fun s -> raise (Eval_error s)) fmt

(* ---------- pretty ---------- *)

let format_money f =
  if Float.is_integer f && Float.abs f < 1e16 then
    let n = int_of_float f in
    let s = string_of_int (abs n) in
    let len = String.length s in
    let b = Buffer.create (len + len / 3 + 2) in
    if n < 0 then Buffer.add_char b '-';
    Buffer.add_char b '$';
    String.iteri (fun i c ->
      if i > 0 && (len - i) mod 3 = 0 then Buffer.add_char b ',';
      Buffer.add_char b c) s;
    Buffer.contents b
  else Printf.sprintf "$%.2f" f

let rec show_value = function
  | VInt i      -> string_of_int i
  | VFloat f    -> Printf.sprintf "%g" f
  | VBool b     -> string_of_bool b
  | VString s   -> Printf.sprintf "%S" s
  | VMoney f    -> format_money f
  | VDate d     -> d
  | VDuration n -> Printf.sprintf "%dd" n
  | VTag s      -> s
  | VList vs    -> "[" ^ String.concat ", " (List.map show_value vs) ^ "]"
  | VObject kvs ->
      "{" ^ String.concat ", "
              (List.map (fun (k, v) -> k ^ ": " ^ show_value v) kvs) ^ "}"
  | VMissing    -> "missing"
  | VWildcard   -> "_"

let show_outcome (name, args) =
  Printf.sprintf "%s(%s)" name (String.concat ", " (List.map show_value args))

(* User-facing format: drop debug tag prefixes. *)
let pp_value v   = Typed.strip_tags (show_value v)
let pp_outcome o = Typed.strip_tags (show_outcome o)

(* ---------- helpers ---------- *)

(* "$5,000,000" -> 5000000.0 *)
let parse_money s =
  let no_dollar = String.sub s 1 (String.length s - 1) in
  float_of_string (String.concat "" (String.split_on_char ',' no_dollar))

let lit_to_value = function
  | Ast.LInt i    -> VInt i
  | Ast.LFloat f  -> VFloat f
  | Ast.LString s -> VString s
  | Ast.LBool b   -> VBool b
  | Ast.LMoney s  -> VMoney (parse_money s)
  | Ast.LDate s   -> VDate s

let to_num = function
  | VInt i      -> Some (float_of_int i)
  | VFloat f    -> Some f
  | VMoney f    -> Some f
  | VDuration n -> Some (float_of_int n)
  | _ -> None

(* "YYYY-MM-DD" → julian day number (proleptic Gregorian). *)
let parse_date s =
  if String.length s <> 10 || s.[4] <> '-' || s.[7] <> '-'
  then err "bad date %S" s
  else
    try
      let y = int_of_string (String.sub s 0 4) in
      let m = int_of_string (String.sub s 5 2) in
      let d = int_of_string (String.sub s 8 2) in
      (y, m, d)
    with _ -> err "bad date %S" s

let julian_day (y, m, d) =
  let a = (14 - m) / 12 in
  let y' = y + 4800 - a in
  let m' = m + 12 * a - 3 in
  d + (153 * m' + 2) / 5 + 365 * y' + y'/4 - y'/100 + y'/400 - 32045

let date_diff_days a b =
  julian_day (parse_date a) - julian_day (parse_date b)

(* Convert a julian-day count back to a YYYY-MM-DD civil date (proleptic
   Gregorian). Inverse of `julian_day`. *)
let civil_of_jdn jdn =
  let a = jdn + 32044 in
  let b = (4 * a + 3) / 146097 in
  let c = a - (146097 * b) / 4 in
  let d = (4 * c + 3) / 1461 in
  let e = c - (1461 * d) / 4 in
  let m = (5 * e + 2) / 153 in
  let day   = e - (153 * m + 2) / 5 + 1 in
  let month = m + 3 - 12 * (m / 10) in
  let year  = 100 * b + d - 4800 + (m / 10) in
  (year, month, day)

let format_date (y, m, d) = Printf.sprintf "%04d-%02d-%02d" y m d

let date_plus_days s n =
  format_date (civil_of_jdn (julian_day (parse_date s) + n))

(* ---------- comparison & arithmetic on values ---------- *)

let is_money = function VMoney _ -> true | _ -> false

let num_op op a b =
  match a, b with
  | VMissing, _ | _, VMissing -> VMissing
  | _ ->
    (match to_num a, to_num b with
     | Some x, Some y ->
         let r = op x y in
         if is_money a || is_money b then VMoney r else VFloat r
     | _ -> err "non-numeric: %s %s" (show_value a) (show_value b))

let cmp_op op a b =
  match a, b with
  | VMissing, _ | _, VMissing -> VBool false
  | VDate x, VDate y     -> VBool (op (compare x y) 0)
  | VString x, VString y -> VBool (op (compare x y) 0)
  | _ ->
    (match to_num a, to_num b with
     | Some x, Some y -> VBool (op (compare x y) 0)
     | _ -> err "incomparable: %s, %s" (show_value a) (show_value b))

let rec value_eq a b =
  match a, b with
  | VWildcard, _ | _, VWildcard -> true
  | VMissing, VMissing          -> true
  | VInt x, VInt y       -> x = y
  | VBool x, VBool y     -> x = y
  | VString x, VString y -> x = y
  | VTag x, VTag y       -> x = y
  | VDate x, VDate y     -> x = y
  | VDuration x, VDuration y -> x = y
  | VList xs, VList ys ->
      List.length xs = List.length ys && List.for_all2 value_eq xs ys
  | VObject xs, VObject ys ->
      List.length xs = List.length ys
      && List.for_all (fun (k, v) ->
           match List.assoc_opt k ys with
           | Some w -> value_eq v w
           | None   -> false) xs
  | _ ->
    (match to_num a, to_num b with
     | Some x, Some y -> x = y
     | _ -> false)

(* ---------- env ---------- *)

type env = {
  bindings  : (ident * value) list;
  instances : (ident, value) Hashtbl.t;
}

let empty_env = { bindings = []; instances = Hashtbl.create 0 }
let bind env k v = { env with bindings = (k, v) :: env.bindings }
let lookup env k = List.assoc_opt k env.bindings

type test_result = {
  rname     : string;
  passed    : bool;
  failures  : string list;
  outcomes  : outcome list;
  fired     : string list;
  test_env  : env option;
}

(* ---------- expr eval ---------- *)

let pred_true = function VBool true -> true | _ -> false

let rec eval env (e : texpr) =
  match e.node with
  | TLit l    -> lit_to_value l
  | TWildcard -> VWildcard
  | TMissing  -> VMissing
  | TVar (VarTag s)   -> VTag s
  | TVar (VarInstance id) ->
      (match Hashtbl.find_opt env.instances id with
       | Some v -> v
       | None   -> err "unknown instance %s" id)
  | TVar (VarLocal id) | TVar (VarField id) ->
      (match lookup env id with
       | Some v -> v
       | None   -> VMissing)   (* raw field absent in given *)
  | TPath (obj, _, f) ->
      (match eval env obj with
       | VObject kvs ->
           (match List.assoc_opt f kvs with
            | Some v -> v
            | None   -> VMissing)
       | VDuration n ->
           (match f with
            | "days"  -> VInt n
            | "years" -> VFloat (float_of_int n /. 365.25)
            | _ -> err "Duration has no field `%s`" f)
       | VMissing -> VMissing
       | v -> err "field access on non-object: %s.%s" (show_value v) f)
  | TList tes    -> VList (List.map (eval env) tes)
  | TObject kvs  -> VObject (List.map (fun (k, v) -> (k, eval env v)) kvs)
  | TUnary (op, e) -> eval_unop op (eval env e)
  | TBin (op, a, b) -> eval_binop op (eval env a) (eval env b)
  | TIf (c, t, el) ->
      (match eval env c with
       | VBool true  -> eval env t
       | VBool false -> eval env el
       | VMissing    -> eval env el
       | v -> err "if condition not bool: %s" (show_value v))
  | TAny (x, y, p) ->
      with_list env y (VBool false) (fun items ->
        VBool (List.exists (fun item ->
          pred_true (eval (bind env x item) p)) items))
  | TEvery (x, y, p) ->
      with_list env y (VBool true) (fun items ->
        VBool (List.for_all (fun item ->
          pred_true (eval (bind env x item) p)) items))
  | TCount (x, y, p) ->
      with_list env y (VInt 0) (fun items ->
        VInt (List.fold_left (fun n item ->
          if pred_true (eval (bind env x item) p) then n + 1 else n) 0 items))
  | TSum (f, x, y, p) ->
      with_list env y (VFloat 0.0) (fun items ->
        VFloat (List.fold_left (fun n item ->
          let env' = bind env x item in
          if pred_true (eval env' p) then
            match to_num (eval env' f) with Some v -> n +. v | None -> n
          else n) 0.0 items))
  | TIsMissing e ->
      (match eval env e with VMissing -> VBool true  | _ -> VBool false)
  | TIsPresent e ->
      (match eval env e with VMissing -> VBool false | _ -> VBool true)
  | TCall (("min" | "max") as name, [a; b]) ->
      let va = eval env a and vb = eval env b in
      (match to_num va, to_num vb with
       | Some x, Some y ->
           let r = if name = "min" then min x y else max x y in
           if is_money va || is_money vb then VMoney r else VFloat r
       | _ -> err "%s: non-numeric" name)
  | TCall (name, _) ->
      err "call %s only valid as rule action / expectation" name

and eval_unop op v =
  match op, v with
  | Ast.Not, VBool b  -> VBool (not b)
  | Ast.Not, VMissing -> VBool true
  | Ast.Not, _        -> err "not on non-bool: %s" (show_value v)
  | Ast.Neg, _ ->
      (match to_num v with
       | Some x -> VFloat (-. x)
       | None   -> err "negation on non-numeric")

and eval_binop op va vb =
  match op with
  | Ast.And ->
      (match va, vb with VBool x, VBool y -> VBool (x && y) | _ -> VBool false)
  | Ast.Or ->
      (match va, vb with VBool x, VBool y -> VBool (x || y) | _ -> VBool false)
  | Ast.Eq  -> VBool (value_eq va vb)
  | Ast.Neq -> VBool (not (value_eq va vb))
  | Ast.Lt  -> cmp_op (<)  va vb
  | Ast.Gt  -> cmp_op (>)  va vb
  | Ast.Leq -> cmp_op (<=) va vb
  | Ast.Geq -> cmp_op (>=) va vb
  | Ast.Add ->
      (match va, vb with
       | VString x, VString y         -> VString (x ^ y)
       | VString x, v                 -> VString (x ^ show_value v)
       | v, VString y                 -> VString (show_value v ^ y)
       | VDate d, VDuration n
       | VDuration n, VDate d         -> VDate (date_plus_days d n)
       | VDuration a, VDuration b     -> VDuration (a + b)
       | _ -> num_op (+.) va vb)
  | Ast.Sub ->
      (match va, vb with
       | VDate a, VDate b             -> VDuration (date_diff_days a b)
       | VDate d, VDuration n         -> VDate (date_plus_days d (-n))
       | VDuration a, VDuration b     -> VDuration (a - b)
       | _ -> num_op (-.) va vb)
  | Ast.Mul ->
      (match va, vb with
       | VDuration n, VInt k
       | VInt k, VDuration n          -> VDuration (n * k)
       | _ -> num_op ( *. ) va vb)
  | Ast.Div -> num_op (/.)  va vb

and with_list env y on_missing on_list =
  match lookup env y with
  | Some (VList items) -> on_list items
  | Some VMissing | None -> on_missing
  | Some v -> err "%s is not a list (got %s)" y (show_value v)

(* ---------- per-program context ---------- *)

type ctx = {
  schemas   : (ident, tschema) Hashtbl.t;
  instances : (ident, value) Hashtbl.t;
  rules     : trule list;
}

let make_ctx (tp : tprogram) =
  let schemas   = Hashtbl.create 16 in
  let instances = Hashtbl.create 8 in
  List.iter (fun s -> Hashtbl.replace schemas s.ts_name s) tp.schemas;
  let env_with_inst = { empty_env with instances } in
  List.iter (fun (i : tinstance) ->
    let kvs = List.map (fun (k, te) -> (k, eval env_with_inst te)) i.ti_values in
    Hashtbl.replace instances i.ti_name (VObject kvs)) tp.instances;
  (* Higher tr_priority fires first; equal-priority preserves source order. *)
  let rules = List.stable_sort
    (fun a b -> compare b.tr_priority a.tr_priority) tp.rules in
  { schemas; instances; rules }

(* ---------- build object env from given ---------- *)

let derived_of = Typed.derived_fields

let build_env ctx (g : tgiven) =
  let sch =
    match Hashtbl.find_opt ctx.schemas g.tg_schema with
    | Some s -> s
    | None   -> err "test: unknown schema %s" g.tg_schema in
  let env0 = { empty_env with instances = ctx.instances } in
  let env_raw =
    List.fold_left (fun e (k, v) -> bind e k (eval e v)) env0 g.tg_values in
  List.fold_left (fun e (n, te) -> bind e n (eval e te))
    env_raw (derived_of sch)

(* Build an env from (field name → already-evaluated value) pairs and a
   schema. Used by Load when reading JSON inputs at runtime. *)
let build_env_from_values ?(instances = Hashtbl.create 0) sch raw_pairs =
  let env0 = { empty_env with instances } in
  let env_raw =
    List.fold_left (fun e (k, v) -> bind e k v) env0 raw_pairs in
  List.fold_left (fun e (n, te) -> bind e n (eval e te))
    env_raw (derived_of sch)

(* ---------- run rules → outcomes ---------- *)

let run_rules env (rules : trule list) =
  let fired = ref [] in
  let outs = List.fold_left (fun acc r ->
    let fires = List.for_all (fun p -> pred_true (eval env p)) r.tr_when in
    if fires then begin
      fired := String.concat "." r.tr_path :: !fired;
      let calls = List.rev_map
        (fun (_pos, n, args) -> (n, List.map (eval env) args)) r.tr_then in
      List.rev_append calls acc
    end else acc) [] rules in
  (List.rev !fired, List.rev outs)

(* ---------- expectation matching ---------- *)

let outcome_matches env (call_name, expected_args) (name, args) =
  call_name = name
  && List.length expected_args = List.length args
  && List.for_all2 (fun e a -> value_eq (eval env e) a) expected_args args

let check_expectation env outcomes = function
  | TMust (_p, n, args) ->
      if List.exists (outcome_matches env (n, args)) outcomes then None
      else Some (Printf.sprintf "expected %s(...) to fire, got: [%s]"
                   n (String.concat "; " (List.map show_outcome outcomes)))
  | TMustNot (_p, n, args) ->
      if List.exists (outcome_matches env (n, args)) outcomes then
        Some (Printf.sprintf "expected NOT %s(...), but a match fired" n)
      else None

(* ---------- run ---------- *)

let run_test ctx (t : ttest) =
  try
    let env = build_env ctx t.tt_given in
    let fired, outcomes = run_rules env ctx.rules in
    let failures =
      List.filter_map (check_expectation env outcomes) t.tt_expect in
    { rname = t.tt_name; passed = failures = [];
      failures; outcomes; fired; test_env = Some env }
  with Eval_error msg ->
    { rname = t.tt_name; passed = false;
      failures = ["eval error: " ^ msg];
      outcomes = []; fired = []; test_env = None }

let run_all ?(filter = fun _ -> true) (tp : tprogram) =
  let ctx = make_ctx tp in
  let tests = List.filter (fun t -> filter t.tt_name) tp.tests in
  let results = List.map (run_test ctx) tests in
  results, ctx.rules

let report ?(explain_failures = true) (results, all_rules) =
  let passed = List.length (List.filter (fun r -> r.passed) results) in
  let total = List.length results in
  List.iter (fun r ->
    if r.passed then Printf.printf "PASS  %s\n" r.rname
    else begin
      Printf.printf "FAIL  %s\n" r.rname;
      List.iter (fun f -> Printf.printf "        %s\n" f) r.failures;
      if explain_failures then
        match r.test_env with
        | None -> ()
        | Some env ->
            let ctx = { schemas = Hashtbl.create 0;
                        instances = env.instances; rules = all_rules } in
            (* Use a temporary explain call. We can't actually call Explain
               from here without a circular dep — provide an inline simpler
               trace: for each rule, show fired status + first failing pred. *)
            ignore ctx;
            List.iter (fun rule ->
              let fired = List.for_all
                (fun p -> pred_true (eval env p)) rule.tr_when in
              if fired then
                Printf.printf "        [✓ fired] %s\n"
                  (String.concat "." rule.tr_path)
              else begin
                let first_false =
                  List.find_opt (fun p ->
                    match eval env p with VBool true -> false | _ -> true)
                    rule.tr_when in
                let reason = match first_false with
                  | Some p -> Typed.pp_expr p
                  | None   -> "(no predicates)" in
                Printf.printf "        [✗ skip ] %s — %s false\n"
                  (String.concat "." rule.tr_path) reason
              end) all_rules
    end) results;
  Printf.printf "\n%d/%d test(s) passed\n" passed total;
  (* coverage: which rules fired in at least one test *)
  let fire_count = Hashtbl.create 16 in
  List.iter (fun r ->
    List.iter (fun path ->
      let n = try Hashtbl.find fire_count path with Not_found -> 0 in
      Hashtbl.replace fire_count path (n + 1)) r.fired) results;
  if all_rules <> [] then begin
    Printf.printf "\nRule coverage:\n";
    List.iter (fun r ->
      let path = String.concat "." r.tr_path in
      match Hashtbl.find_opt fire_count path with
      | Some n -> Printf.printf "  ✓ %s  (fired in %d test%s)\n"
                    path n (if n = 1 then "" else "s")
      | None   -> Printf.printf "  ✗ %s  (never fired)\n" path) all_rules
  end;
  passed = total
