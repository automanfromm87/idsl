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
  | VRegex  of string * Str.regexp  (* (source, compiled); only used
                                       on the expected side of expect *)
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
  | VRegex (p, _) -> Printf.sprintf "r%S" p

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
  | Ast.LRegex p  -> VRegex (p, Str.regexp p)

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

(* Three-valued comparison: any operand of `missing` propagates to
   `missing`. Use `is missing` / `is present` to probe for it
   explicitly without entering the three-valued world. *)
let cmp_op op a b =
  match a, b with
  | VMissing, _ | _, VMissing -> VMissing
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

(* Asymmetric matcher used by `expect:` blocks.  Differs from
   `value_eq` in two ways:

   1. **Object literals are partial.**  The expected side must contain
      every field listed in the test; the actual side can have more.
      Lets test data evolve (new fields added) without breaking older
      tests that didn't mention them.
   2. **Regex match strings.**  When expected is `VRegex` and actual
      is `VString`, we run the pattern against the string. Used to
      assert "any reason text containing 'high-value'" without
      pinning the exact wording. *)
let rec expect_match expected actual =
  match expected, actual with
  | VWildcard, _ | _, VWildcard -> true
  | VRegex (_, re), VString s ->
      (try ignore (Str.search_forward re s 0); true
       with Not_found -> false)
  | VObject xs, VObject ys ->
      List.for_all (fun (k, v) ->
        match List.assoc_opt k ys with
        | Some w -> expect_match v w
        | None   -> false) xs
  | VList xs, VList ys when List.length xs = List.length ys ->
      List.for_all2 expect_match xs ys
  | _ -> value_eq expected actual

(* ---------- env ---------- *)

type env = {
  bindings   : (ident * value) list;
  instances  : (ident, value) Hashtbl.t;
  predicates : (ident, texpr) Hashtbl.t;
}

let empty_env = {
  bindings   = [];
  instances  = Hashtbl.create 0;
  predicates = Hashtbl.create 0;
}
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

let observed_value = function
  | VBool true  -> `True
  | VBool false -> `False
  | VMissing    -> `Missing
  | _           -> `False  (* non-bool defaults to false for coverage *)

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
  | TUnary (Ast.Not as op, sub) ->
      let v = eval env sub in
      Coverage.observe e.pos ~value:(observed_value v);
      eval_unop op v
  | TUnary (op, sub) -> eval_unop op (eval env sub)
  | TBin ((Ast.And | Ast.Or) as op, a, b) ->
      let r = eval_binop op (eval env a) (eval env b) in
      Coverage.observe e.pos ~value:(observed_value r);
      r
  | TBin (op, a, b) -> eval_binop op (eval env a) (eval env b)
  | TIf (c, t, el) ->
      let cv = eval env c in
      Coverage.observe e.pos ~value:(observed_value cv);
      (match cv with
       | VBool true  -> eval env t
       | VBool false -> eval env el
       | VMissing    -> VMissing
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
  | TIsMissing sub ->
      let v = eval env sub in
      let r = match v with VMissing -> true | _ -> false in
      Coverage.observe e.pos ~value:(if r then `True else `False);
      VBool r
  | TIsPresent sub ->
      let v = eval env sub in
      let r = match v with VMissing -> false | _ -> true in
      Coverage.observe e.pos ~value:(if r then `True else `False);
      VBool r
  | TCall (("min" | "max") as name, [a; b]) ->
      let va = eval env a and vb = eval env b in
      (match to_num va, to_num vb with
       | Some x, Some y ->
           let r = if name = "min" then min x y else max x y in
           if is_money va || is_money vb then VMoney r else VFloat r
       | _ -> err "%s: non-numeric" name)
  | TCall (name, [arg]) when Hashtbl.mem env.predicates name ->
      let body = Hashtbl.find env.predicates name in
      let arg_v = eval env arg in
      let kvs = match arg_v with
        | VObject kvs -> kvs
        | _ -> err "predicate %s: expected an object argument" name in
      (* Bind every (field, value) in the arg as a local; predicate
         body sees those plus the surrounding env's instances. *)
      let pred_env = List.fold_left
        (fun e (k, v) -> bind e k v) env kvs in
      eval pred_env body
  | TCall (name, _) ->
      err "call %s only valid as rule action / expectation" name
  | TSelf field_types ->
      VObject (List.map (fun (k, _) ->
        let v = match lookup env k with
          | Some v -> v
          | None   -> VMissing in
        (k, v)) field_types)

and eval_unop op v =
  match op, v with
  | Ast.Not, VBool b  -> VBool (not b)
  | Ast.Not, VMissing -> VMissing      (* three-valued *)
  | Ast.Not, _        -> err "not on non-bool: %s" (show_value v)
  | Ast.Neg, _ ->
      (match to_num v with
       | Some x -> VFloat (-. x)
       | None   -> err "negation on non-numeric")

and eval_binop op va vb =
  match op with
  | Ast.And ->
      (* Kleene three-valued AND. False short-circuits even when the
         other side is missing (we know the conjunction is false). *)
      (match va, vb with
       | VBool false, _ | _, VBool false   -> VBool false
       | VBool true,  VBool true           -> VBool true
       | VMissing, _ | _, VMissing         -> VMissing
       | _                                 -> VBool false)
  | Ast.Or ->
      (* Kleene three-valued OR. True short-circuits dually. *)
      (match va, vb with
       | VBool true, _ | _, VBool true     -> VBool true
       | VBool false, VBool false          -> VBool false
       | VMissing, _ | _, VMissing         -> VMissing
       | _                                 -> VBool false)
  | Ast.Eq  ->
      (match va, vb with
       | VMissing, _ | _, VMissing -> VMissing
       | _ -> VBool (value_eq va vb))
  | Ast.Neq ->
      (match va, vb with
       | VMissing, _ | _, VMissing -> VMissing
       | _ -> VBool (not (value_eq va vb)))
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
  schemas    : (ident, tschema) Hashtbl.t;
  instances  : (ident, value) Hashtbl.t;
  predicates : (ident, texpr) Hashtbl.t;
  rules      : trule list;
}

let make_ctx (tp : tprogram) =
  let schemas    = Hashtbl.create 16 in
  let instances  = Hashtbl.create 8 in
  let predicates = Hashtbl.create 8 in
  List.iter (fun s -> Hashtbl.replace schemas s.ts_name s) tp.schemas;
  List.iter (fun (p : tpredicate) ->
    Hashtbl.replace predicates p.tp_name p.tp_body) tp.predicates;
  let env_with_inst = { empty_env with instances; predicates } in
  List.iter (fun (i : tinstance) ->
    let kvs = List.map (fun (k, te) -> (k, eval env_with_inst te)) i.ti_values in
    Hashtbl.replace instances i.ti_name (VObject kvs)) tp.instances;
  let rules = List.stable_sort
    (fun a b -> compare b.tr_priority a.tr_priority) tp.rules in
  { schemas; instances; predicates; rules }

(* ---------- build object env from given ---------- *)

let derived_of = Typed.derived_fields

(* Fill in raw fields missing from the user's bindings with the
   schema's `default` expressions, so `default $1` actually delivers
   the fallback its keyword promises. Defaults are only consulted for
   field names the user did not explicitly bind — explicit bindings
   always win. *)
let apply_defaults sch env explicit_keys =
  List.fold_left (fun e (n, te) ->
    if List.mem n explicit_keys then e
    else bind e n (eval e te)) env sch.ts_defaults

let build_env ctx (g : tgiven) =
  let sch =
    match Hashtbl.find_opt ctx.schemas g.tg_schema with
    | Some s -> s
    | None   -> err "test: unknown schema %s" g.tg_schema in
  let env0 = { empty_env with
               instances = ctx.instances;
               predicates = ctx.predicates } in
  let env_raw =
    List.fold_left (fun e (k, v) -> bind e k (eval e v)) env0 g.tg_values in
  let explicit = List.map fst g.tg_values in
  let env_with_defaults = apply_defaults sch env_raw explicit in
  List.fold_left (fun e (n, te) -> bind e n (eval e te))
    env_with_defaults (derived_of sch)

(* Build an env from (field name → already-evaluated value) pairs and a
   schema. Used by Load when reading JSON inputs at runtime. *)
let build_env_from_values ?(instances = Hashtbl.create 0)
                          ?(predicates = Hashtbl.create 0)
                          sch raw_pairs =
  let env0 = { empty_env with instances; predicates } in
  let env_raw =
    List.fold_left (fun e (k, v) -> bind e k v) env0 raw_pairs in
  let explicit = List.map fst raw_pairs in
  let env_with_defaults = apply_defaults sch env_raw explicit in
  List.fold_left (fun e (n, te) -> bind e n (eval e te))
    env_with_defaults (derived_of sch)

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

(* A "matcher" is the expected (name, pre-evaluated arg values) pair.
   Evaluating expected_args once up front avoids recomputing them
   (and re-compiling regex literals) per outcome scanned. *)
type matcher = string * value list

let prepare_matcher env (_, name, args) : matcher =
  (name, List.map (eval env) args)

let matcher_match (n, vargs) (name, args) =
  n = name
  && List.length vargs = List.length args
  && List.for_all2 expect_match vargs args

let count_matching m outcomes =
  List.length (List.filter (matcher_match m) outcomes)

let first_match_index m outcomes =
  let rec loop i = function
    | [] -> None
    | o :: _ when matcher_match m o -> Some i
    | _ :: rest -> loop (i + 1) rest
  in
  loop 0 outcomes

let outcomes_summary = function
  | []  -> "[]"
  | os  -> Printf.sprintf "[%s]"
             (String.concat "; " (List.map show_outcome os))

let check_count name got bound label cmp =
  if cmp got bound then None
  else Some (Printf.sprintf
               "expected %s(...) %s %d time(s), got %d" name label bound got)

let check_order ~(label : string) ~(ok : int -> int -> bool)
    (ma : matcher) (mb : matcher) outcomes =
  match first_match_index ma outcomes, first_match_index mb outcomes with
  | Some ia, Some ib when ok ia ib -> None
  | Some _,  Some _ ->
      Some (Printf.sprintf
              "expected %s(...) %s %s(...), but the order was wrong"
              (fst ma) label (fst mb))
  | None, _ ->
      Some (Printf.sprintf
              "expected %s(...) to fire (%s-clause)" (fst ma) label)
  | _, None ->
      Some (Printf.sprintf
              "expected %s(...) to fire (%s-clause)" (fst mb) label)

let check_expectation env outcomes exp =
  let m c = prepare_matcher env c in
  match exp with
  | TMust c ->
      let mc = m c in
      if List.exists (matcher_match mc) outcomes then None
      else
        let n = fst mc in
        Some (Printf.sprintf "expected %s(...) to fire, got: %s"
                n (outcomes_summary outcomes))
  | TMustNot c ->
      let mc = m c in
      if List.exists (matcher_match mc) outcomes then
        Some (Printf.sprintf "expected NOT %s(...), but a match fired" (fst mc))
      else None
  | TTimes (c, n) ->
      let mc = m c in
      check_count (fst mc) (count_matching mc outcomes) n "exactly" (=)
  | TAtLeast (c, n) ->
      let mc = m c in
      check_count (fst mc) (count_matching mc outcomes) n "at least" (>=)
  | TAtMost (c, n) ->
      let mc = m c in
      check_count (fst mc) (count_matching mc outcomes) n "at most" (<=)
  | TBefore (a, b) ->
      check_order ~label:"before" ~ok:(<) (m a) (m b) outcomes
  | TAfter (a, b) ->
      check_order ~label:"after"  ~ok:(>) (m a) (m b) outcomes

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

(* Strip the trailing " #N" a table-driven test inserts, returning the
   parent name. Not a table case → returns the original name. *)
let case_parent name =
  match String.rindex_opt name '#' with
  | Some i when i > 0 && name.[i - 1] = ' ' ->
      let stem = String.sub name 0 (i - 1) in
      let suffix = String.sub name (i + 1) (String.length name - i - 1) in
      (try ignore (int_of_string suffix); Some stem
       with _ -> None)
  | _ -> None

let report ?(explain_failures = true) (results, all_rules) =
  let passed = List.length (List.filter (fun r -> r.passed) results) in
  let total = List.length results in
  (* Group consecutive passing table cases under their parent name. *)
  let rec emit_group = function
    | [] -> ()
    | r :: rest when not r.passed -> emit_one r; emit_group rest
    | r :: _ as all ->
        match case_parent r.rname with
        | None -> emit_one r; emit_group (List.tl all)
        | Some parent ->
            let same, others = List.partition (fun r' ->
              r'.passed && case_parent r'.rname = Some parent) all in
            (match List.length same with
             | 1 -> emit_one r
             | n -> Printf.printf "PASS  %s  (%d cases)\n" parent n);
            emit_group others
  and emit_one r =
    if r.passed then Printf.printf "PASS  %s\n" r.rname
    else begin
      Printf.printf "FAIL  %s\n" r.rname;
      List.iter (fun f -> Printf.printf "        %s\n" f) r.failures;
      if explain_failures then
        match r.test_env with
        | None -> ()
        | Some env ->
            let ctx = { schemas = Hashtbl.create 0;
                        instances = env.instances;
                        predicates = env.predicates;
                        rules = all_rules } in
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
    end
  in
  emit_group results;
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
