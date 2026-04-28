(* Evaluator interface. Internal types kept abstract where possible; the
   constructors of `value` are exposed because Load (JSON → value) and
   Dump (value → JSON) need to build / inspect them. *)

open Typed

type value =
  | VInt    of int
  | VFloat  of float
  | VBool   of bool
  | VString of string
  | VMoney  of float
  | VDate   of string
  | VDuration of int
  | VList   of value list
  | VObject of (string * value) list
  | VTag    of string
  | VRegex  of string * Str.regexp
  | VMissing
  | VWildcard

type outcome = string * value list

type env
type ctx = {
  schemas    : (ident, tschema) Hashtbl.t;
  instances  : (ident, value) Hashtbl.t;
  predicates : (ident, texpr) Hashtbl.t;
  rules      : trule list;
}

type test_result = {
  rname     : string;
  passed    : bool;
  failures  : string list;
  outcomes  : outcome list;
  fired     : string list;
  test_env  : env option;
}

exception Eval_error of string

(* Pretty-printers. The first two are debug-flavored; pp_* drop the
   `tag` / `@instance` prefixes for end-user output. *)
val value_eq     : value -> value -> bool
val show_value   : value -> string
val show_outcome : outcome -> string
val pp_value     : value -> string
val pp_outcome   : outcome -> string
val format_money : float -> string

(* Env helpers — needed by Load to construct an env from JSON. *)
val empty_env : env
val bind      : env -> ident -> value -> env
val lookup    : env -> ident -> value option

(* Typed-expr evaluation. Caller is responsible for binding fields the
   expression references (e.g. via build_env_from_values). *)
val eval : env -> texpr -> value

(* Build a fresh env from already-evaluated raw field bindings + a schema.
   Used by Load to bridge JSON → runtime. *)
val build_env_from_values :
  ?instances:(ident, value) Hashtbl.t ->
  ?predicates:(ident, texpr) Hashtbl.t ->
  tschema -> (ident * value) list -> env

(* Per-program context: schema table, instance table (lazily evaluated),
   and rules sorted by priority. *)
val make_ctx : tprogram -> ctx

(* Run all rules against an env. Returns (rules-that-fired, outcomes). *)
val run_rules : env -> trule list -> string list * outcome list

(* Test runner. *)
val run_all  : ?filter:(string -> bool) -> tprogram ->
               test_result list * trule list
val run_test : ctx -> ttest -> test_result
val report   : ?explain_failures:bool ->
               test_result list * trule list -> bool
