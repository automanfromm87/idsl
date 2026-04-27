(* Static type lattice for the typechecker. *)

type ty =
  | TInt | TFloat | TMoney
  | TBool | TString | TDate
  | TDuration                  (* result of Date - Date *)
  | TTag    of string
  | TEnum   of string list
  | TList   of ty
  | TSchema of string
  | TObject of (string * ty) list
  | TMissing
  | TAny

let rec pp_ty = function
  | TInt      -> "Int"
  | TFloat    -> "Float"
  | TMoney    -> "Money"
  | TBool     -> "Bool"
  | TString   -> "String"
  | TDate     -> "Date"
  | TDuration -> "Duration"
  | TTag t    -> "`" ^ t
  | TEnum xs  -> "{" ^ String.concat "|" xs ^ "}"
  | TList t   -> "[" ^ pp_ty t ^ "]"
  | TSchema s -> s
  | TObject kvs ->
      "{" ^ String.concat ", "
              (List.map (fun (k, t) -> k ^ ": " ^ pp_ty t) kvs) ^ "}"
  | TMissing  -> "Missing"
  | TAny      -> "?"

let is_numeric = function
  | TInt | TFloat | TMoney -> true
  | _ -> false

let is_ordered = function
  | TInt | TFloat | TMoney | TDate | TString -> true
  | _ -> false

(* Combine two types into the most specific type that fits both, or fail.
   Rules:
   - TAny is the bottom: unifies with anything to the other side.
   - TMissing unifies with anything (treat as polymorphic absence).
   - TTag x  ⊔ TEnum xs  → TEnum xs  iff x ∈ xs.
   - TInt    ⊔ TFloat    → TFloat (numeric widening).
   - TList a ⊔ TList b   → TList (a ⊔ b).
   - TSchema s ⊔ TObject kvs → TSchema s iff every (k, t) in kvs matches the
     schema's field type (handled in typecheck, not here).
   - Otherwise must be structurally equal. *)
exception Type_error of string
let err fmt = Printf.ksprintf (fun s -> raise (Type_error s)) fmt

let rec unify a b =
  match a, b with
  | TAny, t | t, TAny           -> t
  | TMissing, t | t, TMissing   -> t
  | TTag x, TEnum xs | TEnum xs, TTag x ->
      if List.mem x xs then TEnum xs
      else err "tag `%s` not in {%s}" x (String.concat "|" xs)
  | TTag x, TTag y when x = y   -> TTag x
  | TInt, TFloat | TFloat, TInt -> TFloat
  | TList a, TList b            -> TList (unify a b)
  | TEnum xs, TEnum ys when xs = ys -> TEnum xs
  | _ when a = b                -> a
  | _ -> err "type mismatch: %s vs %s" (pp_ty a) (pp_ty b)

(* Result type of arithmetic between two numeric operands. Money dominates,
   then Float, then Int. *)
let arith_result a b =
  match a, b with
  | TMissing, _ | _, TMissing -> TMissing
  | TMoney, _ | _, TMoney     -> TMoney
  | TFloat, _ | _, TFloat     -> TFloat
  | TInt,   TInt              -> TInt
  | _ -> err "arith on non-numeric: %s, %s" (pp_ty a) (pp_ty b)
