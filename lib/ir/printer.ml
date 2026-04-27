open Ast

let pp_lit = function
  | LInt i    -> string_of_int i
  | LFloat f  -> Printf.sprintf "%g" f
  | LString s -> Printf.sprintf "%S" s
  | LBool b   -> string_of_bool b
  | LMoney m  -> m
  | LDate d   -> d

let pp_binop = function
  | And -> "and" | Or -> "or"
  | Eq  -> "=="  | Neq -> "!="
  | Lt  -> "<"   | Gt  -> ">"  | Leq -> "<=" | Geq -> ">="
  | Add -> "+"   | Sub -> "-"  | Mul -> "*"  | Div -> "/"

let pp_unop = function Not -> "not" | Neg -> "-"

let rec pp_expr e =
  match e.e_node with
  | EVar x          -> x
  | EField (e, _, f) -> pp_expr e ^ "." ^ f
  | ELit l          -> pp_lit l
  | EList es        -> "[" ^ String.concat ", " (List.map pp_expr es) ^ "]"
  | EObject kvs     ->
      "{" ^ String.concat ", "
              (List.map (fun (k, v) -> k ^ ": " ^ pp_expr v) kvs) ^ "}"
  | EWildcard       -> "_"
  | EMissing        -> "missing"
  | EUnary (op, e)  -> Printf.sprintf "(%s %s)" (pp_unop op) (pp_expr e)
  | EBin (op, a, b) ->
      Printf.sprintf "(%s %s %s)" (pp_expr a) (pp_binop op) (pp_expr b)
  | EIf (c, t, e)   ->
      Printf.sprintf "(if %s then %s else %s)" (pp_expr c) (pp_expr t) (pp_expr e)
  | EAny   (x, y, p) -> Printf.sprintf "(any %s in %s: %s)"   x y (pp_expr p)
  | EEvery (x, y, p) -> Printf.sprintf "(every %s in %s: %s)" x y (pp_expr p)
  | ECount (x, y, p) -> Printf.sprintf "(count of %s in %s where %s)" x y (pp_expr p)
  | ESum (f, x, y, p) ->
      Printf.sprintf "(sum of %s for %s in %s where %s)"
        (pp_expr f) x y (pp_expr p)
  | EIsMissing e    -> Printf.sprintf "(%s is missing)" (pp_expr e)
  | EIsPresent e    -> Printf.sprintf "(%s is present)" (pp_expr e)
  | ECall (f, args) ->
      Printf.sprintf "%s(%s)" f (String.concat ", " (List.map pp_expr args))

let pp_example = function
  | ExLit l   -> pp_lit l
  | ExEnum xs -> String.concat ", " xs
  | ExList es -> "[" ^ String.concat ", " (List.map pp_expr es) ^ "]"

let pp_field = function
  | FRaw (_, n, ex)    -> Printf.sprintf "  - %s: e.g. %s" n (pp_example ex)
  | FDerived (_, n, e) -> Printf.sprintf "  - %s: i.e. %s" n (pp_expr e)

let indent_lines prefix xs =
  String.concat "\n" (List.map (fun s -> prefix ^ s) xs)

let rec pp_ty_annot = function
  | AnnScalar s -> s
  | AnnEnum xs  -> "{" ^ String.concat "|" xs ^ "}"
  | AnnList t   -> "[" ^ pp_ty_annot t ^ "]"
  | AnnSchema s -> s

let pp_top = function
  | TMeta { mkey; mvalue } ->
      Printf.sprintf "@%s(%S)" mkey mvalue
  | TAction { asname; asparams; aspos = _ } ->
      let ps = String.concat ", "
        (List.map (fun p ->
           Printf.sprintf "%s: %s" p.pname (pp_ty_annot p.ptype))
           asparams) in
      Printf.sprintf "@action %s(%s)" asname ps
  | TInclude { inc_path; inc_pos = _ } ->
      Printf.sprintf "include %S" inc_path
  | TInstance { iname; ischema; ivalues; _ } ->
      let body = String.concat "\n"
        (List.map (fun a ->
           Printf.sprintf "  %s = %s" a.aname (pp_expr a.avalue)) ivalues) in
      Printf.sprintf "instance %s %s:\n%s" ischema iname body
  | TSchema { sname; sfields; spos = _ } ->
      Printf.sprintf "schema %s:\n%s"
        sname (String.concat "\n" (List.map pp_field sfields))
  | TTest { tname; tgiven; texpect; tpos = _ } ->
      let givens = indent_lines "    "
        (List.map (fun a ->
          Printf.sprintf "%s = %s" a.aname (pp_expr a.avalue)) tgiven.gvalues) in
      let expects = indent_lines "    "
        (List.map (function
          | Must (_, e)    -> pp_expr e
          | MustNot (_, e) -> "not " ^ pp_expr e) texpect) in
      Printf.sprintf "test %S:\n  given %s:\n%s\n  expect:\n%s"
        tname tgiven.gschema givens expects
  | TRule { rpath; rdesc; rwhen; rthen; rschema; rpriority; _ } ->
      let name = String.concat "." rpath in
      let on   = match rschema with Some s -> " on " ^ s | None -> "" in
      let prio = if rpriority = 0 then ""
                 else Printf.sprintf " priority %d" rpriority in
      let preds = indent_lines "    " (List.map (fun (_, e) -> pp_expr e) rwhen) in
      let acts  = indent_lines "    " (List.map (fun (_, e) -> pp_expr e) rthen) in
      let desc  = match rdesc with
        | None   -> ""
        | Some s -> Printf.sprintf "  \"\"\"%s\"\"\"\n" s in
      Printf.sprintf "rule %s%s%s:\n%s  when:\n%s\n  then:\n%s"
        name on prio desc preds acts

let pp_program p = String.concat "\n\n" (List.map pp_top p)
