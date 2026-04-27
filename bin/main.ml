(* iDSL CLI:
   idsl <file>                                          parse + dump
   idsl typed <file>                                    dump typed AST
   idsl test <file>                                     run `test` blocks
   idsl run <file> --schema S --input obj.json          run rules → outcomes
   idsl explain <file> --schema S --input obj.json [--json]
                                                         per-rule audit trail
   idsl whatif <file> --schema S --input obj.json
              --set FIELD=VALUE [--set FIELD=VALUE ...]
                                                         counterfactual diff
   idsl diff <file> --schema S --before a.json --after b.json
                                                         compare two inputs *)

let usage () =
  prerr_endline "usage: idsl <file>";
  prerr_endline "       idsl typed <file>";
  prerr_endline "       idsl test <file>";
  prerr_endline "       idsl run <file> --schema S --input obj.json";
  prerr_endline "       idsl explain <file> --schema S --input obj.json [--json]";
  prerr_endline "       idsl whatif <file> --schema S --input obj.json --set F=V ...";
  prerr_endline "       idsl diff <file> --schema S --before a.json --after b.json";
  exit 2

let die_with file diags =
  List.iter (fun d ->
    Printf.eprintf "%s: %s\n" file (IDSL.Diagnostic.to_string d)) diags;
  exit 1

let load file =
  let s = IDSL.Session.compile_file file in
  match s.ast, s.typed with
  | Some prog, Some tp -> prog, tp
  | _ -> die_with file s.diagnostics

let cmd_dump file =
  let prog, _ = load file in
  print_endline (IDSL.Printer.pp_program prog);
  Printf.printf "\n\n(* parsed %d top-level item(s) *)\n" (List.length prog)

let cmd_fmt file =
  let s = IDSL.Session.compile_file file in
  if s.ast = None then die_with file s.diagnostics;
  (* Use the CST tree for byte-perfect output: comments, whitespace,
     and original formatting are all preserved. *)
  print_string (IDSL.Cst.text_of_node s.cst)

let cmd_cst file =
  let s = IDSL.Session.compile_file file in
  if s.ast = None then die_with file s.diagnostics;
  let pos_str (s : Lexing.position) (e : Lexing.position) =
    Printf.sprintf "[%d:%d-%d:%d]"
      s.pos_lnum (s.pos_cnum - s.pos_bol)
      e.pos_lnum (e.pos_cnum - e.pos_bol) in
  let rec dump indent = function
    | IDSL.Cst.GTok t ->
        (match t.kind with
         | Whitespace | Newline -> ()
         | _ ->
             Printf.printf "%s· %s   %S  %s\n"
               (String.make indent ' ')
               (IDSL.Cst.pp_token_kind t.kind) t.text
               (pos_str t.start t.stop))
    | IDSL.Cst.GNode n ->
        let sp, ep = n.nspan in
        Printf.printf "%s%s  %s\n"
          (String.make indent ' ')
          (IDSL.Cst.pp_node_kind n.nkind) (pos_str sp ep);
        List.iter (dump (indent + 2)) n.nchildren
  in
  dump 0 (IDSL.Cst.GNode s.cst)

let cmd_typed file =
  let _, tp = load file in
  print_endline (IDSL.Typed.pp_program tp)

type flag_action =
  | StrOpt  of string option ref
  | Bool    of bool ref
  | Push    of (string -> unit)

let parse_flags spec rest =
  let rec go = function
    | [] -> ()
    | flag :: rest ->
      match List.assoc_opt flag spec, rest with
      | Some (StrOpt r), v :: tl -> r := Some v; go tl
      | Some (Push f),   v :: tl -> f v; go tl
      | Some (Bool r),   tl      -> r := true; go tl
      | _ -> prerr_endline ("unknown arg: " ^ flag); usage ()
  in go rest

let cmd_test file rest =
  let filter = ref None in
  parse_flags [ "--filter", StrOpt filter ] rest;
  let _, tp = load file in
  let pred = match !filter with
    | None -> fun _ -> true
    | Some pat ->
        let re = Str.regexp_string pat in
        fun name ->
          try ignore (Str.search_forward re name 0); true
          with Not_found -> false in
  let results = IDSL.Eval.run_all ~filter:pred tp in
  let ok = IDSL.Eval.report results in
  exit (if ok then 0 else 1)

let load_json path =
  try IDSL.Json.of_file path
  with IDSL.Json.Parse_error msg ->
    prerr_endline (path ^ ": " ^ msg); exit 1

let load_ctx file =
  let _, tp = load file in
  let ctx = IDSL.Eval.make_ctx tp in
  tp, ctx

let env_from_json ctx schema_name j =
  try IDSL.Load.build_env ~instances:ctx.IDSL.Eval.instances
        ctx.IDSL.Eval.schemas schema_name j
  with IDSL.Load.Load_error msg ->
    prerr_endline ("input error: " ^ msg); exit 1

let parse_run_args rest =
  let schema = ref None and input = ref None and json = ref false in
  parse_flags
    [ "--schema", StrOpt schema;
      "--input",  StrOpt input;
      "--json",   Bool json ]
    rest;
  match !schema, !input with
  | Some s, Some i -> s, i, !json
  | _ -> usage ()

let cmd_run file rest =
  let schema_name, input_path, _ = parse_run_args rest in
  let tp, ctx = load_ctx file in
  let env = env_from_json ctx schema_name (load_json input_path) in
  let _fired, outcomes =
    try IDSL.Eval.run_rules env tp.rules
    with IDSL.Eval.Eval_error m ->
      prerr_endline ("eval error: " ^ m); exit 1 in
  print_endline (IDSL.Json.to_string_pretty (IDSL.Dump.outcomes_to_json outcomes))

let cmd_explain file rest =
  let schema_name, input_path, want_json = parse_run_args rest in
  let _, ctx = load_ctx file in
  let env = env_from_json ctx schema_name (load_json input_path) in
  let traces =
    try IDSL.Explain.run ctx env
    with IDSL.Eval.Eval_error m ->
      prerr_endline ("eval error: " ^ m); exit 1 in
  if want_json then
    print_endline (IDSL.Json.to_string_pretty (IDSL.Explain.to_json traces))
  else
    print_endline (IDSL.Explain.pp_report traces)

(* parse "FIELD=VALUE": value is JSON; if not parseable, treat as bare string *)
let parse_set s =
  match String.index_opt s '=' with
  | None -> prerr_endline ("bad --set: " ^ s); usage ()
  | Some i ->
      let k = String.sub s 0 i in
      let v_str = String.sub s (i + 1) (String.length s - i - 1) in
      let v =
        try IDSL.Json.of_string v_str
        with _ -> IDSL.Json.JStr v_str in
      (k, v)

let parse_whatif_args rest =
  let schema = ref None and input = ref None and sets = ref [] in
  parse_flags
    [ "--schema", StrOpt schema;
      "--input",  StrOpt input;
      "--set",    Push (fun s -> sets := parse_set s :: !sets) ]
    rest;
  match !schema, !input with
  | Some s, Some i -> s, i, List.rev !sets
  | _ -> usage ()

let parse_diff_args rest =
  let schema = ref None and before = ref None and after = ref None in
  parse_flags
    [ "--schema", StrOpt schema;
      "--before", StrOpt before;
      "--after",  StrOpt after ]
    rest;
  match !schema, !before, !after with
  | Some s, Some b, Some a -> s, b, a
  | _ -> usage ()

let do_diff file schema_name json_before json_after =
  let _, ctx = load_ctx file in
  let env_b = env_from_json ctx schema_name json_before in
  let env_a = env_from_json ctx schema_name json_after  in
  let traces_b = IDSL.Explain.run ctx env_b in
  let traces_a = IDSL.Explain.run ctx env_a in
  let tsch = Hashtbl.find ctx.schemas schema_name in
  let d = IDSL.Whatif.compute tsch env_b env_a traces_b traces_a in
  print_endline (IDSL.Whatif.pp_diff d)

let cmd_whatif file rest =
  let schema_name, input_path, sets = parse_whatif_args rest in
  let base = load_json input_path in
  let after = List.fold_left (fun j (k, v) -> IDSL.Json.set_field j k v) base sets in
  do_diff file schema_name base after

let cmd_diff file rest =
  let schema_name, before_path, after_path = parse_diff_args rest in
  do_diff file schema_name (load_json before_path) (load_json after_path)

let () =
  match Array.to_list Sys.argv with
  | _ :: "test"    :: file :: rest -> cmd_test  file rest
  | _ :: "typed"   :: file :: _    -> cmd_typed file
  | _ :: "fmt"     :: file :: _    -> cmd_fmt   file
  | _ :: "cst"     :: file :: _    -> cmd_cst   file
  | _ :: "run"     :: file :: rest -> cmd_run     file rest
  | _ :: "explain" :: file :: rest -> cmd_explain file rest
  | _ :: "whatif"  :: file :: rest -> cmd_whatif  file rest
  | _ :: "diff"    :: file :: rest -> cmd_diff    file rest
  | _ :: file :: _                 -> cmd_dump file
  | _                              -> usage ()
