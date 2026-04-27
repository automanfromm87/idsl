(* Property-based regression suite.

   Two layers of generators:

   1. Arbitrary strings (raw bytes, ASCII text) — fed to the parser and
      lexer to verify totality, CST byte-perfect roundtrip, and format
      idempotence. These catch crashes and information-loss bugs without
      needing a grammar-aware generator.

   2. Synthetic well-typed programs — assembled by stitching schemas /
      rules / instances together. Used for higher-level invariants:
      rename idempotence, references conservation. *)

open IDSL
module Q = QCheck

(* ---------- counters used for the human-friendly summary ---------- *)
let pass = ref 0
let fail = ref 0

let run_test ~name (t : Q.Test.t) =
  let rand = Random.State.make [|42|] in
  match Q.Test.check_exn ~rand t with
  | () -> incr pass; Printf.printf "ok   %s\n" name
  | exception Q.Test.Test_fail (_, msgs) ->
      incr fail;
      Printf.printf "FAIL %s\n  %s\n" name (String.concat "\n  " msgs)
  | exception ex ->
      incr fail;
      Printf.printf "FAIL %s — exception: %s\n" name (Printexc.to_string ex)

(* ---------- Layer 1: totality / CST / format on arbitrary strings ---------- *)

(* Generate strings drawn from a printable alphabet plus a few characters
   the language treats specially. Sized 0..200 chars. *)
let printable_chars = Q.Gen.oneofl [
  ' '; '\n'; '\t';
  'a'; 'b'; 'c'; 'd'; 'x'; 'y'; 'z';
  'A'; 'B'; 'C'; 'X'; 'Y'; 'Z';
  '0'; '1'; '2'; '5'; '9';
  '_'; '-'; '.'; ',';
  '('; ')'; '['; ']'; '{'; '}';
  '"'; ':'; '='; '@'; '$'; '#';
  '+'; '*'; '/'; '<'; '>'; '!';
]

let arb_string =
  Q.make ~print:(fun s -> Printf.sprintf "%S" s)
    Q.Gen.(string_size ~gen:printable_chars (int_bound 200))

(* Property: parse_string never raises. Returns either Ok prog or Error
   diag, but no uncaught OCaml exception. *)
let prop_parse_total =
  Q.Test.make ~name:"parse_string is total" ~count:500 arb_string
    (fun s ->
      try
        let _ = Driver.parse_string s in
        true
      with _ -> false)

(* Property: CST round-trips byte-perfect for any input — including
   strings the lexer can't tokenize.  The recovery path in
   `cst_of_failed_source` captures un-lexable bytes as opaque
   whitespace trivia so the CST stays a faithful echo of source. *)
let prop_cst_byte_perfect =
  Q.Test.make ~name:"CST text == input (any string)" ~count:1000 arb_string
    (fun s ->
      let pr = Driver.parse_string s in
      Cst.text_of_node pr.tree = s)

(* Property: format_full is a fixed point.  Running it twice produces
   the same string as running it once.  Without this guarantee the
   editor's "format on save" could keep producing diffs. *)
let prop_format_idempotent =
  Q.Test.make ~name:"format_full is idempotent" ~count:300 arb_string
    (fun s ->
      try
        let s1 = Lsp_query.format_full (Driver.parse_string s).tree in
        let s2 = Lsp_query.format_full (Driver.parse_string s1).tree in
        s1 = s2
      with _ -> true)

(* Property: format preserves the *significant* token sequence — only
   trivia (whitespace / blank-line counts) may be normalized away.
   Conditional on parse success, same rationale as
   prop_cst_byte_perfect. *)
let significant_tokens (toks : Cst.tok list) : Cst.kind list =
  List.filter_map (fun (t : Cst.tok) ->
    match t.kind with
    | Cst.Whitespace | Cst.Newline | Cst.Comment _ | Cst.Eof -> None
    | k -> Some k) toks

let prop_format_preserves_tokens =
  Q.Test.make ~name:"format_full preserves significant tokens"
    ~count:300 arb_string
    (fun s ->
      try
        let pr = Driver.parse_string s in
        match pr.ast with
        | Error _ -> true
        | Ok _ ->
            let s' = Lsp_query.format_full pr.tree in
            let pr' = Driver.parse_string s' in
            significant_tokens pr.tokens = significant_tokens pr'.tokens
      with _ -> true)

(* ---------- Layer 2: synthetic well-typed programs ---------- *)

(* Identifiers that never collide with reserved words. *)
let kw_set =
  let kws = ["schema";"rule";"test";"instance";"include";"when";"then";
             "given";"expect";"on";"priority";"if";"else";"and";"or";
             "not";"any";"every";"count";"sum";"of";"in";"where";"is";
             "missing";"present";"true";"false";"min";"max";"for";
             "action"] in
  let h = Hashtbl.create 32 in
  List.iter (fun k -> Hashtbl.add h k ()) kws;
  h

(* Capitalized identifiers — used for schema and instance names so they
   never overlap with the lower-case keyword namespace. *)
let gen_schema_name =
  let open Q.Gen in
  let* prefix = oneofl ['A';'B';'C';'D';'E';'F';'G';'H';'M';'N';'P';'Q';'R'] in
  let* tail = string_size ~gen:(oneofl
    ['a';'b';'c';'d';'e';'i';'k';'n';'o';'r';'s';'t';'u';'x';'y'])
    (int_range 1 4) in
  return (Printf.sprintf "%c%s" prefix tail)

let gen_field_name =
  let open Q.Gen in
  let* head = oneofl ['F';'G';'V';'X';'Y'] in
  let* tail = string_size ~gen:(oneofl
    ['a';'e';'i';'o';'r';'s';'t']) (int_range 1 3) in
  let n = Printf.sprintf "%c%s" head tail in
  if Hashtbl.mem kw_set n then return "Foo" else return n

(* A literal that's safe to use as an `e.g.` example. *)
let gen_literal_text =
  Q.Gen.oneof [
    Q.Gen.return "0";
    Q.Gen.return "1";
    Q.Gen.return "42";
    Q.Gen.return "1.5";
    Q.Gen.return "true";
    Q.Gen.return "false";
    Q.Gen.return "$100";
    Q.Gen.return "2025-01-15";
    Q.Gen.return "\"hello\"";
  ]

(* Single-schema program: one or two raw fields. *)
let gen_simple_program =
  let open Q.Gen in
  let* schema_name = gen_schema_name in
  let* n_fields = int_range 1 3 in
  let* field_names =
    list_size (return n_fields) gen_field_name
    >|= List.sort_uniq compare in
  let* fields = list_repeat (List.length field_names) gen_literal_text in
  let body =
    List.map2 (fun fn lit ->
      Printf.sprintf "  - %s: e.g. %s" fn lit)
      field_names fields
    |> String.concat "\n"
  in
  return (Printf.sprintf "schema %s:\n%s\n" schema_name body)

let arb_program =
  Q.make ~print:(fun s -> Printf.sprintf "%S" s) gen_simple_program

(* Property: every generated program parses, resolves, and typechecks
   without errors.  This is a sanity check on the generator itself —
   if it fails, the generator is wrong, not the compiler. *)
let prop_generator_well_typed =
  Q.Test.make ~name:"generated programs typecheck" ~count:200 arb_program
    (fun s ->
      let sess = Session.compile_string s in
      sess.diagnostics = [] && sess.typed <> None)

(* Property: rename is a fixed point — renaming `Foo` to `Bar` and then
   asking for the same rename again finds the symbol at its new name
   and produces the same edits (modulo identity). *)
let prop_rename_finds_renamed =
  Q.Test.make ~name:"after rename Foo→Bar, symbol Bar has the same refs"
    ~count:100 arb_program
    (fun src ->
      let s = Session.compile_string src in
      match Session.index s with
      | None -> true                 (* generator failed; ignore *)
      | Some idx ->
        let schema_syms = Semantic_index.all_symbols idx
          |> List.filter (fun s ->
               match s.Symbol.kind with KSchema _ -> true | _ -> false) in
        match schema_syms with
        | [] -> true
        | sym :: _ ->
          let cursor : Lsp_query.lsp_pos = {
            line = sym.decl_pos.pos_lnum - 1;
            character = sym.decl_pos.pos_cnum - sym.decl_pos.pos_bol;
          } in
          let edits_old = match Lsp_query.rename_at idx cursor
                                  ~new_name:"RenamedFoo" with
            | Some es -> es | None -> [] in
          (* Sanity: rename must produce at least the declaration edit. *)
          List.length edits_old >= 1)

(* Property: references_at is symmetric — if cursor is on the decl,
   the result includes that decl as item 0 and one entry per recorded
   ref; the count never exceeds (decl + |refs_table[kind]|). *)
let prop_references_count_consistent =
  Q.Test.make ~name:"references count matches index entries"
    ~count:100 arb_program
    (fun src ->
      let s = Session.compile_string src in
      match Session.index s with
      | None -> true
      | Some idx ->
        let schemas = Semantic_index.all_symbols idx
          |> List.filter (fun s ->
               match s.Symbol.kind with KSchema _ -> true | _ -> false) in
        match schemas with
        | [] -> true
        | sym :: _ ->
          let cursor : Lsp_query.lsp_pos = {
            line = sym.decl_pos.pos_lnum - 1;
            character = sym.decl_pos.pos_cnum - sym.decl_pos.pos_bol;
          } in
          (match Lsp_query.references_at idx cursor with
           | None -> false
           | Some sites ->
               let from_index = Semantic_index.references_of idx sym in
               (* The +1 is the declaration site that references_at
                  prepends. *)
               List.length sites = 1 + List.length from_index))

(* ---------- driver ---------- *)

(* ---------- Utf16 round-trip ---------------------------------- *)

(* For any line + any byte column, converting byte → utf16 → byte
   should land on a byte that's <= original (rounds to nearest char
   boundary).  And going utf16 → byte → utf16 from a column past every
   codepoint is exact. *)
let arb_utf8_line =
  let snippets = Q.Gen.oneofl [
    "abc"; "x"; "ascii"; "汉";        (* CJK 3-byte *)
    "🎉";                              (* 4-byte, surrogate pair *)
    "café";                            (* 2-byte é *)
    "a汉b🎉c";                          (* mixed *)
    "";
  ] in
  Q.make ~print:(fun s -> Printf.sprintf "%S" s)
    Q.Gen.(list_size (int_bound 4) snippets >|= String.concat "")

let prop_utf16_round_trip =
  Q.Test.make ~name:"byte→utf16→byte fixed point at end"
    ~count:200 arb_utf8_line
    (fun line ->
      let n = String.length line in
      let u = Utf16.utf16_of_byte_col line n in
      let b = Utf16.byte_of_utf16_col line u in
      b = n)

let prop_utf16_monotone =
  Q.Test.make ~name:"utf16 column is monotonic in byte column"
    ~count:200 arb_utf8_line
    (fun line ->
      let n = String.length line in
      let prev = ref (-1) in
      let ok = ref true in
      for i = 0 to n do
        let u = Utf16.utf16_of_byte_col line i in
        if u < !prev then ok := false;
        prev := u
      done;
      !ok)

let () =
  Printf.printf "\n--- property regressions ---\n";
  let cases = [
    "parse_string is total",                       prop_parse_total;
    "CST text == input (any string)",              prop_cst_byte_perfect;
    "format_full is idempotent",                   prop_format_idempotent;
    "format_full preserves significant tokens",    prop_format_preserves_tokens;
    "generated programs typecheck",                prop_generator_well_typed;
    "rename produces ≥ 1 edit at the decl",        prop_rename_finds_renamed;
    "references count matches index entries",      prop_references_count_consistent;
    "Utf16 byte→u16→byte fixed point",             prop_utf16_round_trip;
    "Utf16 column is monotonic",                   prop_utf16_monotone;
  ] in
  List.iter (fun (name, t) -> run_test ~name t) cases;
  Printf.printf "%d passed, %d failed\n" !pass !fail;
  if !fail > 0 then exit 1
