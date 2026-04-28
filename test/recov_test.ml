let () =
  let s = {|schema A:
  - X: default 1

schema B:
  - Y: !!! broken !!!

schema C:
  - Z: default 2
|} in
  let prog, errs = IDSL.Driver.parse_with_recovery s in
  Printf.printf "Parsed %d top-level item(s):\n" (List.length prog);
  List.iter (fun item ->
    match item with
    | IDSL.Ast.TSchema s -> Printf.printf "  schema %s\n" s.sname
    | _ -> ()) prog;
  Printf.printf "Error chunks: %d\n" (List.length errs);
  List.iter (fun (line, d) ->
    Printf.printf "  [line %d] %s\n" line d.IDSL.Diagnostic.message) errs
