(* Structured diagnostic — replaces ad-hoc error-string lists.
   Every analysis stage (parse, resolve, typecheck) emits these; CLI / LSP /
   Web each render them in their own format without re-parsing strings. *)

type stage = Parse | Resolve | Typecheck | Lint

let pp_stage = function
  | Parse     -> "parse"
  | Resolve   -> "resolve"
  | Typecheck -> "typecheck"
  | Lint      -> "lint"

type severity = Error | Warning | Info

let pp_severity = function
  | Error   -> "error"
  | Warning -> "warning"
  | Info    -> "info"

type related = {
  rel_pos : Lexing.position;
  rel_msg : string;
}

type t = {
  stage    : stage;
  severity : severity;
  pos      : Lexing.position;
  end_pos  : Lexing.position;
  code     : string option;
  message  : string;
  related  : related list;
}

let make ?(severity = Error) ?end_pos ?code ?(related = [])
         ~stage ~pos message =
  let end_pos = match end_pos with Some p -> p | None -> pos in
  { stage; severity; pos; end_pos; code; message; related }

let error   ?end_pos ?code ?related ~stage ~pos m =
  make ?end_pos ?code ?related ~severity:Error   ~stage ~pos m
let warning ?end_pos ?code ?related ~stage ~pos m =
  make ?end_pos ?code ?related ~severity:Warning ~stage ~pos m

let pp_pos (p : Lexing.position) =
  Printf.sprintf "line %d, col %d"
    p.pos_lnum (p.pos_cnum - p.pos_bol + 1)

(* Human-readable rendering — matches the previous string format so
   the CLI output is unchanged. *)
let to_string (d : t) =
  if d.pos = Lexing.dummy_pos then
    Printf.sprintf "%s: %s" (pp_stage d.stage) d.message
  else
    Printf.sprintf "%s: %s: %s" (pp_pos d.pos) (pp_stage d.stage) d.message

(* Compatibility shim: convert a positionless error string to a Diagnostic
   pinned at dummy_pos. Used while migrating old code paths. *)
let of_string ~stage message =
  make ~stage ~pos:Lexing.dummy_pos message
