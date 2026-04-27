(* UTF-16 ↔ byte offset conversion at the LSP wire boundary.

   The LSP spec defines `Position.character` as a UTF-16 code unit
   offset from the start of the line, but OCaml's `Lexing.position`
   tracks byte offsets.  Treating one as the other works only for
   ASCII; emoji / CJK / 4-byte UTF-8 codepoints all desync the editor's
   range and the server's internal span.

   These converters operate on a single line at a time — the caller
   is responsible for slicing.  Decoding is forgiving: malformed UTF-8
   counts each bad byte as one code unit so we never throw on user
   input.  Both functions are O(line length). *)

(* Width in UTF-16 code units of the codepoint that *starts* at
   `line.[i]` — 1 for BMP, 2 for codepoints > 0xFFFF (surrogate pair). *)
let utf16_width_of_byte (line : string) (i : int) : int =
  if i >= String.length line then 0
  else
    let b = Char.code line.[i] in
    if b < 0x80 then 1               (* ASCII *)
    else if b < 0xc0 then 1          (* lone continuation; skip-1 fallback *)
    else if b < 0xe0 then 1          (* 2-byte UTF-8 → 1 UTF-16 unit *)
    else if b < 0xf0 then 1          (* 3-byte UTF-8 → 1 UTF-16 unit *)
    else 2                           (* 4-byte UTF-8 → surrogate pair *)

(* Byte advance given the UTF-8 lead byte. *)
let utf8_byte_step (b : int) : int =
  if b < 0x80 then 1
  else if b < 0xc0 then 1            (* malformed; advance 1 *)
  else if b < 0xe0 then 2
  else if b < 0xf0 then 3
  else 4

(* Convert a byte column within `line` to a UTF-16 column. *)
let utf16_of_byte_col (line : string) (byte_col : int) : int =
  let n = String.length line in
  let target = if byte_col > n then n else byte_col in
  let i  = ref 0 in
  let u  = ref 0 in
  while !i < target do
    let b = Char.code line.[!i] in
    u := !u + utf16_width_of_byte line !i;
    i := !i + utf8_byte_step b
  done;
  !u

(* Inverse: convert a UTF-16 column to a byte column.  Stops at the
   first position whose accumulated UTF-16 width is ≥ target — so an
   editor pointing at the second half of a surrogate pair lands on the
   start of the surrogate, which matches client-side rendering. *)
let byte_of_utf16_col (line : string) (utf16_col : int) : int =
  let n = String.length line in
  let i = ref 0 in
  let u = ref 0 in
  while !u < utf16_col && !i < n do
    let b = Char.code line.[!i] in
    u := !u + utf16_width_of_byte line !i;
    i := !i + utf8_byte_step b
  done;
  !i

(* ---------- whole-source helpers --------------------------------- *)

(* Pick out the substring of `src` that holds line `line_idx`
   (0-indexed, exclusive of the trailing newline).  Returns "" for
   out-of-range indices so the converters degrade gracefully. *)
let line_of_source (src : string) (line_idx : int) : string =
  let n = String.length src in
  let rec find_start k pos =
    if k = 0 || pos >= n then pos
    else if src.[pos] = '\n' then find_start (k - 1) (pos + 1)
    else find_start k (pos + 1)
  in
  let start = find_start line_idx 0 in
  if start >= n then ""
  else
    let stop = try String.index_from src start '\n'
               with Not_found -> n in
    String.sub src start (stop - start)

(* Convert the byte column of a `Lexing.position` to UTF-16 coords for
   the LSP wire.  Falls back to the byte column when `src` is empty
   (e.g. file not open in workspace). *)
let utf16_col_of_lex ~src (p : Lexing.position) : int =
  let byte_col = p.pos_cnum - p.pos_bol in
  if src = "" then byte_col
  else
    let line = line_of_source src (p.pos_lnum - 1) in
    utf16_of_byte_col line byte_col

(* Convert an LSP UTF-16 (line, character) into a byte column for use
   with internal byte-indexed APIs. *)
let byte_col_of_utf16 ~src ~line (utf16_col : int) : int =
  if src = "" then utf16_col
  else byte_of_utf16_col (line_of_source src line) utf16_col
