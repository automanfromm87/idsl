(* Stable identity for the things you can hover, jump to, or rename.

   The kind variant *is* the identity — two symbols are equal iff their
   kinds compare equal. Kinds carry the *canonical qualified* name
   ("shipping.Item" inside `domain shipping:`, just "Item" at the top
   level). The qualified form is what lets two same-bare-name decls in
   different domains coexist as distinct symbols.

   `decl_name` is the *bare* identifier — what the user typed at the
   declaration site. Range / span computations (LSP selectionRange,
   text-edit length, decl_length) must use this; using the qualified
   string would overshoot the source token.

   `decl_pos` is just where the declaration sits in source; it is not
   part of the identity. This means we can refer to "the schema named
   shipping.Item" without already knowing its position. *)

type ident = string

type kind =
  | KSchema   of ident                    (* canonical key; e.g. "shipping.Item" *)
  | KField    of ident * ident            (* (canonical schema key, bare field) *)
  | KRule     of ident list               (* rule path; first segment is the
                                             domain when the rule is scoped *)
  | KTest     of string                   (* canonical: "domain.<test name>" *)
  | KInstance of ident                    (* canonical instance key *)
  | KAction   of ident                    (* canonical @action key *)
  | KPredicate of ident                   (* canonical predicate key *)

type t = {
  kind      : kind;
  decl_pos  : Lexing.position;
  decl_name : string;           (* bare token text at the source declaration *)
  label     : string;           (* short human-readable summary for hover *)
}

let equal_kind a b = a = b
let equal a b = equal_kind a.kind b.kind

(* Display labels used in def_at / hover. *)
let label_of_kind = function
  | KSchema s         -> "schema " ^ s
  | KField (s, f)     -> Printf.sprintf "field %s.%s" s f
  | KRule path        -> "rule "   ^ String.concat "." path
  | KTest n           -> Printf.sprintf "test %S" n
  | KInstance n       -> "instance " ^ n
  | KAction n         -> "@action " ^ n
  | KPredicate n      -> "predicate " ^ n
