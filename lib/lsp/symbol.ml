(* Stable identity for the things you can hover, jump to, or rename.

   The kind variant *is* the identity — two symbols are equal iff their
   kinds compare equal. The decl_pos is just where the declaration sits
   in source; it is not part of the identity. This means we can refer to
   "the schema named Contract" without already knowing its position. *)

type ident = string

type kind =
  | KSchema   of ident                    (* schema Contract *)
  | KField    of ident * ident            (* schema.field *)
  | KRule     of ident list               (* rule path, e.g. ["budget";"high"] *)
  | KTest     of string                   (* test "name" *)
  | KInstance of ident                    (* instance ID — globally unique *)
  | KAction   of ident                    (* @action name *)

type t = {
  kind     : kind;
  decl_pos : Lexing.position;
  label    : string;            (* short human-readable summary for hover *)
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
