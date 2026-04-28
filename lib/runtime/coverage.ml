(* Branch coverage instrumentation, opt-in via `Coverage.start`.
   Eval observes at every conditional site (if / and / or / not /
   is missing / is present); each site accumulates the set of
   outcome values seen across the whole test run. *)

type branch_state = {
  mutable saw_true    : bool;
  mutable saw_false   : bool;
  mutable saw_missing : bool;
}

let fresh () =
  { saw_true = false; saw_false = false; saw_missing = false }

(* Indexed by source position (file + line + col). The eval module
   records at branch points; the report builder summarises after. *)
type t = (Lexing.position, branch_state) Hashtbl.t

let active : t option ref = ref None

let start () : t =
  let tbl = Hashtbl.create 128 in
  active := Some tbl;
  tbl

let stop () = active := None

(* eval calls this at every conditional site.  `value` is the
   evaluated truth-valued result (or "missing"). *)
let observe (pos : Lexing.position) ~value : unit =
  match !active with
  | None -> ()
  | Some tbl ->
      let state =
        match Hashtbl.find_opt tbl pos with
        | Some s -> s
        | None ->
            let s = fresh () in
            Hashtbl.add tbl pos s;
            s
      in
      (match value with
       | `True    -> state.saw_true <- true
       | `False   -> state.saw_false <- true
       | `Missing -> state.saw_missing <- true)

(* ---------- reporting ---------- *)

type site_status = Full | Partial of string | Uncovered

(* A branch site is "fully covered" when both true and false have
   fired at least once. Missing on top is bonus information but not
   required for "full". A site that's only ever true (or only false)
   is partially covered — the alternate branch is dead per the test
   suite. *)
let classify (s : branch_state) : site_status =
  match s.saw_true, s.saw_false with
  | true, true   -> Full
  | true, false  -> Partial "only true"
  | false, true  -> Partial "only false"
  | false, false ->
      if s.saw_missing then Partial "only missing"
      else Uncovered

type summary = {
  total      : int;
  full       : int;
  partial    : int;
  uncovered  : int;
  sites      : (Lexing.position * site_status * branch_state) list;
}

let summarise (tbl : t) : summary =
  let sites = Hashtbl.fold (fun pos state acc ->
    (pos, classify state, state) :: acc) tbl [] in
  let sites = List.sort (fun (p1, _, _) (p2, _, _) ->
    let f = compare p1.Lexing.pos_fname p2.Lexing.pos_fname in
    if f <> 0 then f
    else if p1.pos_lnum <> p2.pos_lnum
    then compare p1.pos_lnum p2.pos_lnum
    else compare p1.pos_cnum p2.pos_cnum) sites in
  let count f = List.length (List.filter (fun (_, s, _) -> f s) sites) in
  let full      = count (function Full -> true | _ -> false) in
  let partial   = count (function Partial _ -> true | _ -> false) in
  let uncovered = count (function Uncovered -> true | _ -> false) in
  { total = List.length sites; full; partial; uncovered; sites }

let pp_pos (p : Lexing.position) =
  Printf.sprintf "%s:%d:%d"
    (if p.pos_fname = "" then "<input>" else p.pos_fname)
    p.pos_lnum (p.pos_cnum - p.pos_bol + 1)

let pp_state (s : branch_state) =
  let bits = [
    if s.saw_true    then Some "true"    else None;
    if s.saw_false   then Some "false"   else None;
    if s.saw_missing then Some "missing" else None;
  ] |> List.filter_map (fun x -> x) in
  match bits with
  | [] -> "(never reached)"
  | xs -> "{" ^ String.concat ", " xs ^ "}"

let report (sum : summary) : string =
  let buf = Buffer.create 1024 in
  let add fmt = Printf.ksprintf (Buffer.add_string buf) fmt in
  if sum.total = 0 then
    add "(no branch sites instrumented)\n"
  else begin
    let pct n = if sum.total = 0 then 0.0
                else 100.0 *. float_of_int n /. float_of_int sum.total in
    add "Branch coverage\n";
    add "  fully covered:    %d / %d  (%.1f%%)\n" sum.full sum.total (pct sum.full);
    add "  partial:          %d\n" sum.partial;
    add "  uncovered:        %d\n" sum.uncovered;
    if sum.partial > 0 || sum.uncovered > 0 then begin
      add "\nNot fully covered:\n";
      List.iter (fun (pos, status, state) ->
        match status with
        | Full -> ()
        | Uncovered ->
            add "  %s — never reached\n" (pp_pos pos)
        | Partial reason ->
            add "  %s — %s  observed: %s\n"
              (pp_pos pos) reason (pp_state state))
        sum.sites
    end
  end;
  Buffer.contents buf
