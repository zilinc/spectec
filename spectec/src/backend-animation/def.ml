open Il.Ast
open Util.Source
open Il.Print

type type_def' = id * param list * inst list
type type_def = type_def' phrase


type partial = Partial | Total
type func_clause = id option * clause
type func_def' = id * id option * param list * typ * func_clause list * partial option
type func_def = func_def' phrase

type dl_def =
  | TypeDef of type_def
  | FuncDef of func_def
  | RecDef  of dl_def list  (* recursive definitions *)

let string_of_funcname id osubid =
  match osubid with
  | Some subid -> if String.starts_with ~prefix:"/" subid.it || String.starts_with ~prefix:"-" subid.it then
                    raise (Failure ("Function subid must not start with `/` or `-`,\
                                     but got `" ^ subid.it ^ "` in function `" ^ id.it ^ "`."))
                  else
                    id.it ^ "/" ^ subid.it
  | None       -> id.it


let rec find_dl_type_def name dl : type_def option =
  List.find_map (function
    | TypeDef def -> let (id, _, _) = def.it in
                     if id.it = name then Some def else None
    | RecDef dl'  -> find_dl_type_def name dl'
    | _           -> None
  ) dl

let rec find_dl_func_def name dl : func_def option =
  List.find_map (function
    | FuncDef def -> let (id, osubid, _, _, _, _) = def.it in
                     let fid = string_of_funcname id osubid $> id in
                     if fid.it = name then Some def else None
    | RecDef dl'  -> find_dl_func_def name dl'
    | _           -> None
  ) dl

let rec dl_loc def : region = match def with
  | TypeDef tdef -> tdef.at
  | FuncDef fdef -> fdef.at
  | RecDef  defs -> begin match defs with
    | [] -> no_region
    | _  -> over_region (List.map dl_loc defs)
    end

let concat = String.concat
let prefix s f x = s ^ f x


let string_of_type_def td =
  let id, ps, insts = td.it in
  let blob = List.map (fun inst -> (id, inst)) insts in
  "syntax " ^ string_of_id id ^ string_of_params ps ^ " where\n" ^
  String.concat "\n" (List.map (fun (id, {it = InstD (qs, as_, dt); _}) ->
  "syntax " ^ string_of_id id ^ string_of_quants qs ^ string_of_args as_ ^ " = " ^
    string_of_deftyp ~layout:`V dt) blob) ^ "\n"


let string_of_rule_clause rc =
  let id, qs, e1, e2, prems = rc.it in
  Printf.sprintf "%s%s: %s ~> %s%s"
    (Il.Print.string_of_id     id)
    (Il.Print.string_of_quants qs)
    (Il.Print.string_of_exp    e1)
    (Il.Print.string_of_exp    e2)
    (concat "" (List.map (prefix "\n    -- " Il.Print.string_of_prem) prems))

let string_of_rule_def rd =
  let instr_name, rel_id, _t1, _t2, rcs = rd.it in
  instr_name ^ "/" ^ rel_id.it ^ "\n" ^
  (concat "\n" (List.map string_of_rule_clause rcs))

let region_comment ?(suppress_pos = false) omsg indent at =
  if at = no_region then "" else
  let s1 = indent ^ ";; " ^ (if suppress_pos then at.left.file else string_of_region at) ^ "\n" in
  let s2 = match omsg with None -> "" | Some msg -> (indent ^ ";; " ^ msg ^ "\n") in
  s1 ^ s2

let string_of_func_clause fid (fc: func_clause) =
  let oid, { it = DefD (qs, as_, e, prems); at; _ } = fc in
    "\n" ^ region_comment (Option.map (fun id -> "Derived from rule " ^ id.it) oid) "  " at ^
    "  def $" ^ string_of_id fid ^ string_of_quants qs ^ string_of_args as_ ^ " = " ^
      string_of_exp e ^
      concat "" (List.map (prefix "\n    -- " string_of_prem) prems)

let string_of_func_def fd =
  let id, osubid, params, typ, fcs, opartial = fd.it in
  let partial = match opartial with
  | None         -> "partial?"
  | Some Partial -> "partial"
  | Some Total   -> "total"
  in
  let fid = string_of_funcname id osubid $> id in
  string_of_id fid ^ string_of_params params ^ " : " ^ string_of_typ typ ^ " [" ^ partial ^ "]\n" ^
  (concat "\n" (List.map (string_of_func_clause fid) fcs)) ^ "\n"


let rec string_of_dl_def = function
| TypeDef tdef -> string_of_type_def tdef
| FuncDef fdef -> string_of_func_def fdef
| RecDef dl_defs -> "recursive\n" ^ String.concat "\n" (List.map string_of_dl_def dl_defs) ^ "end\n"

let string_of_dl_script dl =
  String.concat "\n" (List.map string_of_dl_def dl)
