open Il.Ast
open Util.Source
open Il.Print

type type_def' = id * param list * inst list
type type_def = type_def' phrase

(* NOTE: [rule_name] is not the same as [rule_id].
   The former is the part of the [rule_id] before the
   first "-".
*)
type rule_clause' = id * bind list * exp * exp * (prem list)  (* rule_id *)
type rule_clause = rule_clause' phrase
type rule_def' = string * id * typ * typ * rule_clause list  (* rule_name, rel_id *)
type rule_def = rule_def' phrase

type partial = Partial | Total
type func_clause = clause
type func_def' = id * param list * typ * func_clause list * partial option
type func_def = func_def' phrase

type dl_def =
  | TypeDef of type_def
  | RuleDef of rule_def  (* only input to animation *)
  | FuncDef of func_def
  | RecDef  of dl_def list  (* recursive definitions *)


let rec find_dl_type_def name dl : type_def option =
  List.find_map (function
    | TypeDef def -> let (id, _, _) = def.it in
                     if id.it = name then Some def else None
    | RecDef dl'  -> find_dl_type_def name dl'
    | _           -> None
  ) dl

let rec find_dl_func_def name dl : func_def option =
  List.find_map (function
    | FuncDef def -> let (id, _, _, _, _) = def.it in
                     if id.it = name then Some def else None
    | RecDef dl'  -> find_dl_func_def name dl'
    | _           -> None
  ) dl

let rec dl_loc def : region = match def with
  | TypeDef tdef -> tdef.at
  | RuleDef rdef -> rdef.at
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
  String.concat "\n" (List.map (fun (id, {it = InstD (bs, as_, dt); _}) ->
  "syntax " ^ string_of_id id ^ string_of_binds bs ^ string_of_args as_ ^ " = " ^
    string_of_deftyp `V dt) blob) ^ "\n"


let string_of_rule_clause rc =
  let id, bs, e1, e2, prems = rc.it in
  Printf.sprintf "%s%s: %s ~> %s%s"
    (Il.Print.string_of_id    id)
    (Il.Print.string_of_binds bs)
    (Il.Print.string_of_exp   e1)
    (Il.Print.string_of_exp   e2)
    (concat "" (List.map (prefix "\n    -- " Il.Print.string_of_prem) prems))

let string_of_rule_def rd =
  let instr_name, rel_id, _t1, _t2, rcs = rd.it in
  instr_name ^ "/" ^ rel_id.it ^ "\n" ^
  (concat "\n" (List.map string_of_rule_clause rcs))

let string_of_func_def fd =
  let id, params, typ, fcs, opartial = fd.it in
  let partial = match opartial with
  | None         -> "partial?"
  | Some Partial -> "partial"
  | Some Total   -> "total"
  in
  id.it ^ string_of_params params ^ " : " ^ string_of_typ typ ^ " [" ^ partial ^ "]\n" ^
  (concat "\n" (List.map (Il.Print.string_of_clause id) fcs)) ^ "\n"


let rec string_of_dl_def = function
| TypeDef tdef -> string_of_type_def tdef
| RuleDef rdef -> string_of_rule_def rdef
| FuncDef fdef -> string_of_func_def fdef
| RecDef dl_defs -> "recursive\n" ^ String.concat "\n" (List.map string_of_dl_def dl_defs) ^ "end\n"
