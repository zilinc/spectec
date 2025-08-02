open Il.Ast
open Util.Source
open Il.Print

type type_def' = id * param list * inst list
type type_def = type_def' phrase

(* NOTE: [rule_name] is not the same as [rule_id].
   The former is the part of the [rule_id] before the
   first "-".
*)
type rule_clause' = id * exp * exp * (prem list)  (* rule_id *)
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

let concat = String.concat
let prefix s f x = s ^ f x


let string_of_type_def td =
  let id, _ps, [{it = InstD (bs, as_, dt); _}] = td.it in
  "syntax " ^ string_of_id id ^ string_of_binds bs ^ string_of_args as_ ^ " = " ^
    string_of_deftyp `V dt ^ "\n"


let string_of_rule_clause rc =
  let id, e1, e2, prems = rc.it in
  Printf.sprintf "%s: %s ~> %s%s"
    (Il.Print.string_of_id  id)
    (Il.Print.string_of_exp e1)
    (Il.Print.string_of_exp e2)
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


let string_of_dl_def = function
| TypeDef tdef -> string_of_type_def tdef
| RuleDef rdef -> string_of_rule_def rdef
| FuncDef fdef -> string_of_func_def fdef