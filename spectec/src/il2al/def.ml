open Il.Ast
open Util.Source

type partial = Partial | Total
type helper_clause = clause
type helper_def' = id * helper_clause list * partial
type helper_def = helper_def' phrase
type func_clause = clause
type func_def' = id * func_clause list
type func_def = func_def' phrase
type rule_clause = id * exp * exp * (prem list)
type rule_def' = string * id * rule_clause list  (* rule_name, rel_id, rules *)
type rule_def = rule_def' phrase
type dl_def = RuleDef of rule_def | HelperDef of helper_def