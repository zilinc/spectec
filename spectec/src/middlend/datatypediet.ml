(* 

This transformation aims to produce an AST where no datatype has more than *50* constructors.

This is because some proof assistants, like Isabelle, struggle to process datatypes with many constructors. In Isabelle, compiling a datatype is quadratic in the number of constructors, and 50 constructors already takes several seconds. 

Instead, when a datatype has more than 50 constructors, we redefine the grammar with several layers, e.g.

mydatatype =
| Case0 of args0
| Case1 of args1
| Case2 of args2
.
.
.
| Case99 of args99

becomes

mydatatype =
| Mydatatype_case0 of mydatatype0
| Mydatatype_case1 of mydatatype1
| Mydatatype_case2 of mydatatype2
.
.
.
| Mydatatype_case10 of mydataype10

where

mydatatype_case0 =
| Expanded_case0 of args0
| Expanded_case1 of args1
| Expanded_case2 of args2
.
.
.
| Expanded_case9 of args9

and

mydatatype_case1 =
| Expanded_case10 of args10
| Expanded_case11 of args11
| Expanded_case12 of args12
.
.
.
| Expanded_case19 of args19

etc.

We can then define functions Case0 args = Mydatatype_case0 (Expanded_case0 args) to allow the user to use their constructor names on all RHS occurences.

We still need to replace all occurences of constructor `Case37 args` with `Mydatatype_case3 (Expanded_case37 args)`, etc in LHS occurences.

For optimality, when breaking up a datatype with a number N>50 of constructors, we make sqrt(N) cases. If sqrt(N) is greater than 50 we repeat the operation recursively.

Recursion: if mydatatype is recursive, we group all non-recursive cases first and make a minimal recursive definition in the end.

 *)


open Il.Ast
open Util.Source

module StringMap = Map.Make(String)


let transform_exp acc exp =
  assert false (* TODO: replace LHS occurences *)

let transform_arg acc arg =
  assert false (* TODO: replace LHS occurences *)

let transform_iterexp acc itexp =
  assert false (* TODO: easy bit *)

let rec transform_prem acc prem =
  match prem.it with
  | RulePr (id, args, op, exp) -> {prem with it = RulePr (id, List.map (transform_arg acc) args, op, transform_exp acc exp)}
  | IfPr exp -> {prem with it = IfPr (transform_exp acc exp)}
  | LetPr (exp1, exp2, ss) -> {prem with it = LetPr (transform_exp acc exp1, transform_exp acc exp2, ss)}
  | ElsePr -> prem
  | IterPr (prem', itexp) -> {prem with it = IterPr (transform_prem acc prem', transform_iterexp acc itexp)}
  | NegPr prem' -> {prem with it = NegPr (transform_prem acc prem')}

let transform_rule acc rule =
  match rule.it with
  | RuleD (id, quants, op, exp, prems) -> {rule with it = RuleD (id, quants, op, transform_exp acc exp, List.map (transform_prem acc) prems)}

let transform_clause acc clause =
  assert false (* TODO: easy bit *)

let transform_prod acc clause =
  assert false (* TODO : easy bit *)

let transform_typ_def acc id params insts =
  assert false (* TODO: meaty bit *)

let transform_def acc def =
  match def.it with
  | TypD (id, params, insts) -> transform_typ_def acc id params insts 
  | RelD (id, params, op, t, rules) ->  acc, [{def with it = RelD (id, params, op, t, List.map (transform_rule acc) rules)}]
  | DecD (id, params, t, clauses) -> acc, [{def with it = DecD (id, params, t, List.map (transform_clause acc) clauses)}]
  | GramD (id, params, t, prods) -> acc, [{def with it = GramD (id, params, t, List.map (transform_prod acc) prods)}]
  | RecD defs -> assert false (* TODO: deal with mutual recursion *)
  | HintD _ -> acc, [def]



let transform_script script =
  let (_, defs) = List.fold_left (fun (acc, defs) def ->
                      let (acc, def) = transform_def acc def in
                      acc, def :: defs) (StringMap.empty, []) script in
  List.flatten (List.rev defs)
