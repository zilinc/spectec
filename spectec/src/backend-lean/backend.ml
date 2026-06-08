open Il.Ast
open Util.Source
open Il.Walk
open Lean_ast
open Lean_builder

let error at msg = Util.Error.error at "Lean4 translation" msg 

let preamble = "" (* TODO *)

(* let convert_alias (id : string) () *)

let convert_numtyp (nt : Il.Ast.numtyp) : term = match nt with
  (* TODO: check again *)
  | `NatT -> Ident "Nat"
  | `IntT -> Ident "Nat"
  | `RatT -> Ident "Nat"
  | `RealT -> Ident "Nat"

let rec convert_iter (iter : Il.Ast.iter) (t : typ) : term = match iter with
  | Opt -> Ident "Option"
  | List -> FunApp (Ident "List", {head = Term (convert_typ t); tail = []})
  | List1 -> FunApp (Ident "List", {head = Term (convert_typ t); tail = []})
  | ListN _ -> FunApp (Ident "List", {head = Term (convert_typ t); tail = []})

and convert_typ (t : Il.Ast.typ) : term = match t.it with
  | VarT (id, []) -> Ident id.it
  | VarT (_, _) -> error t.at "arg list in VarT must be empty because they should be eliminated by undep!"
  | BoolT -> Ident "Bool"
  | NumT nt -> convert_numtyp nt
  | TextT -> Ident "String"
  | TupT [] -> Ident "Unit"
  | TupT l -> Prod (List.map (Fun.compose convert_typ snd) l)
  | IterT (t, iter) -> convert_iter iter t

let convert_typcase (tc : Il.Ast.typcase) : _inductive_case = {
  modifier = empty_modifier;
  id = tc.id;
  signature = ([], Some (Type None));
}

let convert_def (d : Il.Ast.def) : command = match d.it with
  | TypD (id, params, [{it = (InstD (quants, args, {it = AliasT t; _})); _}])
    -> Abbrev (AbbrevAsgn {
      modifier = empty_modifier;
      id = id.it;
      signature = ([], Some (Type None));
      body = convert_typ t;
    })
  | TypD (id, params, [{it = (InstD (quants, args, {it = VariantT ts; _})); _}])
    -> Inductive {
      modifier = empty_modifier;
      id = id.it;
      signature = ([], Some (Type None));
      cases = 
    }
  | _ -> failwith "here to stop incomplete case linting lol"


let convert_script (il : script) : command list =
  List.map convert_def il