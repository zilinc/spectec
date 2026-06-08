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


(* let atom_string (a : Il.Ast.atom) : string = match a.it with
  | Atom s -> s
  | _ -> failwith "uhh compare this with the old backend" *)

let mixop_to_id (m : Il.Ast.mixop) : string = Xl.Mixop.to_string_with (Fun.const "") "" m

let convert_typcase_params (i : Il.Ast.id) (t : Il.Ast.typ) : bracketed_binder =
  ExplicitParam (
    {head = Ident i.it; tail = []},
    convert_typ t
  )

let convert_tupt (t : Il.Ast.typ) : _params list = match t.it with
  | TupT l -> List.map (fun (i, t) -> BracketedBinder (convert_typcase_params i t)) l
  | _ -> failwith "typ under typcase must be TupT!"

let convert_typcase (parent_type : Il.Ast.id) (tc : Il.Ast.typcase) : _inductive_case =
  let (m, (t, qs, ps), hs) = tc in
  {
    modifier = empty_modifier;
    id = mixop_to_id m;
    signature = (convert_tupt t, Some (Type None));
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
      cases = List.map (convert_typcase id) ts;
      deriving = None; (* TODO: look into deriving *)
    }
  | TypD (id, params, [{it = (InstD (quants, args, {it = StructT ts; _})); _}])
    -> Structure {
      modifier = empty_modifier;
      id = id.it;
      binders = [];
      universe = None;
      constructor = None; (* TODO: previous version did this *)
      fields = List.map (fun (i, (t, qs, ps), hs) -> StructSimpleBinder {
        modifier = empty_modifier;
        id = i.it;
        signature = ([], Some (convert_typ t));
      }) ts;
      deriving = None; (* TODO: look into deriving *)
    }
  | _ -> failwith "here to stop incomplete case linting lol"


let convert_script (il : script) : command list =
  List.map convert_def il