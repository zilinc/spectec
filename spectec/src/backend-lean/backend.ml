open Il.Ast
open Util.Source
open Il.Walk
open Lean_ast
open Lean_builder

let error at msg = Util.Error.error at "Lean4 translation" msg 

let preamble = "" (* TODO *)

(* let convert_alias (id : string) () *)

let nel (l : 'a list) : 'a non_empty_list
  = match l with
    | [] -> failwith "expected non-empty list"
    | head :: tail -> {head; tail}

let rec create_curried_func (term_chain : term list) : term
  = match term_chain with
    | [] -> failwith "create_curried_func: empty term_chain"
    | [t] -> t
    | t :: ts -> Fun (t, create_curried_func ts)

let create_numtyp (nt : Il.Ast.numtyp) : term
  = match nt with
    (* TODO: check again *)
    | `NatT -> Ident "Nat"
    | `IntT -> Ident "Nat"
    | `RatT -> Ident "Nat"
    | `RealT -> Ident "Nat"

let rec create_iter (iter : Il.Ast.iter) (t : typ) : term
  = match iter with
    | Opt -> Ident "Option"
    | List -> FunApp (Ident "List", {head = Term (create_typ t); tail = []})
    | List1 -> FunApp (Ident "List", {head = Term (create_typ t); tail = []})
    | ListN _ -> FunApp (Ident "List", {head = Term (create_typ t); tail = []})

and create_typ (t : Il.Ast.typ) : term
  = match t.it with
    | VarT (id, []) -> Ident id.it
    | VarT (_, _) -> error t.at "arg list in VarT must be empty because they should be eliminated by undep!"
    | BoolT -> Ident "Bool"
    | NumT nt -> create_numtyp nt
    | TextT -> Ident "String"
    | TupT [] -> Ident "Unit"
    | TupT l -> Prod (List.map (Fun.compose create_typ snd) l)
    | IterT (t, iter) -> create_iter iter t


(* let atom_string (a : Il.Ast.atom) : string = match a.it with
  | Atom s -> s
  | _ -> failwith "uhh compare this with the old backend" *)

let mixop_to_id (m : Il.Ast.mixop) : string
  = Xl.Mixop.to_string_with (Fun.const "") "" m

(* let create_typcase_params (i : Il.Ast.id) (t : Il.Ast.typ) : bracketed_binder =
  ExplicitParam (
    {head = Ident i.it; tail = []},
    create_typ t
  ) *)

let create_inductive_type_with_params_applied
  (parent_type : Il.Ast.id)
  (params : Il.Ast.quant list)
  : term
  = match params with
    | [] -> Ident parent_type.it
    | _
      when List.for_all (fun p -> match p.it with TypP _ -> true | _ -> false) params
      ->
        let args = List.map (
          fun p -> match p.it with
            | TypP t -> Term (Ident t.it)
            | _ -> failwith "all params of a typecase should be TypP"
        ) params in
        FunApp (Ident parent_type.it, nel args)
    | _ -> failwith "all params of a typecase should be TypP"

let create_unop (op : Il.Ast.unop) : string
  = match op with
    | `PlusOp -> "+"
    | `MinusOp -> "-"

let create_optyp (t : Il.Ast.optyp) : term
  = match t with
    | `BoolT -> Ident "Bool"
    | `NatT -> Ident "Nat"
    | `IntT -> Ident "Int"
    | `RatT -> Ident "Rat"

let create_exp (e : Il.Ast.exp) : term
  = match e.it with
    | VarE id -> Ident id.it
    | BoolE b -> if b then Ident "true" else Ident "false"
    | NumE n -> match n with
      | `Nat n -> Num (LeanNat n)
      | `Int i -> Num (LeanInt i)
      | `Rat r -> Num (LeanRat r)
      | `Real r -> Num (LeanReal r)
    | TextE t -> Text t

    (* | VarE (_, _) -> error e.at "arg list in VarE must be empty because they should be eliminated by undep!"
    | BoolE b -> if b then Ident "true" else Ident "false"
    | NumE n -> Num n
    | TextE s -> Text s
    | TupE [] -> Unit
    | TupE l -> Tuple (List.map create_exp l)
    | CatE (e1, e2) -> FunApp (Ident "List.append", nel [Term (create_exp e1); Term (create_exp e2)])
    | BinE (op, typ, e1, e2) ->
      let op_str = match op with
        | AddOp -> "+"
        | SubOp -> "-"
        | MulOp -> "*"
        | DivOp -> "/" *)

let create_prem (p : Il.Ast.prem) : term = match p.it with
  | RulePr (
    (id : Il.Ast.id),
    ([] : Il.Ast.arg list),
    (mixop : Il.Ast.mixop),
    (exp : Il.Ast.exp)
  ) -> failwith ""


let append_prems_to_term (term : term) (prems : Il.Ast.prem list) : term
  = if prems = [] then term
    else
      let prems_as_terms = List.map create_prem prems in
      create_curried_func (term :: prems_as_terms)

let create_typcase
  (* 
  Take the example of a toy inductive type

  inductive vec (X : Type) : Type
    | mk_vec (X_lst : List X) (v_n : n) : X_lst.length < v_n -> vec X

  This function is responsible for creating typecases such as

    | mk_vec (X_lst : List X) (v_n : n) : X_lst.length < v_n -> vec X
  *)
  (parent_type    : Il.Ast.id)            (* In the example, this would be `vec` *)
  (parent_params  : Il.Ast.quant list)    (* In the example, this would be `(X : Type)` *)
  (typcase        : Il.Ast.typcase)       (* In the example, this would be `mk_vec (X_lst : List X) {v_n : n} : X_lst.length < v_n` *)
  : _inductive_case
  =
  
  let (
    mixop,                  (* mk_vec *)
    (
      typ,                  (* (X_lst : List X) *)
      quants,               (* (v_n : n) *)
      prems                 (* X_lst.length < v_n *)
    ),
    _                       (* hints are ignored *)
  ) = typcase
  in

  let inductive_type_with_params_applied (* vec X *)
    = create_inductive_type_with_params_applied parent_type parent_params
  in

  let appended_with_prems (* X_lst.length < v_n -> vec X *)
    = append_prems_to_term inductive_type_with_params_applied prems
  in

  let params_from_typ (* (X_lst : List X) *)
    = match typ.it with
        | TupT id_typ_list 
            -> List.map (
              fun (id, typ) -> BracketedBinder(ExplicitParam(
                nel [(Ident id.it : _ident_or_hole);], (* TODO: disambiguate Ident *)
                create_typ typ
              ))
            ) id_typ_list
        | _ -> failwith "typ under typcase must be TupT!"
  in

  let params_from_quants (* (v_n : n) *)
    = List.map (
      fun q -> match q.it with
        | ExpP (id, typ) -> BracketedBinder(ExplicitParam(
          nel [(Ident id.it : _ident_or_hole);], (* TODO: disambiguate Ident *)
          create_typ typ
        ))
        | _ -> failwith "only ExpP should be here"
    ) quants
  in
  
  {
    modifier = empty_modifier;
    id = mixop_to_id mixop;
    signature = (
      params_from_typ @ params_from_quants,
      Some appended_with_prems
    );
  }

let create_def (def : Il.Ast.def) : command
  = match def.it with

    | TypD (id, params, [{it = (InstD (quants, args, {it = AliasT t; _})); _}])
      -> Abbrev (AbbrevAsgn {
        modifier = empty_modifier;
        id = id.it;
        signature = ([], Some (Type None));
        body = create_typ t;
      })

    | TypD (id, params, [{it = (InstD (quants, args, {it = VariantT ts; _})); _}])
      -> Inductive {
        modifier = empty_modifier;
        id = id.it;
        signature = ([], Some (Type None));
        cases = List.map (create_typcase id params) ts;
        deriving = None; (* TODO: look into deriving *)
      }

    | TypD (id, params, [{it = (InstD (quants, args, {it = StructT ts; _})); _}])
      ->
      let create_struct_field (typfield : Il.Ast.typfield) : struct_field
        =
        let (atom, (typ, quants, prems), hints) = typfield in
        StructSimpleBinder {
          modifier = empty_modifier;
          id = Xl.Atom.to_string atom;
          signature = ([], Some (create_typ typ));
        }
      in
      Structure {
        modifier = empty_modifier;
        id = id.it;
        binders = [];
        universe = None;
        constructor = Some (empty_modifier, "MK" ^ id.it); (* following previous version *)
        fields = List.map create_struct_field ts;
        deriving = None; (* TODO: look into deriving *)
      }

    | RelD (
        id,     (* fun_sum *)
        [],     (* undep should get rid of params, so this should be empty *)
        mixop,
        typ,    (* (TupT (typbind "_" (IterT nat List)) (typbind "_" nat)) *)
        rules   (* (RuleD "fun_sum_case_0" (Seq Arg Arg) (TupE (ListE) (NumE (Nat 0)))) *)
      )
      ->
      (*
        Taking the example of
      
        inductive fun_sum : List Nat → Nat → Prop where
          | fun_sum_case_0 : fun_sum [] 0
          | fun_sum_case_1 (v_n : Nat) (n'_lst : List Nat) (var_0 : Nat) :
              fun_sum n'_lst var_0 →
              fun_sum ([v_n] ++ n'_lst) (v_n + var_0)
      *)

      let create_relations_inductive_type (typ : Il.Ast.typ) : term
        (* List Nat → Nat → Prop *)
        = match typ.it with
          | VarT (id, []) -> Ident id.it
          | VarT _ -> failwith "undep should ensure empty arg list" 
          | TupT id_typ_list ->
            let types = List.map (fun (_, typ) -> create_typ typ) id_typ_list in
            let types_and_prop = types @ [Ident "Prop"] in
            create_curried_func types_and_prop
          | _ -> failwith "no other typ should be here!"  
      in

      let create_relations_inductive_case (rule : Il.Ast.rule) : _inductive_case
        (*
          | fun_sum_case_1 (v_n : Nat) (n'_lst : List Nat) (var_0 : Nat) :
                fun_sum n'_lst var_0 →
                fun_sum ([v_n] ++ n'_lst) (v_n + var_0)
        *)
        = match rule.it with
          | RuleD (
              id,     (* fun_sum_case_1 *)
              quants, (*
                        (ExpP "v_n" nat)
                        ...
                      *)
              mixop,
              exp,    (*
                        (TupE
                          (CatE (ListE (VarE "v_n")) (VarE "n'_lst"))
                          (BinE AddOp nat (VarE "v_n") (VarE "var_0"))
                        )
                        ...
                      *)
              prems   (* (RulePr "fun_sum" (Seq Arg Arg) (TupE (VarE "n'_lst") (VarE "var_0"))) *)
            )
            ->
            let params_from_args : _params list (* (v_n : Nat) (n'_lst : List Nat) (var_0 : Nat) *)
              = List.map (
                fun q -> match q.it with
                  | ExpP (id, typ) -> BracketedBinder(ExplicitParam(
                    nel [(Ident id.it : _ident_or_hole);], (* TODO: disambiguate Ident *)
                    create_typ typ
                  ))
                  | _ -> failwith "only ExpP should be here"
              ) quants
            in
            
            {
              modifier = empty_modifier;
              id = id.it;                 (* fun_sum_case_1 *)
              signature = (
                params_from_args,         (* (v_n : Nat) (n'_lst : List Nat) (var_0 : Nat) *)

                (*
                    fun_sum n'_lst var_0 →
                    fun_sum ([v_n] ++ n'_lst) (v_n + var_0)
                *)
                Some (
                  append_prems_to_term
                  (create_exp exp)
                  prems
                )
              );
            }
          | _ -> failwith "no other `rule'` exists in the AST at time of writing"

      in

      Inductive {
        modifier = empty_modifier;
        id = id.it;                       (* fun_sum *)
        signature = (
          [],                             (* We don't need parameters for the inductive type itself *)
          Some (create_relations_inductive_type typ)   (* List Nat → Nat → Prop *)
        );
        cases = List.map create_relations_inductive_case rules;
        deriving = None; (* TODO: look into deriving *)
      }

    | _ -> failwith "unexpected case in create_def"


let create_script (il : script) : command list
  = List.map create_def il