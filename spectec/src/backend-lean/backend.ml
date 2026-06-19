open Il.Ast
open Util.Source
(* open Il.Walk *)
open Lean_ast
open Lean_builder

let error at msg = Util.Error.error at "Lean4 translation" msg 
module NonEmptyList = Util.Lib.NonEmptyList
let preamble = "" (* TODO *)

(* let convert_alias (id : string) () *)

let rec create_curried_func (term_chain : term list) : term
  = match term_chain with
    | [] -> failwith "create_curried_func: empty term_chain"
    | [t] -> t
    | t :: ts -> FunType (t, create_curried_func ts)

let create_numtyp (nt : Il.Ast.numtyp) : term
  = match nt with
    (* TODO: check again *)
    | `NatT -> Ident "Nat"
    | `IntT -> Ident "Nat"
    | `RatT -> Ident "Nat"
    | `RealT -> Ident "Nat"

let rec create_iter (iter : Il.Ast.iter) (t : typ) : term
  = match iter with
    | Opt -> FunApp (Ident "Option", NonEmptyList.from_list_unsafe [Term (create_typ t)])
    | List -> FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (create_typ t)])
    | List1 -> FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (create_typ t)])
    | ListN _ -> FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (create_typ t)])

and create_typ (t : Il.Ast.typ) : term
  = match t.it with
    | VarT (id, []) -> Ident id.it
    | VarT (_, _) -> error t.at "arg list in VarT must be empty because they should be eliminated by undep!"
    | BoolT -> Ident "Bool"
    | NumT nt -> create_numtyp nt
    | TextT -> Ident "String"
    | TupT [] -> Ident "Unit"
    | TupT id_typ_list -> (
      let terms = List.map (fun (_, typ) -> create_typ typ) id_typ_list in
      let rec construct_prod l
        = match l with
          | [] -> failwith "should have been handled by earlier case"
          | [t] -> t
          | t :: ts -> ProdType (t, construct_prod ts)
      in
      construct_prod terms
    )
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
        FunApp (Ident parent_type.it, NonEmptyList.from_list_unsafe args)
    | _ -> failwith "all params of a typecase should be TypP"

let standard_deriving : _deriving option = Some ["Inhabited"; "BEq"]

let create_unop (op : Il.Ast.unop) : term
  = match op with
    | `PlusOp -> Ident "+"
    | `MinusOp -> Ident "-"
    | `NotOp -> Ident "¬"

let create_binop (op : Il.Ast.binop) : term
  = match op with
    | `AndOp -> Ident "&&"
    | `OrOp -> Ident "||"
    | `ImplOp -> Ident "→"
    | `EquivOp -> Ident "↔"
    | `AddOp -> Ident "+"
    | `SubOp -> Ident "-"
    | `MulOp -> Ident "*"
    | `DivOp -> Ident "/"
    | `ModOp -> Ident "%"
    | `PowOp -> Ident "^"

let create_cmpop (op : Il.Ast.cmpop) : term
  = match op with
    | `EqOp -> Ident "=="
    | `NeOp -> Ident "≠"
    | `LtOp -> Ident "<"
    | `GtOp -> Ident ">"
    | `LeOp -> Ident "≤"
    | `GeOp -> Ident "≥"

let create_optyp (t : Il.Ast.optyp) : term
  = match t with
    | `BoolT -> Ident "Bool"
    | `NatT -> Ident "Nat"
    | `IntT -> Ident "Int"
    | `RatT -> Ident "Rat"
    | `RealT -> Ident "Real"

let create_atom (a : Il.Ast.atom) : string
  = match a.it with
    | Atom s -> s
    | _ -> failwith "expected Atom"


type path_seg =
  | DotSeg of Il.Ast.atom
  | IdxSeg of Il.Ast.exp
  | SliceSeg of Il.Ast.exp * Il.Ast.exp


let rec create_exp (e : Il.Ast.exp) : term
  = match e.it with
    | VarE id -> Ident id.it
    | BoolE b -> if b then Ident "true" else Ident "false"
    | NumE n -> (
      match n with
        | `Nat n -> Num (LeanNat n)
        | `Int i -> Num (LeanInt i)
        | `Rat r -> Num (LeanRat r)
        | `Real r -> Num (LeanReal r)
      )
    | TextE t -> Text t
    | UnE (op, _, e) 
      -> FunApp (
        create_unop op,
        NonEmptyList.from_list_unsafe [Term (create_exp e)]
      )
    | BinE (op, _, e1, e2)
      -> BinaryInfixFunApp (
        Term (create_exp e1),
        create_binop op,
        Term (create_exp e2)
      )
    | CmpE (op, _, e1, e2)
      -> BinaryInfixFunApp (
        Term (create_exp e1),
        create_cmpop op,
        Term (create_exp e2)
      )
    | TupE exps -> Tuple (List.map create_exp exps)
    | ProjE (exp, idx)
      ->
        let length_of_exp
          = match exp.it with
            | TupE exps -> List.length exps
            | _ -> 1
        in

        let selector_elems =
          let twos : string list
            = List.init (length_of_exp - 1) (fun _ -> "2") in
          let final_one_or_two : string list
            = if length_of_exp = (idx + 1)
            then ["1"]
            else ["2"]
          in
          twos @ final_one_or_two
        in

        (* Constructs a selector like x.2.2.2.2.2.1 *)
        List.fold_left
          (fun acc selector_elem
            -> DotProj (acc, Ident selector_elem))
          (create_exp exp)
          selector_elems

    | CaseE (mixop, exp)
      ->
        let mixop_args : term list
          = match exp.it with
            | TupE exps -> List.map create_exp exps
            | _ -> [create_exp exp]
        in

        let namespaced_mixop = LeadingDot (Ident (mixop_to_id mixop)) in

        (* TODO: see if it's feasible to make the namespacing explicit *)
        (* let namespaced_mixop = match exp.note.it with
          | VarT (id, _) -> (DotProj (Ident id.it, Ident (mixop_to_id mixop)))
          | _ -> LeadingDot (Ident (mixop_to_id mixop))   (* fallback to leading-dot notation *)
        in *)
        
        if List.length mixop_args = 0 then
          namespaced_mixop
        else
          FunApp (
            namespaced_mixop,
            NonEmptyList.from_list_unsafe
              (List.map (fun arg -> Term arg) mixop_args)
          )
    | UncaseE (exp, mixop) -> error exp.at "Uncase should have been eliminated by uncase-removal pass!"
    | OptE (Some exp) -> FunApp (Ident "some", NonEmptyList.from_list_unsafe [Term (create_exp exp)])
    | OptE (None) -> Ident "none"
    | TheE exp -> FunApp (DotProj (Ident "Option", Ident "get!"), NonEmptyList.from_list_unsafe [Term (create_exp exp)])
    | StrE struct_fields
      ->
        let field_terms = List.map (
          fun (atom, exp) -> (create_atom atom, create_exp exp)
        ) struct_fields in
        Struct {
          fields = List.map (fun (field_name, field_value) -> AssignedField {
            l_val = Ident_SILV field_name;
            is_private = false;
            term = field_value;
          }) field_terms;
          type_annotation = None;
        }
    | DotE (exp, atom)
      -> DotProj (create_exp exp, Ident (create_atom atom))
    | CompE (e1, e2) -> BinaryInfixFunApp (Term (create_exp e1), Ident "append", Term (create_exp e2))
    | ListE exps -> List (List.map create_exp exps)
    | LiftE option_term -> FunApp (DotProj (Ident "Option", Ident "toList"), NonEmptyList.from_list_unsafe [Term (create_exp option_term)])
    | MemE (e1, e2) -> FunApp (DotProj (Ident "List", Ident "contains"), NonEmptyList.from_list_unsafe [Term (create_exp e1); Term (create_exp e2)])
    | LenE e1 -> FunApp (DotProj (Ident "List", Ident "length"), NonEmptyList.from_list_unsafe [Term (create_exp e1)])
    (* TODO: tackle pattern matching version of CatE *)
    | CatE (e1, e2) -> BinaryInfixFunApp (Term (create_exp e1), Ident "++", Term (create_exp e2))
    | IdxE (e1, e2) -> Index {
        collection = create_exp e1;
        index = create_exp e2;
        index_type = Unsafe
      }
    | SliceE (e1, e2, e3) -> Slice {
        collection = create_exp e1;
        bounds = SliceBetween (create_exp e2, create_exp e3);
      }
    | UpdE (e1, p, e2) -> create_upd_exp e1 p e2
    | ExtE (e1, p, e2) -> failwith "not implemented yet"
    | IfE (if_exp, then_exp, else_exp) -> IfThenElse {
        cond = create_exp if_exp;
        then_branch = create_exp then_exp;
        else_branch = create_exp else_exp;
      }
    | CallE (id, args) -> 
      let func = (Ident id.it : term) in
      let arg_terms = List.map (fun arg -> Term (create_arg arg)) args in
      FunApp (func, NonEmptyList.from_list_unsafe arg_terms)
    | _ -> failwith "not implemented yet"
    

and create_arg (arg : Il.Ast.arg) : term
  = match arg.it with
    | ExpA exp -> create_exp exp
    | TypA typ -> create_typ typ
    | DefA id -> Ident id.it
    | GramA _ -> failwith "not implemented yet"

        
    (* | BinE (op, t, e1, e2) -> *)

    (* | VarE (_, _) -> error e.at "arg list in VarE must be empty because they should be eliminated by undep!"
    | BoolE b -> if b then Ident "true" else Ident "false"
    | NumE n -> Num n
    | TextE s -> Text s
    | TupE [] -> Unit
    | TupE l -> Tuple (List.map create_exp l)
    | CatE (e1, e2) -> FunApp (Ident "List.append", NonEmptyList.from_list_unsafe [Term (create_exp e1); Term (create_exp e2)])
    | BinE (op, typ, e1, e2) ->
      let op_str = match op with
        | AddOp -> "+"
        | SubOp -> "-"
        | MulOp -> "*"
        | DivOp -> "/" *)

(* TODO check AI-generated *)
and create_upd_exp
  (root : Il.Ast.exp)
  (p : Il.Ast.path)
  (new_val : Il.Ast.exp)
  : term =
  
  let flatten_path (p : Il.Ast.path) : path_seg list =
    let rec go p = match p.it with
      | RootP -> []
      | DotP (p', a)       -> go p' @ [DotSeg a]
      | IdxP (p', e)       -> go p' @ [IdxSeg e]
      | SliceP (p', e1, e2)-> go p' @ [SliceSeg (e1, e2)]
    in go p
  in


  let counter = ref 0 in
  let fresh () = incr counter; "elem_" ^ string_of_int !counter in


  (* List.modify lst idx body *)
  let create_list_modify (lst : term) (idx : term) (body : term) =
    FunApp (DotProj (Ident "List", Ident "modify"),
            NonEmptyList.from_list_unsafe [Term lst; Term idx; Term body])
  in


  let rec go prev segs =
    match segs with
    | [] -> create_exp new_val
    | [DotSeg a] ->
        UpdateStruct {
          struct_to_update = prev;
          fields_to_update = [AssignedField {
            l_val = Ident_SILV (create_atom a);
            is_private = false;
            term = create_exp new_val;
          }]
        }
    | DotSeg a :: rest ->
        let field = create_atom a in
        UpdateStruct {
          struct_to_update = prev;
          fields_to_update = [AssignedField {
            l_val = Ident_SILV field;
            is_private = false;
            term = go (DotProj (prev, Ident field)) rest;
          }]
        }
    | IdxSeg e :: rest ->
        let v = fresh () in
        create_list_modify prev (create_exp e) (simple_lambda v (go (Ident v) rest))
    | SliceSeg _ :: _ ->
        failwith "SliceP inside UpdE not yet supported"
  in
  go (create_exp root) (flatten_path p)

let create_prem (p : Il.Ast.prem) : term = match p.it with
  | RulePr (
    (id : Il.Ast.id),
    ([] : Il.Ast.arg list),
    (mixop : Il.Ast.mixop),
    (exp : Il.Ast.exp)
  ) -> FunApp (
    Ident id.it,
    NonEmptyList.from_list_unsafe [Term (create_exp exp)]
  )
  | IfPr (
    (exp : Il.Ast.exp)
  ) -> create_exp exp
  | _ -> Ident "TEMPORARY_PREM"


let append_prems_to_term (term : term) (prems : Il.Ast.prem list) : term
  = if prems = [] then term
    else
      let prems_as_terms = List.map create_prem prems in
      create_curried_func (prems_as_terms @ [term])

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
                NonEmptyList.from_list_unsafe [(Ident id.it : _ident_or_hole);], (* TODO: disambiguate Ident *)
                create_typ typ
              ))
            ) id_typ_list
        | _ -> failwith "typ under typcase must be TupT!"
  in

  let params_from_quants (* (v_n : n) *)
    = List.map (
      fun q -> match q.it with
        | ExpP (id, typ) -> BracketedBinder(ExplicitParam(
          NonEmptyList.from_list_unsafe [(Ident id.it : _ident_or_hole);], (* TODO: disambiguate Ident *)
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

let create_def (def : Il.Ast.def) : command option
  = match def.it with

    | TypD (id, params, [{it = (InstD (quants, args, {it = AliasT t; _})); _}])
      -> Some (Abbrev (AbbrevAsgn {
        modifier = empty_modifier;
        id = id.it;
        signature = ([], Some (Type None));
        body = create_typ t;
      }))

    | TypD (id, params, [{it = (InstD (quants, args, {it = VariantT ts; _})); _}])
      -> Some (Inductive {
        modifier = empty_modifier;
        id = id.it;
        signature = ([], Some (Type None));
        cases = List.map (create_typcase id params) ts;
        deriving = standard_deriving; (* TODO: look into deriving *)
      })

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
      Some (Structure {
        modifier = empty_modifier;
        id = id.it;
        binders = [];
        universe = None;
        constructor = Some (empty_modifier, "MK" ^ id.it); (* following previous version *)
        fields = List.map create_struct_field ts;
        deriving = standard_deriving; (* TODO: look into deriving *)
      })

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

      let create_relations_inductive_case (rule : Il.Ast.rule) (rel_id : Il.Ast.id) : _inductive_case
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
                    NonEmptyList.from_list_unsafe [(Ident id.it : _ident_or_hole);], (* TODO: disambiguate Ident *)
                    create_typ typ
                  ))
                  | _ -> failwith "only ExpP should be here"
              ) quants
            in

            let exp_with_rel_id_prepended : term (* fun_sum ([v_n] ++ n'_lst) (v_n + var_0) *)
              = let mixop_args : term list
                  = match exp.it with
                    | TupE exps -> List.map create_exp exps
                    | _ -> [create_exp exp]
                in
                let id_as_term = (Ident rel_id.it : term) in
                FunApp (
                  id_as_term,
                  NonEmptyList.from_list_unsafe (List.map (fun arg -> Term arg) mixop_args)
                )
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
                  exp_with_rel_id_prepended
                  prems
                )
              );
            }

      in

      Some (Inductive {
        modifier = empty_modifier;
        id = id.it;                       (* fun_sum *)
        signature = (
          [],                             (* We don't need parameters for the inductive type itself *)
          Some (create_relations_inductive_type typ)   (* List Nat → Nat → Prop *)
        );
        cases = List.map (fun rule -> create_relations_inductive_case rule id) rules;
        deriving = None; (* TODO: look into deriving *)
      })

    | DecD (
      id,                               (* "Ki" *)
      [],                               (* This handles the case with no params *)
      typ,                              (* nat *)
      [{it = DefD ([], [], exp, prems); _}]    (* (NumE (Nat 1024)) *)
    )

    (*
      Let's say we have a definition like

      def $Ki : nat
      def $Ki = 1024

      We want to generate a Lean4 definition like

      def Ki : Nat := 1024
    *)
      -> Some (Def (DefAsgn {
        modifier = empty_modifier;
        id = id.it;                               (* "Ki" *)
        signature = (
          [],
          Some (create_typ typ)                   (* Nat *)
        );
        body = create_exp exp;                    (* 1024 *)
      }))


    | DecD (
      id,
      params,
      typ,
      []
    ) -> failwith "case 1"
    | DecD (id, [], typ, clauses) -> failwith "case 1"

    | DecD _ -> None
    | GramD _ -> None
    | RecD _ -> None
    | HintD _ -> None
    | RelD _ -> failwith "should have been handled by earlier case"
    | TypD _ -> None


let create_script (il : script) : command list
  = List.filter_map create_def il