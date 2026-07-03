open Il.Ast
open Util.Source
(* open Il.Walk *)
open Lean_ast
open Lean_builder
open Lean_utils

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

let rec create_iter_typ (iter : Il.Ast.iter) (t : typ) : term
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
    | IterT (t, iter) -> create_iter_typ iter t

let mixop_to_id (m : Il.Ast.mixop) : string
  = Xl.Mixop.to_string_with (Fun.const "") "" m

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
    | `NotOp -> Ident "!"

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
    | MemE (e1, e2) -> FunApp (DotProj (Ident "List", Ident "contains"), NonEmptyList.from_list_unsafe [Term (create_exp e2); Term (create_exp e1)])
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
    | UpdE (e1, p, e2) -> create_upd_exp e1 p (fun _ -> create_exp e2)
    | ExtE (e1, p, e2) ->
        let concat_old_term_to_new_list_exp (existing_term : term) : term
          = BinaryInfixFunApp (
              Term (existing_term),
              Ident "++",
              Term (create_exp e2)
            )
        in

        (match e2.it with
          | ListE _ -> create_upd_exp e1 p (fun existing_term -> concat_old_term_to_new_list_exp existing_term)
          | _ -> failwith "ExtE must take a list as the new value")
    | IfE (if_exp, then_exp, else_exp) -> IfThenElse {
        cond = create_exp if_exp;
        then_branch = create_exp then_exp;
        else_branch = create_exp else_exp;
      }
    | CallE (id, args) -> 
      let func = (Ident id.it : term) in
      let arg_terms = List.map (fun arg -> Term (create_arg arg)) args in
      FunApp (func, NonEmptyList.from_list_unsafe arg_terms)
    | IterE (exp, iterexp) -> create_iter exp iterexp
    | CvtE (exp, numtyp1, numtyp2) -> 
      BinaryInfixFunApp (
        Term (create_exp exp),
        Ident ":",
        Term (create_numtyp numtyp2)
      )
      (* let func = Ident "cast" in
      let arg_terms = NonEmptyList.from_list_unsafe [
        Term (create_exp exp);
        Term (create_numtyp numtyp1);
        Term (create_numtyp numtyp2);
      ] in
      FunApp (func, arg_terms) *)
    | _ -> failwith "not implemented yet for create_exp"
    
and create_iter
  (*
      Let's say we have an example like


      (a.map (fun w x y z => w + x + y + z)).ap b |>.ap c |>.ap d

      from

      (IterE
        (BinE AddOp NatT
          (BinE AddOp NatT
            (BinE AddOp NatT (VarE "a") (VarE "b"))
            (VarE "c"))
          (VarE "d"))
        List
        (iterexp "a" (ListE (NumE (Nat 1)) (NumE (Nat 2)) (NumE (Nat 3))))
        (iterexp "b" (ListE (NumE (Nat 4)) (NumE (Nat 5)) (NumE (Nat 6))))
        (iterexp "c" (ListE (NumE (Nat 7)) (NumE (Nat 8)) (NumE (Nat 9))))
        (iterexp "d" (ListE (NumE (Nat 10)) (NumE (Nat 11)) (NumE (Nat 12))))
      )
  *)
  (exp : Il.Ast.exp)            (*
                                  (BinE AddOp NatT
                                    (BinE AddOp NatT
                                      (BinE AddOp NatT (VarE "a") (VarE "b"))
                                      (VarE "c"))
                                    (VarE "d"))
                                *)
  (iterexp : Il.Ast.iterexp)
  : term =
    let (
      iter,                     (* List *)
      id_exp_list               (*
                                  (iterexp "a" (ListE (NumE (Nat 1)) (NumE (Nat 2)) (NumE (Nat 3))))
                                  (iterexp "b" (ListE (NumE (Nat 4)) (NumE (Nat 5)) (NumE (Nat 6))))
                                  (iterexp "c" (ListE (NumE (Nat 7)) (NumE (Nat 8)) (NumE (Nat 9))))
                                  (iterexp "d" (ListE (NumE (Nat 10)) (NumE (Nat 11)) (NumE (Nat 12))))
                                *)
    ) = iterexp in
    
    let arity = List.length id_exp_list in
    

    match arity, iter with
    | 0, ListN (n_exp, None) ->
      (*
        List.replicate n_exp exp
      *)
      FunApp (
        DotProj (Ident "List", Ident "replicate"),
        NonEmptyList.from_list_unsafe
          [Term (create_exp n_exp); Term (create_exp exp)]
      )
    | 0, ListN (n_exp, Some id) ->
      (*
        List.range n_exp |>.map (fun id => exp)
      *)
      FunApp (
        RightPipelineField (
          FunApp (
            DotProj (Ident "List", Ident "range"),
            NonEmptyList.from_list_unsafe [Term (create_exp n_exp)]
          ),
          Ident "map"
        ),
        NonEmptyList.from_list_unsafe
          [
            Term (Lambda {

              (* NOTE: The point of the `id` in the case of `ListN (n_exp, Some
              id)` is that the body `exp` already uses this name in its
              variables, so we don't need to worry about matching names in the
              backend.*)
              params = NonEmptyList.from_list_unsafe [Ident_FB id.it];

              body = create_exp exp;
            })
          ]
      )


    | _ ->
      
      (*
        The remaining cases share some infrastructure which we define below,
        before creating another `match` case to handle each remaining case
      *)

      let elem_name_generator (id : Il.Ast.id) : string
        (*
          Gives sensible names to the variables that will be used to represent
          elements of a list in the lambda. For example,

          a.map (fun a_elem b_elem c_elem d_elem => a_elem + b_elem + c_elem + d_elem) |>.ap b |>.ap c |>.ap d

          ^          ^
          list       list elem
        *)
        = id.it ^ "_elem"
      in

      (* [a, b, c, d] *)
      let target_ids_to_rename = List.map (fun (id, _) -> id.it) id_exp_list in

      let rename_il_vars (target_ids_to_rename : string list) (exp : Il.Ast.exp) : Il.Ast.exp =

        let t = { Il.Walk.base_transformer with
          transform_var_id = fun id ->
            if List.mem id.it target_ids_to_rename
            then { id with it = elem_name_generator id }
            else id
        } in

        Il.Walk.transform_exp t exp
      in

      let renamed_exp = rename_il_vars target_ids_to_rename exp in

      let collections = List.map (fun (_, exp) -> create_exp exp) id_exp_list in

      let create_zip
        (*
          Creates a term that zips together the lists in `list_terms` using the
          function `zipping_func`. For example, given

          list_terms = [a, b, c, d]
          zipping_func = fun a_elem, b_elem, c_elem, d_elem => a_elem + b_elem + c_elem + d_elem

          The result will be the term:

          a.map (fun w x y z => w + x + y + z) |>.ap b |>.ap c |>.ap d

          where List.ap is our custom application function that should be defined in the prologue.
        *)

        (list_terms : term list)               (* [a, b, c, d]*)
        (zipping_func : term)                  (* fun a_elem, b_elem, c_elem, d_elem => a_elem + b_elem + c_elem + d_elem *)
        : term =
        
        (* this helper exists because we need a recursive function, but we also
        need to reverse the terms list exactly once on entry. The reversing is
        just to make it convenient to do hd and tl. *)
        let rec go
          (reversed_terms : term list)      (* [d, c, b, a]*)
          (func : term)                     (* fun a_elem, b_elem, c_elem, d_elem => a_elem + b_elem + c_elem + d_elem *)
          : term =

          let arity = List.length reversed_terms in
          
          match arity with
          | 0 -> failwith "arity should never reach 0 here"
          | 1 -> 
            let term = List.hd reversed_terms in
            FunApp (
              (RightPipelineField (term, Ident "map")),
              NonEmptyList.from_list_unsafe
                [Term func]
            )
          | _ ->
            let term = List.hd reversed_terms in
            let nested = go (List.tl reversed_terms) func in
            FunApp (
              RightPipelineField (
                nested,
                Ident "ap"
              ),
              NonEmptyList.from_list_unsafe
                [Term term]
            )
        in

        go (List.rev list_terms) zipping_func
      in
      
      (
        match arity, iter with
      
          | arity, Opt | arity, List | arity, List1 | arity, ListN (_, None)
            when arity > 0 ->

            let lambda_func : term =              (* fun a_elem, b_elem, c_elem, d_elem => a_elem + b_elem + c_elem + d_elem *)
              Lambda {
                params =                          (* a_elem, b_elem, c_elem, d_elem *)
                  NonEmptyList.from_list_unsafe (
                    List.map
                      (fun (id, _) -> Ident_FB (elem_name_generator id))
                    id_exp_list
                  );

                body = create_exp renamed_exp;    (* a_elem + b_elem + c_elem + d_elem *)
              }
            in

            create_zip collections lambda_func
          
          | arity, ListN (n_exp, Some id) when arity > 0 ->

            let range_term =
              FunApp (
                DotProj (Ident "List", Ident "range"),
                NonEmptyList.from_list_unsafe [Term (create_exp n_exp)]
              )
            in

            let lambda_with_index = Lambda {
                params =
                  NonEmptyList.from_list_unsafe (

                    (* extra term for index. DO NOT use elem_name_generator on
                    this since `exp` already uses exactly this id *)
                    Ident_FB id.it ::

                    (List.map
                      (fun (id, _) -> Ident_FB (elem_name_generator id))
                    id_exp_list)
                  );
                body = create_exp renamed_exp;
              }
            in

            create_zip (range_term :: collections) lambda_with_index

          | _ -> failwith "other cases should not exist!"
      )

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
  (* (new_val : Il.Ast.exp) *)
  (operation_on_old_val : term -> term)
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


  let rec go
    (prev : term)
    (segs : path_seg list) =
    match segs with
    | [] -> operation_on_old_val prev
    | [DotSeg a] ->
        UpdateStruct {
          struct_to_update = prev;
          fields_to_update = [AssignedField {
            l_val = Ident_SILV (create_atom a);
            is_private = false;
            term = operation_on_old_val (DotProj (prev, Ident (create_atom a)));
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


(* ── IterPr helpers ─────────────────────────────────────────────────────────
   These are standalone (not in the create_exp and-chain) because they only
   depend on create_exp (defined above) and create_prem/create_iter_prem
   (defined below as a mutual let rec pair).
   ─────────────────────────────────────────────────────────────────────────── *)


(*
  make_left_zip collections

  Build a left-associatively zipped list from two or more Lean terms using
  the |>.zip syntax (RightPipelineField).

  Example with 2 inputs [m_lst; n_lst] (Pairs_ok):
    m_lst |>.zip (n_lst)  →  m_lst.zip n_lst  : List (m × n)

  Example with 3 inputs [xs; ys; zs]:
    xs |>.zip (ys) |>.zip (zs)  →  (xs.zip ys).zip zs  : List ((α × β) × γ)

  This is only called for n ≥ 2.
*)
let make_left_zip (collections : term list) : term =
  (* collections = [xs; ys; zs; ...]  (at least 2 elements) *)
  List.fold_left
    (fun acc coll ->
      (* acc.zip coll  →  FunApp(RightPipelineField(acc, "zip"), [coll]) *)
      FunApp (
        RightPipelineField (acc, Ident "zip"),
        NonEmptyList.from_list_unsafe [Term coll]
      ))
    (List.hd collections)    (* start with xs *)
    (List.tl collections)    (* fold in ys, then zs, etc. *)

(*
  make_proj i n base

  Return the Lean projection for element at 0-indexed position i in a
  left-nested tuple of depth n, rooted at base.

  Left-nested structure (how List.zip chains):
    n=2 : α × β           → i=0: base.1   i=1: base.2
      (Pairs_ok: base=__iter_tuple; i=0 → "v_m"=__iter_tuple.1, i=1 → "v_n"=__iter_tuple.2)
    n=3 : (α × β) × γ     → i=0: base.1.1   i=1: base.1.2   i=2: base.2
    n=4 : ((α×β)×γ) × δ   → i=0: base.1.1.1  i=1: base.1.1.2  i=2: base.1.2  i=3: base.2

  Recursive rule:
    n=1        → base             (scalar, no tuple)
    i = n-1    → base.2           (last element is always the right component)
    otherwise  → proj i (n-1) base.1   (recurse into left sub-tuple)
*)
let rec make_proj (i : int) (n : int) (base : term) : term =
  if n = 1 then
    base                                               (* n=1: element is the term itself *)
  else if i = n - 1 then
    DotProj (base, Ident "2")                         (* last element → .2 *)
  else
    make_proj i (n - 1) (DotProj (base, Ident "1"))  (* recurse into left sub-tuple via .1 *)


(*
  create_prem and create_iter_prem are mutually recursive:
    create_prem dispatches IterPr to create_iter_prem
    create_iter_prem calls create_prem on (possibly renamed) sub-premises

  ── create_prem ────────────────────────────────────────────────────────────
  Translates an IL premise into a Lean term (always a Prop-valued expression).

  ── create_iter_prem ───────────────────────────────────────────────────────
  Translates IterPr(p, iterexp) into a kernel-safe BoundedForall term.

  IterPr(p, (iter, id_exp_list)) means:
    "premise p holds for every simultaneous assignment of variables id_i to
     elements drawn in parallel from their respective collections."

  We use ∀ x ∈ xs, P x rather than inductive Forall/Forall₂ because the
  inductive form breaks Lean's positivity checker inside mutual inductive
  blocks (see PR #192 discussion, Lean issue leanprover/lean4#1964).

  ARITY 0 — no iteration variables, emit the premise directly:
    IterPr(IfPr(x == y), (List, []))
    →  x == y

  ARITY 1 — single collection, emit ∀ var ∈ collection, body:
    IterPr(RulePr("TypeOk", VarE "t"), (List, [("t", VarE "ts")]))
    →  ∀ t ∈ ts, TypeOk (t)

    No renaming needed: the prem body already uses "t" as the element
    variable, and BoundedForall binds "t" exactly.

  ARITY ≥ 2 — zip all collections, bind one tuple variable, project each:
    IterPr(
      RulePr("Pair_ok", (Infix Arg |- Arg), TupE [VarE "v_n"; VarE "v_m"]),
      (List, [("v_m", VarE "m_lst"); ("v_n", VarE "n_lst")])
    )
    →  ∀ __iter_tuple ∈ m_lst |>.zip (n_lst),
         Pair_ok (__iter_tuple.2) (__iter_tuple.1)

  Algorithm for arity ≥ 2:
    1. Build zipped collection: m_lst |>.zip (n_lst)
    2. create_prem on the UNCHANGED prem → Lean term with Ident "v_n", Ident "v_m"
    3. Substitute: "v_m" (i=0) → __iter_tuple.1, "v_n" (i=1) → __iter_tuple.2
       — this is safe (no capture) because subst_lean_term drops a name from
       the active substitution as soon as it descends into a binder that
       rebinds it (see subst_lean_term's BoundedForall/Lambda cases).
    4. Wrap in BoundedForall { var = "__iter_tuple"; collection = m_lst |>.zip (n_lst); body }

  For Opt iteration the option is converted to a list via Option.toList.
*)
let rec create_prem (p : Il.Ast.prem) : term = match p.it with
  | RulePr (
    (id : Il.Ast.id),
    ([] : Il.Ast.arg list),
    (mixop : Il.Ast.mixop),
    (exp : Il.Ast.exp)
  ) ->
    let flattened_mixop_args : term list
      = match exp.it with
        | TupE exps -> List.map create_exp exps
        | _ -> [create_exp exp]
    in
    FunApp (
      Ident id.it,
      NonEmptyList.from_list_unsafe (List.map (fun arg -> Term arg) flattened_mixop_args)
    )
  | IfPr (
    (exp : Il.Ast.exp)
  ) -> create_exp exp
  | IterPr (inner_prem, iterexp) ->
      create_iter_prem inner_prem iterexp   (* dispatch to the arity-independent handler *)
  | NegPr (inner_prem) ->
      Not (create_prem inner_prem)
  | _ -> Ident "TEMPORARY_PREM"

(*
  create_iter_prem — see the large comment block above create_prem for full docs.
*)
and create_iter_prem
  (prem       : Il.Ast.prem)
  (iterexp    : Il.Ast.iterexp)
  : term =

  let (
    iter,           (* List *)
    id_exp_list
  ) = iterexp in

  (* Wrap a collection term in Option.toList if this is an Opt iteration.
     e.g. for IterPr(p, (Opt, [("x", opt_exp)])):
       opt_exp : Option α  →  Option.toList opt_exp : List α *)
  let to_list_if_opt (coll : term) : term =
    match iter with
    | Opt ->
        FunApp (
          DotProj (Ident "Option", Ident "toList"),
          NonEmptyList.from_list_unsafe [Term coll]
        )
    | _ -> coll
  in

  match id_exp_list with

  (* ── Arity 0: degenerate — no iteration, emit premise directly ───────── *)
  | [] ->
      create_prem prem

  (* ── Arity 1: ∀ id ∈ collection, body ───────────────────────────────── *)
  | [(id, coll_exp)] ->
      (*
        id.it    = "t"        the element variable name already used in prem body
        coll_exp = VarE "ts"  the list to iterate over

        No renaming needed: prem body already contains VarE "t", and we bind
        BoundedForall var = "t" — so create_prem's Ident "t" is correct as-is.

        Example:
          IterPr(RulePr("TypeOk", VarE "t"), (List, [("t", VarE "ts")]))
          →  ∀ t ∈ ts, TypeOk (t)
      *)
      let collection : term = to_list_if_opt (create_exp coll_exp) in   (* ts *)
      let body       : term = create_prem prem in                         (* TypeOk (t) *)
      BoundedForall { var = id.it; collection; body }

  (* ── Arity ≥ 2: zip collections, bind tuple var, project each id ─────── *)
  | _ ->
      (*
        Example (Pairs_ok): id_exp_list = [("v_m", VarE "m_lst"); ("v_n", VarE "n_lst")]
          n            = 2
          tuple_var    = "__iter_tuple"
          collections  = [Ident "m_lst"; Ident "n_lst"]
          zipped       = m_lst |>.zip (n_lst)        : List (m × n)
          prem_term    = create_prem prem (UNCHANGED — no renaming)
                       = Pair_ok (Ident "v_n") (Ident "v_m")
          substs       = [("v_m", __iter_tuple.1); ("v_n", __iter_tuple.2)]
          body         = Pair_ok (__iter_tuple.2) (__iter_tuple.1)
          result       = ∀ __iter_tuple ∈ m_lst |>.zip (n_lst),
                            Pair_ok (__iter_tuple.2) (__iter_tuple.1)

        We substitute directly on the original names (t1, t2, ...) rather
        than renaming to placeholders first — there is no safety benefit to
        the indirection, since id_exp_list's names are already distinct
        within this IterPr. The thing that actually has to be capture-safe
        is subst_lean_term itself: it must stop substituting a name once it
        descends into a nested binder (BoundedForall/Lambda) that rebinds
        it, which it now does (see its definition above).
      *)
      let n : int = List.length id_exp_list in          (* e.g. 2 *)
      let tuple_var = "__iter_tuple" in                  (* fresh bound variable *)

      (* 1. Build left-nested zip: ts1 |>.zip (ts2) |>.zip (ts3) ... *)
      let collections : term list =
        List.map (fun (_, e) -> to_list_if_opt (create_exp e)) id_exp_list in
      let zipped_collection : term = make_left_zip collections in

      (* 2. Translate prem as-is — no renaming. create_prem produces
            Ident "v_n", Ident "v_m", ... directly from the original names. *)
      let prem_term : term = create_prem prem in

      (* 3. Substitution: original name → make_proj i n (Ident "__iter_tuple")
            e.g. n=2 (Pairs_ok): "v_m" (i=0) → __iter_tuple.1   "v_n" (i=1) → __iter_tuple.2
                 n=3: "x" (i=0) → __iter_tuple.1.1  "y" (i=1) → __iter_tuple.1.2  "z" (i=2) → __iter_tuple.2 *)
      let substs : (string * term) list =
        List.mapi
          (fun i (id, _) ->
            ( id.it,                                  (* original name, e.g. "v_m" *)
              make_proj i n (Ident tuple_var) ))      (* __iter_tuple.1.2 etc. *)
          id_exp_list in

      (* 4. Apply substitution (capture-safe — see subst_lean_term) and
            wrap in BoundedForall *)
      let body : term = subst_lean_term substs prem_term in
      BoundedForall {
        var        = tuple_var;          (* "__iter_tuple" *)
        collection = zipped_collection;  (* ts1 |>.zip (ts2) |>.zip ... *)
        body;
      }


let append_prems_to_term (term : term) (prems : Il.Ast.prem list) : term
  
  (* TODO: it would be nice if this could be elegantly done but only for DecD *)
  (*
    ElsePr ("-- otherwise") carries no actual condition to check at runtime —
    it just marks "this is the fallback clause" for the else/else-simplification
    middlend passes. Drop it here so it never turns into a printed guard; e.g.

      def $opt_(syntax X, x1) = none  -- otherwise

    should render as a plain match arm body, not `TEMPORARY_PREM → none` or
    `True → none`.
  *)
  = let prems = List.filter (fun p -> match p.it with ElsePr -> false | _ -> true) prems in
    if prems = [] then term
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
        | TupT id_typ_list ->

            (* TODO: Check Claude-generated hash table id dedup algo *)
            let counts = Hashtbl.create 4 in
            List.iter (fun (id, _) ->
              let n = try Hashtbl.find counts id.it with Not_found -> 0 in
              Hashtbl.replace counts id.it (n + 1)
            ) id_typ_list;
            let seen = Hashtbl.create 4 in
            List.map (fun (id, typ) ->
              let name =
                if Hashtbl.find counts id.it > 1 then begin
                  let k = try Hashtbl.find seen id.it with Not_found -> 0 in
                  Hashtbl.replace seen id.it (k + 1);
                  id.it ^ "_" ^ string_of_int k
                end else id.it
              in
              BracketedBinder(ExplicitParam(
                NonEmptyList.from_list_unsafe [Ident_IOH name],
                create_typ typ
              ))
            ) id_typ_list
        | _ -> failwith "typ under typcase must be TupT!"
  in

  let params_from_quants (* (v_n : n) *)
    = List.map (
      fun q -> match q.it with
        | ExpP (id, typ) -> BracketedBinder(ExplicitParam(
          NonEmptyList.from_list_unsafe [Ident_IOH id.it;],
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

let rec create_def (def : Il.Ast.def) : command option
  = match def.it with

    | TypD (id, params, [{it = (InstD (quants, args, {it = AliasT t; _})); _}])
      -> Some (Abbrev (AbbrevAsgn {
        modifier = empty_modifier;
        id = id.it;
        signature = ([], Some (Type None));
        body = create_typ t;
      }))

    | TypD (id, params, [{it = (InstD (quants, args, {it = VariantT ts; _})); _}])
      ->
        (* (X : Type) *)
        let create_typ_binder (quant : Il.Ast.quant) : _params
          = match quant.it with
            | TypP id -> BracketedBinder(ExplicitParam(
              NonEmptyList.from_list_unsafe [Ident_IOH id.it;],
              Type None
            ))
            | _ -> failwith "only TypP should be here"
        in

        Some (Inductive {
        modifier = empty_modifier;
        id = id.it;
        signature = (
          List.map
            create_typ_binder
            params,
          
          Some (Type None)
        );
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
                    NonEmptyList.from_list_unsafe [Ident_IOH id.it;], (* TODO: disambiguate Ident *)
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
      [{it = DefD ([], [], exp, []); _}]    (* (NumE (Nat 1024)) *)
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
      id,       (* "float" *)
      params,   (*
                  (ExpP "nat" nat)
                  (ExpP "var_0" (IterT nat List))
                *)
      typ,      (* (VarT "const") *)
      []
    ) ->
      (*
        Let's say we have a definition like

        /- Axiom Definition at: doc/example/NanoWasm.spectec:136.1-136.30 -/
        opaque float (nat : Nat) (var_0 : (List Nat)) : const := opaqueDef

        corresponding to IL AST

        (DecD
          "float"
          (ExpP "nat" nat)
          (ExpP "var_0" (IterT nat List))
          (VarT "const")
          []
        )
      *)
      let signature : decl_sig (* (nat : Nat) (var_0 : (List Nat)) : const *)
        =
          List.map (
            fun p -> match p.it with
              | TypP t -> BracketedBinder(ExplicitParam(
                NonEmptyList.from_list_unsafe [Ident_IOH t.it;], (* (X : Type) *)
                Type None
              ))
              | ExpP (id, typ) -> BracketedBinder(ExplicitParam(
                NonEmptyList.from_list_unsafe [Ident_IOH id.it;], (* (v_state : state) *)
                create_typ typ
              ))
              | _ -> failwith "only ExpP or TypP should be here"
          ) params,
          create_typ typ

          
      in
      Some(Opaque {
        modifier = empty_modifier;
        id = id.it;                               (* "float" *)
        signature = signature;
        rhs = Some opaque_def;
      })
    (* | DecD (id, [], typ, clauses)
      -> None *)

      

    | DecD (
      id,     (* "local" *)
      params, (*
                (ExpP "v_state" (VarT "state"))
                (ExpP "v_localidx" (VarT "localidx"))
              *)
      typ,    (* (VarT "val") *)
      clauses (*
                (DecD
                  "local"
                  (ExpP "v_state" (VarT "state"))
                  (ExpP "v_localidx" (VarT "localidx"))
                  (VarT "val")
                  (DefD
                    (ExpP "s" (VarT "store"))
                    (ExpP "f" (VarT "frame"))
                    (ExpP "x" nat)
                    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
                    (ExpA (VarE "x"))
                    (IdxE (DotE (VarE "f") (Atom LOCALS)) (VarE "x"))
                  )
                )
              *)
    ) ->
      (*
        Let's say we have a definition like

        /- Auxiliary Definition at: doc/example/NanoWasm.spectec:82.1-82.34 -/
        def «local» (v_state : state) (v_localidx : localidx) : val :=
          match v_state with
          | .mk_state s f => ((f.LOCALS)[v_localidx]!)

        corresponding to IL AST

        (DecD
          "local"
          (ExpP "v_state" (VarT "state"))
          (ExpP "v_localidx" (VarT "localidx"))
          (VarT "val")
          (DefD
            (ExpP "s" (VarT "store"))
            (ExpP "f" (VarT "frame"))
            (ExpP "x" nat)
            (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
            (ExpA (VarE "x"))
            (IdxE (DotE (VarE "f") (Atom LOCALS)) (VarE "x"))
          )
        )

      *)


      let signature : opt_decl_sig (* (v_state : state) (v_localidx : localidx) : val *)
        =
          let params_as_binders : _params list (* (v_state : state) (v_localidx : localidx) *)
            = List.map (
              fun p -> match p.it with
                | TypP t -> BracketedBinder(ExplicitParam(
                  NonEmptyList.from_list_unsafe [Ident_IOH t.it;], (* (X : Type) *)
                  Type None
                ))
                | ExpP (id, typ) -> BracketedBinder(ExplicitParam(
                  NonEmptyList.from_list_unsafe [Ident_IOH id.it;], (* (v_state : state) *)
                  create_typ typ
                ))
                | _ -> failwith "only ExpP or TypP should be here"
            ) params
          in

          params_as_binders,
          Some (create_typ typ) (* val *)
      in

      let get_redundant_match_terms ()

      
      (* TODO: see if we should / can remove unnecessary components of match term *)
      let create_clause
        (*
          | .mk_state s f => ((f.LOCALS)[v_localidx]!)
        *)
        (clause : Il.Ast.clause)
        (params_from_parent : Il.Ast.quant list)   (*
                                              (ExpP "v_state" (VarT "state"))
                                              (ExpP "v_localidx" (VarT "localidx"))
                                            *)
        : term list * term =

          let DefD (
            quants,   (*
                        (ExpP "s" (VarT "store"))
                        (ExpP "f" (VarT "frame"))
                        (ExpP "x" nat)
                      *)
            args,     (*
                        corr. to v_state    ---- (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
                        corr. to v_localidx ---- (ExpA (VarE "x"))
                      *)
            exp,      (* (IdxE (DotE (VarE "f") (Atom LOCALS)) (VarE "x")) *)
            prems
          ) = clause.it in

          let arg_to_lhs_pattern (* .mk_state s f *)
            (arg : Il.Ast.arg)
            : term
            = match arg.it with
              | TypA ({it = VarT (x, []); _} as t) -> create_typ t
              | TypA _ -> failwith "only VarT should be here"
              | ExpA exp -> (
                match exp.it with
                  | CatE (exp1, exp2) ->
                    (* CatE (ListE [e], rest) in IL means [e] ++ rest = e :: rest.
                       Unwrap the singleton ListE so the pattern binds the element,
                       not a singleton list containing it. *)
                    let head_pat = match exp1.it with
                      | ListE [e] -> create_exp e
                      | _ -> create_exp exp1
                    in
                    BinaryInfixFunApp (
                      Term head_pat,
                      Ident "::",
                      Term (create_exp exp2)
                    )
                  | IterE (exp, _) -> create_exp exp
                  | _ -> create_exp exp
              )
              | _ -> failwith "only TypA or ExpA should be here"
          in

          
          (List.map arg_to_lhs_pattern args, append_prems_to_term (create_exp exp) prems)
      in


      let create_match_term
        (params_from_parent : Il.Ast.quant list)   (*
                                              (ExpP "v_state" (VarT "state"))
                                              (ExpP "v_localidx" (VarT "localidx"))
                                            *)
        : term list
        = 
        let collected_ids = List.map (
            fun p -> match p.it with
              | ExpP (id, typ) -> (Ident id.it : term)
              | TypP id -> (Ident id.it : term)
              | _ -> failwith "only ExpP or TypP should be here"
          ) params_from_parent
        in
        collected_ids
      in

      Some (Def (DefAsgn {
        modifier = empty_modifier;
        id = id.it;
        signature = signature;
        body = Match {
          match_terms = create_match_term params;
          cases = List.map (fun clause -> create_clause clause params) clauses;
        }
      }))
    | GramD _ -> None
    | RecD defs ->
      (
        match List.length defs with
          | 0 -> None
          | 1 -> create_def (List.hd defs)
          | _ ->
            (* TODO: refactor to make maintenance easier *)
            let is_inductive = fun def -> match def.it with
              | RelD _ -> true
              | _ -> false
            in
            let is_structure = fun def -> match def.it with
              | TypD (_, _, [{it = InstD (_, _, {it = StructT _; _}); _}]) -> true
              | _ -> false
            in
            let is_def = fun def -> match def.it with 
              | DecD (_, _, _, _ :: _) -> true   (* non-empty clauses → Def; empty clauses → Opaque, excluded *)
              | _ -> false
            in
            let is_abbrev = fun def -> match def.it with
              | TypD (_, _, [{it = InstD (_, _, {it = AliasT _; _}); _}]) -> true
              | _ -> false
            in
            let all_inductive_or_structure = List.for_all (fun def -> is_inductive def || is_structure def) defs in
            let all_abbrev_or_def = List.for_all (fun def -> is_abbrev def || is_def def) defs in
            (
              match all_inductive_or_structure, all_abbrev_or_def with
                | true, _ ->
                  let inductives = List.filter_map (fun def ->
                    match create_def def with Some (Inductive i) -> Some i | _ -> None
                  ) defs in
                  let structures = List.filter_map (fun def ->
                    match create_def def with Some (Structure s) -> Some s | _ -> None
                  ) defs in
                  Some (Mutual (MutualInductiveStructure (inductives, structures)))

                | false, true ->
                  let defs' = List.filter_map (fun def -> (* Name collision *)
                    match create_def def with Some (Def s) -> Some s | _ -> None
                  ) defs in
                  let abbrevs = List.filter_map (fun def ->
                    match create_def def with Some (Abbrev i) -> Some i | _ -> None
                  ) defs in
                  Some (Mutual (MutualDefAbbrev (defs', abbrevs)))
                | false, false -> None
            )
        )
    | HintD _ -> None
    | RelD _ -> failwith "should have been handled by earlier case"
    | TypD _ -> None


let prologue : command list =
  [
    list_ap;
    option_ap;
  ]

let create_script (il : script) : command list
  =
    let generated = List.filter_map create_def il in
    
    prologue @ generated