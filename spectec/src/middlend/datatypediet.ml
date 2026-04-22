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


let max_cases = 50

open Il.Ast
open Util.Source
open Xl.Mixop

(* module StringMap = Map.Make(String) *)
module MixopMap = Map.Make(struct type t = unit mixop let compare = compare end)

let get_fathertype id sontype =
  match sontype.it with
  | VarT (_, args) -> { sontype with it = VarT (id $ no_region, args) }
  | _ -> failwith "should be variant type"


let rec transform_exp acc exp =
  let f e = { exp with it = e } in
  let te = transform_exp acc in
  match exp.it with
  | VarE _ (* TODO: can VarE be a type constructor? *)
    | BoolE _ | NumE _ | TextE _ | OptE None -> exp
  | UnE (u, o, exp) -> f (UnE (u, o, te exp))
  | BinE (b, o, e1, e2) -> f (BinE (b, o, te e1, te e2))
  | CmpE (c, o, e1, e2) -> f (CmpE (c, o, te e1, te e2))
  | TupE es -> f (TupE (List.map (te) es))
  | ProjE (e, i) -> f (ProjE (te e, i))
  | CaseE (id, e) when MixopMap.mem id acc ->
     let fathername, fathertypeid = MixopMap.find id acc in
     let fathertype = get_fathertype fathertypeid exp.note in
     f (CaseE (fathername,
               { it = CaseE (id, te e) ; at = exp.at ; note = fathertype }))
  | CaseE (a, e) -> f (CaseE (a, te e)) 

(*  | CaseE (Atom { it = Xl.Atom.Atom id ; at; note } , e) ->
     f (CaseE (Atom { it = Xl.Atom.Atom id ; at ; note } , te e))
  | CaseE _ -> failwith "bad caseE constructor name" *)
  | UncaseE _ -> failwith "Uncase should have been removed"
  | OptE (Some e) -> f (OptE (Some (te e)))
  | TheE e -> f (TheE (te e))
  | StrE fields -> f (StrE (List.map (fun (field, e) -> (field, te e)) fields))
  | DotE (e, field) -> f (DotE (te e, field))
  | CompE (e1, e2) -> f (CompE (te e1, te e2))
  | ListE es -> f (ListE (List.map te es))
  | LiftE e -> f (LiftE (te e))
  | MemE (e1, e2) -> f (MemE (te e1, te e2))
  | LenE e -> f (LenE (te e))
  | CatE (e1, e2) -> f (CatE (te e1, te e2))
  | IdxE (e1, e2) -> f (IdxE (te e1, te e2))
  | SliceE (e1, e2, e3) -> f (SliceE (te e1, te e2, te e3))
  | UpdE (e1, p, e2) -> f (UpdE (te e1, transform_path acc p, te e2))
  | ExtE (e1, p, e2) -> f (ExtE (te e1, transform_path acc p, te e2))
  | IfE (e1, e2, e3) -> f (IfE (te e1, te e2, te e3))
  | CallE (id, args) -> f (CallE (id, List.map (transform_arg acc) args))
  | IterE (id, itexp) -> f (IterE (id, transform_iterexp acc itexp))
  | CvtE (e, t1, t2) -> f (CvtE (te e, t1, t2))
  | SubE (e, t1, t2) -> f (SubE (te e, t1, t2))

and transform_arg acc arg =
  match arg.it with
  | ExpA e -> { arg with it = ExpA (transform_exp acc e) }
  | TypA _ | DefA _ -> arg 
  | GramA sym -> { arg with it = GramA (transform_sym acc sym) }

and transform_iterexp acc (it, exps) =
  (it, List.map (fun (id, exp) -> (id, transform_exp acc exp)) exps)

and transform_sym acc sym =
  match sym.it with
  | VarG (id, args) -> { sym with it = VarG (id, List.map (transform_arg acc) args) }
  | NumG _ | TextG _ | EpsG -> sym
  | SeqG syms -> { sym with it = SeqG (List.map (transform_sym acc) syms) }
  | AltG syms -> { sym with it = AltG (List.map (transform_sym acc) syms) } 
  | RangeG (sym1, sym2) -> { sym with it = RangeG (transform_sym acc sym1, transform_sym acc sym2) }
  | IterG (sym1, itexp) -> { sym with it = IterG (transform_sym acc sym1, transform_iterexp acc itexp) }
  | AttrG (exp, sym1) -> { sym with it = AttrG (transform_exp acc exp, transform_sym acc sym1) }

and transform_path acc path =
  match path.it with
  | RootP -> path
  | IdxP (p,e) -> { path with it = IdxP (transform_path acc p, transform_exp acc e) }
  | SliceP (p, e1, e2) -> { path with it = SliceP (transform_path acc p, transform_exp acc e1, transform_exp acc e2) }
  | DotP (p, a) -> { path with it = DotP (transform_path acc p, a) }



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
  match clause.it with
  | DefD (quants, args, exp, prems) -> {clause with it = DefD (quants, List.map (transform_arg acc) args, transform_exp acc exp, List.map (transform_prem acc) prems)}

let transform_prod acc prod =
  match prod.it with
  | ProdD (quants, sym, exp, prems) -> { prod with it = ProdD (quants, transform_sym acc sym, transform_exp acc exp, List.map (transform_prem acc) prems)}

let sqrt_int n =
  int_of_float (sqrt (float_of_int n))

let rec is_recursive_type ids t =
  match t.it with
  | VarT (id, args) -> List.mem id.it ids || List.exists (is_recursive_arg ids) args 
  | BoolT | NumT _ | TextT -> false
  | TupT ts -> List.exists (fun (_, t) -> is_recursive_type ids t) ts
  | IterT (t, _) -> is_recursive_type ids t
and is_recursive_arg ids arg =
  match arg.it with
  | ExpA _e -> false (* TODO: technically e could contain a type *)
  | TypA t -> is_recursive_type ids t
  | DefA _ -> false 
  | GramA _sym -> false (* TODO: technically sym could contain a type *)


let is_recursive ids typecase =
  match typecase with
  | (_, (t, _,_),  _) ->
     is_recursive_type ids t

let split_constructor id l1 quants l2 typecases ids at1 at2 at3 =
  let n = List.length typecases in
  let nb_cases, max_constr_per_case, resplit =
    if max_cases * max_cases < n then
      if (n / max_cases) * max_cases < n then
        n / max_cases + 1, max_cases, true
      else n / max_cases, max_cases, true
    else let m = sqrt_int n in
         if m * m < n then
           m + 1, m + 1, false
         else m, m, false in
  let yes_rec, non_rec = List.partition (is_recursive ids) typecases in
  let rec aux acc done_cases nexti current_case current_case_count typecases =
    if current_case_count = max_constr_per_case then
      aux acc ((nexti, current_case) :: done_cases) (nexti + 1) [] 0 typecases
    else
      match typecases with
      | [] -> acc, done_cases, nexti, current_case, current_case_count
      | (casename, typ, hints) :: q ->
(*         (match casename with
          | Atom _ -> Printf.printf "it's an atom!\n" 
          | Seq l -> Printf.printf "it's a seq on length %d\n" (List.length l)
          | _ -> Printf.printf "it's something else!\n"); *)
         let fathername =
           (* Seq [ *) Atom { it = Xl.Atom.Atom (id.it ^ "subcase" ^ string_of_int nexti) ;
                        at = no_region ;
                        note = Xl.Atom.info "automatically generated subcase during datatype dieting" } (* ;
                 Arg () ] *) in
         (*         Printf.printf "arity of %ssubcase%d is %d\n" id.it nexti (arity fathername);  *)
         aux (MixopMap.add casename (fathername, id.it ^ "subtype" ^ string_of_int nexti) acc)
           done_cases nexti
           ((casename, typ, hints) :: current_case)
           (current_case_count + 1) q in
  let acc, non_recs, nexti, current_case, current_case_count =
    aux MixopMap.empty [] 0 [] 0 non_rec in
  let acc, yes_recs, nexti, current_case, current_case_count =
    aux acc [] nexti current_case current_case_count yes_rec in
  let yes_recs, nb_cases' =
    if current_case = [] then yes_recs, nexti else yes_recs @ [nexti, current_case], nexti + 1 in
  if nexti * max_constr_per_case + current_case_count = n && nb_cases' = nb_cases then ()
  else failwith "arithmetic error";
  let non_recs = List.map (fun (i, typecases) ->
                     { it = TypD (id.it ^ "subtype" ^ string_of_int i $ no_region, l1, [ { it = InstD (quants, l2, { it = VariantT typecases ; at = at1 ; note = ()}) ;
                                                                      at = at2 ; note = () } ]) ; at = at3 ; note = () }) non_recs in
  let yes_recs = List.map (fun (i, typecases) ->
                     { it = TypD (id.it ^ "subtype" ^ string_of_int i $ no_region, l1, [ { it = InstD (quants, l2, { it = VariantT typecases ; at = at1 ; note = ()}) ;
                                                                      at = at2 ; note = () } ]) ; at = at3 ; note = () }) yes_recs in
  let main_typecases = List.init nb_cases
                         (fun i -> (Seq [Atom { it = Xl.Atom.Atom (id.it ^ "subcase" ^ string_of_int i) ;
                                                at = no_region;
                                                note = Xl.Atom.info "automatically generated subcase during datatype dieting" };
                                         Arg ()],
                                    ((VarT (id.it ^ "subtype" ^ string_of_int i $ no_region, [])) $ no_region, [], []), [])) in
  let main_case =
    { it = TypD (id, l1, [
                     { it = InstD (quants, l2,
                                   { it = VariantT main_typecases;
                                     at = at1 ; note = () }) ; at = at2 ; note = () } ]) ; at = at3 ; note = () } in
  let epilog = [] (* TODO: want to define fun def so only need to replace in pattern matching? *) in
                   
  non_recs, main_case :: yes_recs, epilog, acc, if resplit then [(id, l1, quants, l2, main_typecases, at1, at2, at3)] else []


let get_constructors def =
  match def.it with
  | TypD (id, l1, [{ it = InstD (quants, l2, { it = VariantT typecases ; at = at1 ; _ }) ; at = at2 ; _ }]) -> Some (id, l1, quants, l2, typecases, at1, at2, def.at)
  | TypD (_, _, { it = InstD (_, _, {it = VariantT _ ; _}) ; _} :: _) -> failwith "ill-formed datatype definition"
  | TypD _ -> None
  | _ -> failwith "should be a type definition"

let get_some = function
  | Some x -> x
  | None -> failwith "non-datatype defined mutually recursively with a datatype"



let transform_typ_defs acc def (* original definition, in case no change is needed *) defs =
  let constructors = List.map get_constructors defs in
  if List.for_all (function None -> true | _ -> false) constructors then acc, [def] else
    let constructors = List.map get_some constructors in
    if List.for_all (fun (_,_,_,_,l,_,_,_) -> List.length l <= max_cases) constructors then acc, [def] else
      let ids = List.map (fun (id, _,_,_,_,_,_,_) -> id.it) constructors in
      let rec aux = function
        | [] -> [], [], [], MixopMap.empty
        | (id, l1, quants, l2, typecases, at1, at2, at3) :: q when List.length typecases <= max_cases ->
           let prelude, mutrec, epilog, acc = aux q in
           prelude, { it = TypD (id, l1, [ { it = InstD (quants, l2, { it = VariantT typecases ; at = at1 ; note = ()}) ;
                                             at = at2 ; note = () } ]) ; at = at3 ; note = () } :: mutrec, epilog, acc
        | (id, l1, quants, l2, typecases, at1, at2, at3) :: q ->
           let prelude', mutrec', epilog', acc', resplit = split_constructor id l1 quants l2 typecases ids at1 at2 at3 in
           let prelude, mutrec, epilog, acc = aux (resplit @ q) in
           prelude' @ prelude, mutrec' @ mutrec, epilog' @ epilog,
           MixopMap.union (fun _ _ _ -> failwith "same constructor in multiple datatype definitions") acc acc' in
      let prelude, mutrec, epilog, acc = aux constructors in
      let mutrec = match mutrec with
        | [def] -> def
        | _ -> { it = RecD mutrec ; at = def.at ; note = () } in
      acc, prelude @ [mutrec] @ epilog
    
    
  


let rec transform_def acc def =
  match def.it with
  | TypD _ -> transform_typ_defs acc def [def]
  | RelD (id, params, op, t, rules) ->  acc, [{def with it = RelD (id, params, op, t, List.map (transform_rule acc) rules)}]
  | DecD (id, params, t, clauses) -> acc, [{def with it = DecD (id, params, t, List.map (transform_clause acc) clauses)}]
  | GramD (id, params, t, prods) -> acc, [{def with it = GramD (id, params, t, List.map (transform_prod acc) prods)}]
  | RecD defs ->
     (match defs with
      | { it = TypD _ ; _ } :: _ -> transform_typ_defs acc def defs
      | _ -> let acc, defs = List.fold_left (fun (acc, defs) def ->
                                 let acc, defs' = transform_def acc def in
                                 acc, defs' @ defs) (acc, []) defs in
             acc, [{def with it = RecD (List.rev defs)}])
  | HintD _ -> acc, [def]



let transform script =
  let (_, defs) = List.fold_left (fun (acc, defs) def ->
                      let (acc, def) = transform_def acc def in
                      acc, def :: defs) (MixopMap.empty, []) script in
  List.flatten (List.rev defs)
