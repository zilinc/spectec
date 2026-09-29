open Il.Ast
open Def
open Util.Source
open Il
open Il_util

module Map = Map.Make(String)

module S = Util.Lib.State(Subst)
open S

(* For new variable names *)
let fresh_oracle = ref 0

let fresh_id (oname: string option) at : id =
  let i = !fresh_oracle in
  fresh_oracle := !fresh_oracle + 1;
  let name n onm = "__v" ^ string_of_int n ^
                   match onm with
                   | None -> ""
                   | Some nm -> "_" ^ nm
  in
  name i oname $ at

(*
let test_reld_def = RelD (test_id * test_param_list )

   * [qs] the quantification list for [ps].
   * [ps] is the least common anti-instances of the patterns of the clauses in
     [cl_substs].
   * [cl_substs] is a list of pairs of (clause, subst) that have been anti-unified.
     The clauses are the same as original, but they will be applied by the substitutions
     later, when all clauses are anti-unified. The substitutions are cumulative.
   * [cls] are the clauses to be anti-unified with [p].
*)

(*
Use premises to store the terms created by anti-unification. Convert the prem' type constructor of IfPr of exp to the branching if IfE in exp' NOTE IfE is for merging, not AU

dl is all lifted to functions. Try to combine IfPr into LetPr? subst_to_prems combines them into LetPr clauses

func_def -> func_def' -> func_clause -> clause -> prem -> IfPr/LetPr
func_def -> func_def' -> func_clause -> clause -> exp  -> IfE

QUESTIONS:
Flow appears to be:
1. Exisiting (or empty) accumulated quanitifers qs and current pattern ps, fold on new clause into it. Ig implication is that premises are quantifiers, and inserted at the end?
  1.1 If part is the same, that is the pattern, no new quantifiers.
  1.2 If different, add new quantifier. 
2. subst_to_prems the quantifiers qs back into the premises
3. 

NOTE: Just anti-unify the LHS of step rule, not premises or RHS.
Seems to be, just FuncDef
When converted to DL, the LHS is the params of the FuncDef/function. So it lifts LHS to premises
Param list is LHS vars, func_clause is LHS itself
NOTE: AU preserve all rules(or functions in DL), just lifts the LHS to a pattern, and the terms are added to the premises. See page 12 of prose_spectec paper.
QUESTION: Is it that actual DL runs on LHS/arguments recursively/with a fold?

NOTE: The preprocessing groups rules into functions (which contain lists of functions in the same group). Run AU on those within the same group.
*)

let anti_unification (dl : dl_def list) : dl_def list =
  List.map (function
    | RecDef dl' -> RecDef dl'
    | TypeDef _ as d -> d
    | FuncDef _ as d -> d 
  ) dl

let au_clause qs ps (orid, cl) =
  let DefD (qs', args, exp, prems) = cl.it in
  let ps' = ps in
  let subst = Subst.empty in
  qs', ps', (orid, cl), subst


(* 
  Look at smart constructors and combinators, like combining metadata with phrase etc, look in Xl.source, e.g. $ $$ % $>, don't be confused with Zilin's combinators
*)

let rec merge_exp qs exp1 exp2 : quant list * exp * Subst.t * Subst.t = 
  let replace_it it = { exp1 with it = it } in
  if Il.Eq.eq_exp exp1 exp2 then
    qs, exp1, Subst.empty, Subst.empty
  else
    match exp1.it, exp2.it with
    (*
      1. merge_exp takes two quant lists, ONE(?) exp, no subst. Returns one quant lists (the environment), two exp, and addititional quantifiers? 
      2. In the case of exp1 and exp2 matching VarE, use VarE id1 as the anti-instance
      3. Given 3 exp: (e11, e12) (e21, e22) e3, AU first two exp getting anti-instances (v1, v2) 
        3.1. Get TWO subts, v1 |-> e11 and v2 |-> e12, v1 |-> e21 and v2 |-> e22
        3.2. AU (v1, v2) with e3. Get anti-instance v3 and two substs, s.t. v3 |-> (e11, e12) and v3 |-> (e21, e22) 
        3.3. Composing substs is combining their key-value stores, BUT also requires you apply substs to anti-patterns to maintain invariant that substs return expression from original, never newly quantified variables. Once you've composed the substs, you have v3 |-> (e11, e12), v3 |-> (e21,e22) and v3 |-> e3 in the end, and you only need the new quant v3. You can see v1 and v2 are no longer needed. 
    *)
    (* 
      Reason about invariant -> No information is lost. 
      What are the binders inside ex'
      qs should have coresondence to combined substs
      Domain of substituion of qs and substs should be the same
      Union of substs and qs
      Within single merge_exp call, shouldnt have smth like x->a and a->3 in substs BUT will happen when applied as a fold
    *)
    (* 
      1. See animate main for oracle style __ new var capture avoiding substitution function
      2. See below, return quant list is new variables, not taking in new environment from previous call
      
      au : (quant list, quant list, e, e) -> (quant list, e, subst, subst)
      au (qs1, qs2, e1, e2) = match e1.it, e2.it with
      | vare v1, vare v2 -> ..
      | liste es1, liste es2 -> ...
      | ...
      | _, _ -> let v = fresh_id in
                (mk_quants (v, e1.note), mk_subst [(v, e1)], mk_subst [(v, e2)])

      list.fold_left (fun (substs, qs1, e1) (qs2, e2) ->
        let (qs', e', s1, s2) = au (qs1, qs2, e1, e2) in
        (list.map (apply s1) substs @ [s2], qs', e')
      ) (([] : subst list), hd qss, hd es) (list.combine (tail qss) (tail es))
    *)
    | VarE id1, VarE _ -> 
      (* 
        OLD: Investigate il2al/unify.ml/overlap line ~130, |> replace_it. Seems to handle most cases. 
              Note: Seems they mostly have equality of first element, probably value. 
              |> line equal to replace_it (UnE (unop1, nt1, overlap env e1 e2)). 
        QUESTIONS:
          1. Should I make new quant ExpP or some other quant (esp wrt to constructors that need a typ payload), if ExpP is exp1.note type correct
          2. Currently use $ to fill in note : 'b and use exp1.at, is this right? 
          3. What should reg (region) be? reg currently probably wrong.
          4. Is using replace_it to create exp correct in UnE case? Currently line 143-144
          5. In example code (line 122) why is only s1 applied but s2 appended?
          6. For BinE case (line 150), is logic correct, esp:
            6.1 Using merge_exp recursively on e1, e2, e1', e2'
            6.2 Is merging results correct, including combined_substs, and qs_au @ qs_au' (this seems wrong)
            6.3 Usage of replace_it in line 158
        Note: instead of exp1_payload and exp2_payload names, use math notation, type of payload is just id, usu identifier just use v or x, similarly for BoolE, name smth like b, write a function in a mathematical sense, small but meaningful, usually indicating type
        1. Can make this more generalisable by making VarE v, _ _, because it is trivially generalisable. Other way round too, if it is _ _, VarE. 
        2. Do not make a new quant in this case because it is not a new var, you are reusing one of the VarEs
        3. Change fresh_quant_id name too, see Note: above 
        4. Region try to maintain accuracy for debugging, see over_region utils/source.ml
      *)
      [], exp1, Subst.add_varid Subst.empty id1 exp2, Subst.empty
    | VarE _, VarE id2 -> (* <- Think about this wrt what Zilin said about VarE cases*)
      [], exp2, Subst.empty, Subst.add_varid Subst.empty id2 exp2 
    | BoolE b1, BoolE b2 ->
      let id' = fresh_id (Some "new_quant") exp1.at in
      let param' = (ExpP (id', exp1.note)) $ exp1.at in 
      let exp' : exp = (VarE id') |> replace_it in
      [param'], exp', Subst.add_varid Subst.empty id' exp1, Subst.add_varid Subst.empty id' exp2
    | NumE _, NumE _ ->
      let id' = fresh_id (Some "new_quant") exp1.at in
      let param' = (ExpP (id', exp1.note)) $ exp1.at in 
      let exp' : exp = (VarE id') |> replace_it in
      [param'], exp', Subst.add_varid Subst.empty id' exp1, Subst.add_varid Subst.empty id' exp2
    | TextE _, TextE _ -> 
      let id' = fresh_id (Some "new_quant") exp1.at in
      let param' = (ExpP (id', exp1.note)) $ exp1.at in 
      let exp' : exp = (VarE id') |> replace_it in
      [param'], exp', Subst.add_varid Subst.empty id' exp1, Subst.add_varid Subst.empty id' exp2
    | UnE (unop1, nt1, e1), UnE (unop2, nt2, e2) when unop1 = unop2 && nt1 = nt2 ->
      let (qs_au, exp_au, subst1, subst2) = merge_exp qs e1 e2 in
      let exp' : exp = (UnE (unop1, nt1, exp_au)) |> replace_it in
      qs_au, exp', subst1, subst2
    | BinE (binop1, nt1, e1, e1'), BinE (binop2, nt2, e2, e2') when binop1 = binop2 && nt1 = nt2 ->
      let (qs_au, exp_au, subst1, subst2) = merge_exp qs e1 e2 in
      let (qs_au', exp_au', subst1', subst2') = merge_exp qs e1' e2' in
      let combined_subst1 = Subst.union subst1 subst1' in 
      let combined_subst2 = Subst.union subst2 subst2' in
      let exp' : exp = (BinE (binop1, nt1, exp_au, exp_au')) |> replace_it in
      qs_au @ qs_au', exp', combined_subst1, combined_subst2
    | CmpE (cmpop1, nt1, e1, e1'), CmpE (cmpop2, nt2, e2, e2') when cmpop1 = cmpop2 && nt1 = nt2 -> 
      let (qs_au, exp_au, subst1, subst2) = merge_exp qs e1 e2 in
      let (qs_au', exp_au', subst1', subst2') = merge_exp qs e1' e2' in
      let combined_subst1 = Subst.union subst1 subst1' in 
      let combined_subst2 = Subst.union subst2 subst2' in
      let exp' : exp = (CmpE (cmpop1, nt1, exp_au, exp_au')) |> replace_it in
      qs_au @ qs_au', exp', combined_subst1, combined_subst2
    | TupE es1, TupE es2 when List.length es1 = List.length es2 ->
      let zipped_exps = List.map2 (merge_exp qs) es1 es2 in 
      let qs_list, exp_list, subst1_list, subst2_list = Util_ocaml.unzip4 zipped_exps in
      let combined_subst1 = List.fold_left (Subst.union) Subst.empty subst1_list in
      let combined_subst2 = List.fold_left (Subst.union) Subst.empty subst2_list in 
      List.concat qs_list, TupE exp_list  |> replace_it, combined_subst1, combined_subst2
    | ProjE (e1, i1), ProjE (e2, i2) when i1 = i2 -> 
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in 
      qs_au, ProjE (exp_au, i1) |> replace_it, subst1, subst2 
    | CaseE (mixop1, e1), CaseE (mixop2, e2) when Eq.eq_mixop mixop1 mixop2 -> 
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in 
      qs_au, CaseE (mixop1, exp_au) |> replace_it, subst1, subst2 
    | UncaseE (e1, mixop1), UncaseE (e2, mixop2) when Eq.eq_mixop mixop1 mixop2 -> 
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in 
      qs_au, CaseE (mixop1, exp_au) |> replace_it, subst1, subst2 
    | OptE (Some e1), OptE (Some e2) ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in 
      qs_au, OptE (Some exp_au) |> replace_it, subst1, subst2 
    | TheE exp1, TheE exp2 ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs exp1 exp2 in 
      qs_au, TheE (exp_au) |> replace_it, subst1, subst2
    | StrE efs1, StrE efs2 when 
      List.length efs1 = List.length efs2 && 
      List.for_all2 (fun (a1, _) (a2, _) -> Il.Eq.eq_atom a1 a2) efs1 efs2 ->
      let zipped = List.map2 
        (fun (a, e1') (_, e2') ->
          let qs_au, exp_au, s1, s2 = merge_exp qs e1' e2' in
          (a, qs_au, exp_au, s1, s2)
        ) 
        efs1 efs2 in
      let qs_list = List.map (fun (_, q, _, _, _) -> q) zipped in
      let efs' = List.map (fun (a, _, e, _, _) -> (a, e)) zipped in
      let subst1_list = List.map (fun (_, _, _, s1, _) -> s1) zipped in
      let subst2_list = List.map (fun (_, _, _, _, s2) -> s2) zipped in
      let combined_subst1 = List.fold_left Subst.union Subst.empty subst1_list in
      let combined_subst2 = List.fold_left Subst.union Subst.empty subst2_list in
      List.concat qs_list, StrE efs' |> replace_it, combined_subst1, combined_subst2
    | DotE (e1, atom1), DotE (e2, atom2) when Il.Eq.eq_atom atom1 atom2 ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in
      qs_au, DotE (exp_au, atom1) |> replace_it, subst1, subst2
    | CompE (e1, e1'), CompE (e2, e2') ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in
      let qs_au', exp_au', subst1', subst2' = merge_exp qs e1' e2' in
      qs_au @ qs_au', CompE (exp_au, exp_au') |> replace_it, Subst.union subst1 subst1', Subst.union subst2 subst2'
    | ListE es1, ListE es2 when List.length es1 = List.length es2 ->
      let zipped = List.map2 (merge_exp qs) es1 es2 in
      let qs_list, exp_list, subst1_list, subst2_list = Util_ocaml.unzip4 zipped in
      let combined_subst1 = List.fold_left Subst.union Subst.empty subst1_list in
      let combined_subst2 = List.fold_left Subst.union Subst.empty subst2_list in
      List.concat qs_list, ListE exp_list |> replace_it, combined_subst1, combined_subst2
    | LiftE e1, LiftE e2 ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in
      qs_au, LiftE exp_au |> replace_it, subst1, subst2
    | MemE (e1, e1'), MemE (e2, e2') ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in
      let qs_au', exp_au', subst1', subst2' = merge_exp qs e1' e2' in
      qs_au @ qs_au', MemE (exp_au, exp_au') |> replace_it,
      Subst.union subst1 subst1', Subst.union subst2 subst2'
    | LenE e1, LenE e2 ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in
      qs_au, LenE exp_au |> replace_it, subst1, subst2
    | CatE (e1, e1'), CatE (e2, e2') ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in
      let qs_au', exp_au', subst1', subst2' = merge_exp qs e1' e2' in
      qs_au @ qs_au', CatE (exp_au, exp_au') |> replace_it,
      Subst.union subst1 subst1', Subst.union subst2 subst2'
    | IdxE (e1, e1'), IdxE (e2, e2') ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in
      let qs_au', exp_au', subst1', subst2' = merge_exp qs e1' e2' in
      qs_au @ qs_au', IdxE (exp_au, exp_au') |> replace_it,
      Subst.union subst1 subst1', Subst.union subst2 subst2'
    | SliceE (e1, e1', e1''), SliceE (e2, e2', e2'') ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in
      let qs_au', exp_au', subst1', subst2' = merge_exp qs e1' e2' in
      let qs_au'', exp_au'', subst1'', subst2'' = merge_exp qs e1'' e2'' in
      qs_au @ qs_au' @ qs_au'', SliceE (exp_au, exp_au', exp_au'') |> replace_it, Subst.union (Subst.union subst1 subst1') subst1'', Subst.union (Subst.union subst2 subst2') subst2''
    | UpdE (e1, path1, e1'), UpdE (e2, path2, e2') when Il.Eq.eq_path path1 path2 ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in
      let qs_au', exp_au', subst1', subst2' = merge_exp qs e1' e2' in
      qs_au @ qs_au', UpdE (exp_au, path1, exp_au') |> replace_it,
      Subst.union subst1 subst1', Subst.union subst2 subst2'
    | ExtE (e1, path1, e1'), ExtE (e2, path2, e2') when Il.Eq.eq_path path1 path2 ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in
      let qs_au', exp_au', subst1', subst2' = merge_exp qs e1' e2' in
      qs_au @ qs_au', ExtE (exp_au, path1, exp_au') |> replace_it,
      Subst.union subst1 subst1', Subst.union subst2 subst2'
    | IfE (e1, e1', e1''), IfE (e2, e2', e2'') ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in
      let qs_au', exp_au', subst1', subst2' = merge_exp qs e1' e2' in
      let qs_au'', exp_au'', subst1'', subst2'' = merge_exp qs e1'' e2'' in
      qs_au @ qs_au' @ qs_au'', IfE (exp_au, exp_au', exp_au'') |> replace_it,
      Subst.union (Subst.union subst1 subst1') subst1'',
      Subst.union (Subst.union subst2 subst2') subst2''
    | CallE (id1, args1), CallE (id2, args2) when Il.Eq.eq_id id1 id2 ->
      let merge_arg a1 a2 =
        match a1.it, a2.it with
        | ExpA ea1, ExpA ea2 ->
          let qs_au, exp_au, subst1, subst2 = merge_exp qs ea1 ea2 in
          qs_au, (ExpA exp_au $ a1.at), subst1, subst2
        | TypA _, TypA _ | DefA _, DefA _ | GramA _, GramA _ when Il.Eq.eq_arg a1 a2 ->
          [], a1, Subst.empty, Subst.empty
        | _ -> failwith "merge_exp: cannot anti-unify CallE argument"
      in
      let zipped = List.map2 merge_arg args1 args2 in
      let qs_list, args_list, subst1_list, subst2_list = Util_ocaml.unzip4 zipped in
      let combined_subst1 = List.fold_left Subst.union Subst.empty subst1_list in
      let combined_subst2 = List.fold_left Subst.union Subst.empty subst2_list in
      List.concat qs_list, CallE (id1, args_list) |> replace_it,
      combined_subst1, combined_subst2
    | IterE (e1, iterexp1), IterE (e2, iterexp2) when Il.Eq.eq_iterexp iterexp1 iterexp2 ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in
      qs_au, IterE (exp_au, iterexp1) |> replace_it, subst1, subst2
    | CvtE (e1, nt1, nt1'), CvtE (e2, nt2, nt2') when nt1 = nt2 && nt1' = nt2' ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in
      qs_au, CvtE (exp_au, nt1, nt1') |> replace_it, subst1, subst2
    | SubE (e1, typ1, typ1'), SubE (e2, typ2, typ2')
      when Il.Eq.eq_typ typ1 typ2 && Il.Eq.eq_typ typ1' typ2' ->
      let qs_au, exp_au, subst1, subst2 = merge_exp qs e1 e2 in
      qs_au, SubE (exp_au, typ1, typ1') |> replace_it, subst1, subst2
    | _, _ ->
      let id' = fresh_id (Some "new_quant") exp1.at in
      let param' = (ExpP (id', exp1.note)) $ exp1.at in
      let exp' : exp = (VarE id') |> replace_it in
      [param'], exp', Subst.add_varid Subst.empty id' exp1, Subst.add_varid Subst.empty id' exp2

let au_clauses2 (cl1 : func_clause) (cl2 : func_clause)
    : param list * func_clause * func_clause * Subst.t * Subst.t =
  let (_orid1, c1) = cl1 in 
  let (_orid2, c2) = cl2 in 
  let DefD (_qs1, args1, _exp1, _prems1) = c1.it in 
  let DefD (_qs2, args2, _exp2, _prems2) = c2.it in

  if Il.Eq.eq_list Il.Eq.eq_arg args1 args2 then 
    [], cl1, cl2, Subst.empty, Subst.empty 
  else
    [], cl1, cl2, Subst.empty, Subst.empty
  
let compose_substs (new_subst : Subst.t) (old_subst : Subst.t) : Subst.t =
  Subst.Map.to_list new_subst.varid
  |> List.fold_left
       (fun acc (v, e) -> 
        let id : id = v $ no_region in 
        Subst.add_varid acc id (Subst.subst_exp old_subst e))
       Subst.empty

let au (es : exp list) : quant list * exp * Subst.t list =
  match es with
  | [] -> invalid_arg "anti-unification expression list arg is empty"
  | [e] -> [], e, [Subst.empty]
  | e0 :: es' ->
    let qs, tmpl, substs =
      List.fold_left
        (fun (qs_acc, tmpl_acc, substs_acc) e_next ->
          let qs', tmpl', s_acc, s_next = merge_exp qs_acc tmpl_acc e_next in
          (*
            TODO: Note 
              1. Using note above, apply and compose substs. One example, qs currently returns empty. See print_endline in each fold output. 
              2. Further: Introduce the new exp as premises <- Current if AU works according to Zilin
            QUESTIONS:
              1. Right now for Step_read/load, all LHS of equality (understood to be step LHS) are the same shape in the DL, is that right?
          print_endline "== New fold step au_exp print";
          print_endline (Il.Print.string_of_exp tmpl_acc); 
          *)
          print_endline "=== Printing one AU pass";
          print_endline (Il.Subst.string_of_subst s_acc);
          print_endline (Il.Subst.string_of_subst s_next);
          let substs_acc' = List.map (compose_substs s_acc) substs_acc in
          List.iter print_endline (List.map Il.Subst.string_of_subst (substs_acc @ [s_next]));
          qs', tmpl', substs_acc @ [s_acc] @ [s_next])
        ([], e0, [Subst.empty])
        es'
    in
    qs, tmpl, substs

let rec collect_func_defs_named (name : string) (dl : dl_def list) : func_def list =
  List.concat_map (function
    | FuncDef def ->
      let (id, _osubid, _params, _typ, _fcs, _opartial) = def.it in
      if id.it = name then [def] else []
    | RecDef dl' -> collect_func_defs_named name dl'
    | TypeDef _ -> []
  ) dl

let lhs_of_clause ((_oid, cl) : func_clause) : exp =
  match cl.it with
  | DefD (_qs, [{ it = ExpA e; _ }], _exp, _prems) -> e
  | DefD (_qs, args, _exp, _prems) ->
    failwith (Printf.sprintf
      "lhs_of_clause: expected a single ExpA argument, got %d args at %s"
      (List.length args) (string_of_region cl.at))

let step_lhs_exps name (dl : dl_def list) : exp list =
  collect_func_defs_named name dl
  |> List.concat_map (fun def ->
       let (_id, _osubid, _params, _typ, fcs, _opartial) = def.it in
       List.map lhs_of_clause fcs)

let au_step (name : string) (dl : dl_def list) : quant list * exp * Subst.t list =
  match step_lhs_exps name dl with
  | [] -> invalid_arg "No clauses found in au_step."
  | es -> 
      List.iter print_endline (List.map Il.Print.string_of_exp es);
      au es

let subst_to_prems qs (subst : Subst.t) : prem list =
  let vsubst = subst.varid |> Subst.Map.to_list in
  let qs' = List.filter (fun q -> match q.it with
  | ExpP (v, t) -> not (Subst.Map.mem v.it subst.varid)
  | _ -> false
  ) qs in
  List.map (fun (x, e) -> LetPr (qs', e, varE ~note:e.note x) $ no) vsubst

let rec au_clauses' qs ps cl_substs cls : func_clause list = match cls with
| [] -> (* Apply the respective substitution to each clause. *)
  List.map (fun ((orid, cl), subst) ->
    let DefD (qs', args, exp, prems) = cl.it in
    let qs'' = qs in
    let args'' = args in
    let prems' = subst_to_prems qs' subst @ prems in
    (orid, DefD (qs'', args'', exp, prems') $ cl.at)
  ) cl_substs
| [cl] -> [cl]
| cls -> cls


(*
let au_clauses cls : func_clause list = match cls with
| [] -> []
| [cl] -> [cl]
| cl1 :: cl2 :: cls -> let p12, cl1', cl2', subst1, subst2 = au_clauses2 cl1 cl2 in
                       au_clauses' p12 [(cl1', subst1); (cl2', subst2)] cls
*)