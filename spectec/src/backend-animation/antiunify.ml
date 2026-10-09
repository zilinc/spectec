open Il.Ast
open Def
open Util.Source
open Il
open Il_util

module Map = Map.Make(String)

module S = Util.Lib.State(Subst)
open S

let target_names = ["Step"; "Step_read"; "Step_pure"]

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

let rec merge_exp qs exp1 exp2 : quant list * exp * Subst.t * Subst.t = 
  let replace_it it = { exp1 with it = it } in
  if Il.Eq.eq_exp exp1 exp2 then
    [], exp1, Subst.empty, Subst.empty
  else
    match exp1.it, exp2.it with
    | VarE id1, VarE _ -> 
      [], exp1, Subst.add_varid Subst.empty id1 exp2, Subst.empty
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
    (*
      Note: Check StrE, TupE, check as they allow dependent tuple and dependent records, may need to modify the types as well
    *)
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
          let substs_acc' = List.map (compose_substs s_acc) substs_acc in
          qs', tmpl', substs_acc' @ [s_next])
        ([], e0, [Subst.empty])
        es'
    in
    qs, tmpl, substs

let lhs_of_clause ((_oid, cl) : func_clause) : exp =
  match cl.it with
  | DefD (_qs, [{ it = ExpA e; _ }], _exp, _prems) -> e
  | DefD (_qs, args, _exp, _prems) ->
    failwith (Printf.sprintf
      "lhs_of_clause: expected a single ExpA argument, got %d args at %s"
      (List.length args) (string_of_region cl.at))

let subst_to_prems qs (subst : Subst.t) : prem list =
  let vsubst = subst.varid |> Subst.Map.to_list in
  let qs' = List.filter (fun q -> match q.it with
  | ExpP (v, t) -> not (Subst.Map.mem v.it subst.varid)
  | _ -> false
  ) qs in
  List.map (fun (x, e) -> LetPr (qs', varE ~note:e.note x, e) $ no) vsubst

let sub_lhs_arg (new_exp : exp) (argl : arg list) : arg list = 
  match argl with 
  | [{ it = ExpA e; _ } as arg] -> [{ arg with it = ExpA new_exp }]
  | _ ->
    failwith (Printf.sprintf
      "lhs_of_clause: expected a single ExpA argument, got %d args"
      (List.length argl))

let general_sub (new_exp : exp) (new_qs : quant list) (subst : Subst.t) (fc : func_clause) : func_clause = 
  let (_osubid, cl) = fc in 
  let new_prems = subst_to_prems new_qs subst in 
  let DefD (qsl, argl, exp, pl) = cl.it in
  (_osubid, 
  { cl with it = DefD (new_qs @ qsl, sub_lhs_arg new_exp argl, exp, new_prems @ pl)})

let rec sub_func_clauses (new_exp : exp) (new_qs : quant list) (substs : Subst.t list) (fcs : func_clause list) : func_clause list =
  match substs, fcs with 
  | [sub1], [fc1] -> [general_sub new_exp new_qs sub1 fc1] 
  | sub1::subs, fc1::fcs' -> [general_sub new_exp new_qs sub1 fc1] @ sub_func_clauses new_exp new_qs subs fcs' 
  | _, _ -> failwith (Printf.sprintf
      "add_prems: failure, list diff lengths, substs length: %d, dls length: %d"
      (List.length substs) (List.length fcs))

let rec au_rule (dl : dl_def) : dl_def  =
  match dl with
  | FuncDef def -> 
    (*
    TODO:
      1. Extract func_clauses
      2. Transform into list of LHS exp
      3. Run AU on it
      4. Sub those back in
    *)
    let (id, osubid, params, typ, fcs, opartial) = def.it in 
    let lhses = List.map lhs_of_clause fcs in 
    let au_qs, au_exp, au_subs = au lhses in 
    let fcs' = sub_func_clauses au_exp au_qs au_subs fcs in 
    FuncDef { def with it = (id, osubid, params, typ, fcs', opartial) }
  | _ -> failwith (Printf.sprintf "au_rule: Failed, attempted to anti-unify non-FuncDef definition.")

let rec au_dls (name : string) (dl : dl_def list) : dl_def list =
  match dl with 
  | (FuncDef def)::dl' -> 
      let (id, _osubid, _params, _typ, _fcs, _opartial) = def.it in
      if List.mem id.it target_names then [au_rule (FuncDef def)] @ au_dls name dl' else [(FuncDef def)] @ au_dls name dl'
  | def ::dl' -> [def] @ au_dls name dl' 
  | [] -> []