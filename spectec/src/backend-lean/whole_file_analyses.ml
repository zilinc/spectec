open Il.Ast
open Util.Source

(* Running examples used throughout this file.

   BEq example — setminus1_ and setminus_:

     IL:
       (DecD "setminus1_"
         [(TypP "X"); (ExpP "X_0" (VarT "X")); (ExpP "var_0_lst" (IterT (VarT "X") List))]
         (VarT "bool")
         [clause1: body = ListE [VarE "X_0"]
          clause2: body = IfE (CmpE `EqOp _ (VarE "w" : VarT "X") (VarE "w_1"))
                               [ListE []] [CallE "setminus1_" [TypA (VarT "X"); ...]]])

       (DecD "setminus_"
         [(TypP "X"); (ExpP "var_0_lst" (IterT (VarT "X") List)); ...]
         ...
         [clause1: body = ListE []
          clause2: body = CatE (CallE "setminus1_" [TypA (VarT "X"); ...])
                                (CallE "setminus_"  [TypA (VarT "X"); ...])])

     Goal Lean signatures (the [BEq X] binders being generated):
       def setminus1_ (X : Type) [BEq X] (X_0 : X) (var_0_lst : List X) : Bool := ...
       def setminus_  (X : Type) [BEq X] (var_0_lst : List X) ... : ... := ...

   Inhabited example — fun_relaxed2:

     IL:
       (DecD "fun_relaxed2"
         [(TypP "r_X"); (ExpP "v_relaxed2" (VarT "relaxed2"));
          (ExpP "X_0" (VarT "r_X")); (ExpP "X_1" (VarT "r_X"))]
         (VarT "r_X")
         [clause: body = IfE (VarE "ND")
                             (IdxE (ListE [VarE "X_0"; VarE "X_1"] : IterT (VarT "r_X") List)
                                   (CallE "proj_relaxed2_0" [ExpA (VarE "v_relaxed2")]))
                             (IdxE (ListE [VarE "X_0"; VarE "X_1"] : IterT (VarT "r_X") List)
                                   (NumE 0))])

     Goal Lean signature (the [Inhabited r_X] binder being generated):
       def fun_relaxed2 (v_relaxed2 : relaxed2) (r_X : Type) [Inhabited r_X]
           (X_0 : r_X) (X_1 : r_X) : r_X :=
         if ND then ([X_0, X_1])[proj_relaxed2_0 v_relaxed2]! else ([X_0, X_1])[0]! *)

(* Iterate over every DecD in the script (including inside RecD groups), applying f
   to each and returning one (name, result) pair per function.
   e.g. map_over_decs il (fun _id params _ _ -> params)
     → [("setminus1_", [TypP "X"; ExpP "X_0" (VarT "X"); ...]); ...] *)
let map_over_decs
    (il : script)                                                              (* e.g. all top-level defs of the Wasm spec *)
    (f : Il.Ast.id -> Il.Ast.param list -> Il.Ast.typ -> Il.Ast.clause list -> 'a)
    : (string * 'a) list =                                                     (* e.g. [("setminus1_", [TypP "X"; ...]); ...] *)
  let rec process def =
    match def.it with
    | DecD (id, params, typ, clauses) -> [(id.it, f id params typ clauses)]
    | RecD defs -> List.concat_map process defs   (* descend into mutual-recursion groups *)
    | _ -> []
  in
  List.concat_map process il

(* Core infrastructure: two-phase TypP-need analysis.

   Determines, for every DecD, which of its TypP names require a given typeclass
   instance (e.g. [BEq X] or [Inhabited X]).

   Phase 1 — direct: walk each function body with the caller-supplied `detect` callback.
             `detect ~typp_names e` returns the TypP names triggered by expression e.
   Phase 2 — fixpoint: propagate through CallE. If callee needs [TC X_k] for its k-th TypP
             and the caller passes its own abstract VarT "Yi" as that argument, the caller
             also needs [TC Yi]. Repeat until stable.

   Result: function-name → list-of-TypP-names-needing-the-typeclass.
   Functions with no TypP parameters or no detected needs are absent.
     BEq:       [("setminus1_", ["X"]); ("setminus_", ["X"])]
     Inhabited: [("fun_relaxed2", ["r_X"]); ("fun_relaxed4", ["r_X"])] *)
let analyze_typp_needs
    (il : script)                                                              (* e.g. all top-level defs of the Wasm spec *)
    ~(detect : typp_names:string list -> exp -> string list)                   (* e.g. for BEq: given ["X"] and CmpE `EqOp _ (VarE "w" : VarT "X") _, returns ["X"] *)
    : (string * string list) list =                                            (* e.g. [("setminus1_", ["X"]); ("setminus_", ["X"])] *)

  (* Extract TypP names from a param list.
     [TypP "X"; ExpP "X_0" (VarT "X"); ...] → ["X"]  |  [ExpP "v_state" (VarT "state")] → [] *)
  let typp_names_of (params : Il.Ast.param list) : string list =              (* e.g. [TypP "X"; ExpP "X_0" ...] → ["X"] *)
    List.filter_map (fun p -> match p.it with
      | TypP id -> Some id.it
      | _ -> None) params
  in

  (* Collect (name, params, clauses) for every DecD once.
     Used in both phases to avoid re-walking the script on every fixpoint iteration.
     e.g. [("setminus1_", ([TypP "X"; ...], [clause1; clause2]));
           ("setminus_",  ([TypP "X"; ...], [clause1; clause2])); ...] *)
  let decs : (string * (Il.Ast.param list * Il.Ast.clause list)) list =       (* e.g. [("setminus1_", ([TypP "X"; ...], [...])); ...] *)
    map_over_decs il (fun _id params _typ clauses -> (params, clauses))
  in

  (* Phase 0: derive callee-name → param-list map from decs for positional type-arg matching
     in phase 2. When we see CallE "setminus1_" [TypA (VarT "X"); ...], this lets us look up
     setminus1_'s TypP list ["X"] to match argument positions to TypP names.
     e.g. [("setminus1_", [TypP "X"; ...]); ("setminus_", [TypP "X"; ...]); ...] *)
  let dec_params_map : (string * Il.Ast.param list) list =                    (* e.g. [("setminus1_", [TypP "X"; ...]); ...] *)
    List.map (fun (name, (params, _)) -> (name, params)) decs
  in

  (* Phase 1 collector: wrap `detect` in the Walk.collector interface.
     `detect ~typp_names e` is the caller-supplied pattern.
     `true` means: always recurse into sub-expressions.
     e.g. for BEq with typp_names=["X"] and e = CmpE `EqOp _ (VarE "w" : VarT "X") _:
       detect fires → (["X"], true)  (keep walking children) *)
  let make_direct_collector
      (typp_names : string list)                                               (* e.g. ["X"] — TypP names in scope for this function *)
      : string list Il.Walk.collector =                                        (* e.g. collector that returns ["X"] on CmpE over VarT "X" *)
    { (Il.Walk.base_collector [] (@)) with
      collect_exp = fun e -> (detect ~typp_names e, true) }
  in

  (* Phase 1: run the direct collector over every function's clauses.
     Produces the initial map of functions with directly detected needs.
     BEq:
       setminus1_: clause2 body has CmpE (VarE "w" : VarT "X") _ → ["X"]   retained
       setminus_:  clause2 body has only CallE                   → []        filtered out
       initial_map = [("setminus1_", ["X"])]
     Inhabited:
       fun_relaxed2: body has IdxE (ListE ... : IterT (VarT "r_X") List) → ["r_X"] retained
       fun_relaxed4: same pattern                                          → ["r_X"] retained
       initial_map = [("fun_relaxed2", ["r_X"]); ("fun_relaxed4", ["r_X"])] *)
  let initial_map : (string * string list) list =                             (* e.g. [("setminus1_", ["X"])] for BEq — functions with directly detected needs *)
    List.filter_map (fun (name, (params, clauses)) ->
      let typp_names : string list = typp_names_of params in                 (* e.g. ["X"] for setminus1_, [] for local_ *)
      if typp_names = [] then None                                            (* no type params → nothing to detect *)
      else
        let c : string list Il.Walk.collector = make_direct_collector typp_names in
        let found : string list =
          List.concat_map (Il.Walk.collect_clause c) clauses
          |> List.sort_uniq String.compare
        in                                                                    (* e.g. ["X"] for setminus1_, [] for setminus_ *)
        if found = [] then None else Some (name, found)
    ) decs
  in

  (* Phase 2 collector: propagate needs through CallE edges.

     For CallE("setminus1_", [TypA (VarT "X"); ExpA (VarE "w_1"); ExpA (VarE "lst")]):
       callee_typps = ["X"]          (setminus1_'s TypP list from dec_params_map)
       type_args    = [VarT "X"]     (TypA entries from args, positionally matching callee_typps)
       callee_needs = ["X"]          (setminus1_ needs [BEq X])
       List.combine → [("X", VarT "X")]
       "X" ∈ callee_needs, "X" ∈ typp_names ["X"] of caller (setminus_) → caller gains "X"
       Lean effect: [BEq X] is added to setminus_'s signature

     The `None` branches express "no propagation needed" — two valid cases:
       type_arg is not VarT (e.g. Nat, IterT ...): the concrete type has a globally available
         instance, which Lean's typeclass search resolves automatically. No constraint on caller.
       type_arg = VarT(xi,[]) but xi ∉ typp_names: xi is a globally defined concrete type name,
         not the caller's abstract TypP. Again resolved globally by Lean. No constraint on caller.
     We only propagate (Some xi) when the caller is forwarding its own abstract TypP xi,
     because only then does the caller lack a concrete instance in scope. *)
  let make_callE_collector
      (typp_names : string list)                                               (* e.g. ["X"] — TypP names in scope for the caller being analysed *)
      (needs_map : (string * string list) list)                                (* e.g. [("setminus1_", ["X"])] — currently known needs, grows each fixpoint step *)
      : string list Il.Walk.collector =                                        (* e.g. collector that returns ["X"] when caller calls setminus1_ with TypA (VarT "X") *)
    { (Il.Walk.base_collector [] (@)) with
      collect_exp = fun e ->
        let found : string list = match e.it with
          | CallE (callee_id, args) ->
              (match List.assoc_opt callee_id.it dec_params_map with
              | None -> []                                                    (* callee not a DecD we know about, e.g. a built-in *)
              | Some callee_params ->
                  let callee_typps : string list = typp_names_of callee_params in  (* e.g. ["X"] for setminus1_ *)
                  (* TypA entries from the call site, positionally matching callee_typps:
                     [TypA (VarT "X"); ExpA (VarE "w_1"); ...] → [VarT "X"] *)
                  let type_args : Il.Ast.typ list =
                    List.filter_map (fun a -> match a.it with
                      | TypA t -> Some t | _ -> None) args
                  in
                  let callee_needs : string list =                            (* e.g. ["X"] for setminus1_ *)
                    List.assoc_opt callee_id.it needs_map |> Option.value ~default:[]
                  in
                  (* pair each callee TypP with the corresponding type argument positionally;
                     equal length by IL well-formedness (each TypA matches exactly one TypP) *)
                  List.combine callee_typps type_args
                  |> List.filter_map (fun (callee_typp, type_arg) ->
                    if not (List.mem callee_typp callee_needs) then None      (* callee doesn't need [TC] for this TypP slot *)
                    else match type_arg.it with
                      | VarT (xi, []) when List.mem xi.it typp_names ->
                          (* Caller forwards its own abstract TypP xi (e.g. VarT "X" where "X" ∈ typp_names).
                             Lean has no concrete instance for xi in scope → must constrain the caller. *)
                          Some xi.it                                          (* e.g. Some "X" → setminus_ gains [BEq X] *)
                      | VarT (_, []) ->
                          (* type_arg is a VarT but not one of the caller's own TypP names.
                             Scenario 2: xi names a globally defined concrete type (e.g. VarT "Nat").
                             Lean's global typeclass search resolves [TC Nat] automatically.
                             No constraint on the caller is needed. *)
                          None
                      | _ ->
                          (* type_arg is not a bare VarT — it's a concrete compound type (e.g. IterT, BoolT, NumT).
                             Scenario 1: the callee is instantiated at a concrete type.
                             Lean's global typeclass search resolves [TC <concrete>] automatically.
                             No constraint on the caller is needed. *)
                          None))
          | _ -> []
        in
        (found, true)
    }
  in

  (* One fixpoint step: walk every function, propagating CallE-based needs into acc.
     Uses fold_left so that when a function gains a new need mid-pass, the updated
     needs_map is immediately visible to functions processed later in the same pass —
     this converges in fewer passes than computing all updates from the old state first.

     BEq iteration 1 (acc = [("setminus1_", ["X"])]):
       "setminus1_": calls itself → callee_needs=["X"], type_arg=VarT "X",
                     current=["X"] already → additions=[] → no change
       "setminus_":  calls setminus1_ → new_needs=["X"], current=[] → additions=["X"]
                     acc updated → [("setminus1_", ["X"]); ("setminus_", ["X"])], any_changed=true
     BEq iteration 2:
       "setminus_": calls setminus_ → callee_needs=["X"], current=["X"] → additions=[]
       any_changed=false → fixpoint done *)
  let one_step
      (needs_map : (string * string list) list)                               (* e.g. [("setminus1_", ["X"])] at start of iteration 1 *)
      : (string * string list) list * bool =                                  (* e.g. ([("setminus1_", ["X"]); ("setminus_", ["X"])], true) after iteration 1 *)
    List.fold_left (fun (acc, any_changed) (name, (params, clauses)) ->
      let typp_names : string list = typp_names_of params in                 (* e.g. ["X"] for setminus_ *)
      if typp_names = [] then (acc, any_changed)
      else
        let c : string list Il.Walk.collector = make_callE_collector typp_names acc in
        let new_needs : string list =
          List.concat_map (Il.Walk.collect_clause c) clauses
          |> List.sort_uniq String.compare
        in                                                                    (* e.g. ["X"] for setminus_ in iteration 1 *)
        let current : string list = List.assoc_opt name acc |> Option.value ~default:[] in  (* e.g. [] for setminus_ before update *)
        let additions : string list =
          List.filter (fun x -> not (List.mem x current)) new_needs
        in                                                                    (* e.g. ["X"] for setminus_ — newly discovered *)
        if additions = [] then (acc, any_changed)
        else
          let merged : string list = List.sort_uniq String.compare (current @ additions) in  (* e.g. ["X"] *)
          let updated : (string * string list) list =
            if List.mem_assoc name acc then
              List.map (fun (n, ns) -> if n = name then (n, merged) else (n, ns)) acc
            else
              (name, merged) :: acc                                           (* e.g. acc with ("setminus_", ["X"]) appended *)
          in
          (updated, true)
    ) (needs_map, false) decs
  in

  (* Repeat one_step until no function gains new needs.
     Terminates because each step either adds entries (finite domain) or returns false. *)
  let rec fixpoint
      (needs_map : (string * string list) list)                               (* e.g. [("setminus1_", ["X"])] → stabilises to [("setminus1_", ["X"]); ("setminus_", ["X"])] *)
      : (string * string list) list =                                         (* e.g. [("setminus1_", ["X"]); ("setminus_", ["X"])] for BEq *)
    match one_step needs_map with
    | (map', true)  -> fixpoint map'
    | (map', false) -> map'
  in

  fixpoint initial_map

(* Compute which DecD functions need [BEq X] for each TypP "X".
   Fires on MemE and CmpE(EqOp|NeOp) where the compared/searched element has type VarT "Xi".
   e.g. setminus1_ clause2: CmpE `EqOp _ (VarE "w" : VarT "X") _ → needs BEq for "X"
   Result: [("setminus1_", ["X"]); ("setminus_", ["X"])]
   These become [BEq X] instance binders in the generated Lean signatures. *)
let gather_defs_needing_beq (il : script) : (string * string list) list =
  analyze_typp_needs il ~detect:(fun ~typp_names e ->
    match e.it with
    | MemE (e1, _)
    | CmpE (`EqOp, _, e1, _)
    | CmpE (`NeOp, _, e1, _) ->
        (* e1 has type VarT "Xi" ∈ typp_names: comparing an abstract-typed value needs [BEq Xi]
           e.g. e1 = VarE "w" : VarT "X",  typp_names = ["X"]  → ["X"]
           Lean: [BEq X] inserted after (X : Type) in the generated signature *)
        (match e1.note.it with
        | VarT (id, []) when List.mem id.it typp_names -> [id.it]
        | _ -> [])
    | _ -> [])

(* Compute which DecD functions need [Inhabited X] for each TypP "X".
   Fires on IdxE(list_e, _) when list_e's element type is a TypP VarT.
   e.g. fun_relaxed2: IdxE(ListE [X_0;X_1] : IterT(VarT "r_X",List), i)
     → list_e.note = IterT(VarT "r_X", List), "r_X" ∈ typp_names → needs Inhabited for "r_X"
   Needed because [i]! (List.get!) returns `default` via Inhabited when the index is out of bounds.
   Result: [("fun_relaxed2", ["r_X"]); ("fun_relaxed4", ["r_X"])]
   These become [Inhabited r_X] instance binders in the generated Lean signatures. *)
let gather_defs_needing_inhabited (il : script) : (string * string list) list =
  analyze_typp_needs il ~detect:(fun ~typp_names e ->
    match e.it with
    | IdxE (list_e, _) ->
        (* list_e has type IterT(VarT "Xi", _) ∈ typp_names: indexing an abstract-typed list needs [Inhabited Xi]
           e.g. list_e : IterT(VarT "r_X", List),  typp_names = ["r_X"]  → ["r_X"]
           Lean: [Inhabited r_X] inserted after (r_X : Type) in the generated signature *)
        (match list_e.note.it with
        | IterT ({it = VarT (id, []); _}, _) when List.mem id.it typp_names -> [id.it]
        | _ -> [])
    | _ -> [])

(* Collect the names of all IL types defined as inductive (VariantT).
   These become Lean `inductive` types with namespaced constructors, e.g. externtype.GLOBAL.
   AliasT (abbrev) and StructT (structure) types are excluded.
   Recurses into RecD groups to handle mutually recursive types like instr/admininstr.
   e.g. TypD("addrtype", _, [InstD(_, _, VariantT _)]) → "addrtype" *)
let gather_variant_type_names (il : script) : string list =
  let rec collect_from_def def =
    match def.it with
    | TypD (id, _, [{it = InstD (_, _, {it = VariantT _; _}); _}]) -> [id.it]   (* e.g. "addrtype" → ["addrtype"] *)
    | RecD defs -> List.concat_map collect_from_def defs
    | _ -> []
  in
  List.concat_map collect_from_def il

(* Build a map (alias_name → underlying_variant_name) for non-parametric type
   aliases that transitively resolve to a VariantT type.

   Running example — Wasm 3.0 has:
     inductive addrtype where | I32 | I64   (* VariantT → in variant_names *)
     abbrev Inn : Type := addrtype           (* AliasT   → NOT in variant_names *)

   Without this map, a CaseE with note VarT("Inn",[]) falls through to LeadingDot
   and emits .I32 — ambiguous when Lean can't infer the list element type from
   List.length alone.  With the map, "Inn" resolves to "addrtype" and we emit
   the unambiguous addrtype.I32.

   Parametric aliases (e.g. `type list X := X*`) are deliberately excluded:
   their underlying VarT carries non-empty args (e.g. VarT("List",[VarT "X"])),
   so they never match VarT(_, []) and are skipped. The ambiguity problem only
   arises for zero-arg aliases used as bare constructor sources. *)
let gather_alias_to_variant_map
    (il : script)                      (* full IL script *)
    (variant_names : string list)      (* e.g. ["addrtype"; "numtype"; ...] *)
    : (string * string) list =         (* e.g. [("Inn","addrtype"); ("Fnn","numtype")] *)
  (* Step 1: collect every non-parametric alias X → Y as a flat list.
     TypD("Inn", _, [InstD(_, _, AliasT(VarT("addrtype", [])))])
       → Some ("Inn", "addrtype")
     TypD("list", _, [InstD(_, _, AliasT(VarT("List", [VarT "X"])))])
       → None  (args non-empty, excluded) *)
  let raw_aliases : (string * string) list =
    List.filter_map (fun (def : Il.Ast.def) ->
      match def.it with
      | TypD (alias_id, _,
              [{it = InstD (_, _, {it = AliasT {it = VarT (underlying_id, []); _}; _}); _}]) ->
          (* alias_id.it = "Inn", underlying_id.it = "addrtype" *)
          Some (alias_id.it, underlying_id.it)
      | _ -> None
    ) il
  in
  (* Step 2: transitively resolve X → ... → variant, guarding against cycles.
     resolve "Inn" [] :
       "Inn" ∉ visited, ∉ variant_names
       raw_aliases has "Inn" → "addrtype"
       resolve "addrtype" ["Inn"] :
         "addrtype" ∈ variant_names → Some "addrtype"
       → Some "addrtype"
     resolve "Zzz" [] where Zzz has no alias entry → None (not added to map) *)
  let rec resolve (name : string) (visited : string list) : string option =
    if List.mem name visited then None               (* cycle guard *)
    else if List.mem name variant_names then Some name   (* reached a variant root *)
    else match List.assoc_opt name raw_aliases with
      | Some underlying -> resolve underlying (name :: visited)   (* follow the chain *)
      | None -> None    (* dead end: not a variant and not aliased further *)
  in
  (* Step 3: for each alias, attempt full resolution; keep only those that reach a variant.
     ("Inn", "addrtype") → resolve "Inn" [] = Some "addrtype" → keep ("Inn", "addrtype")
     ("u32", "uN") where uN is StructT → resolve "u32" [] = None → drop *)
  List.filter_map (fun (alias_name : string) ->
    match resolve alias_name [] with
    | Some variant_name -> Some (alias_name, variant_name)   (* e.g. ("Inn","addrtype") *)
    | None -> None
  ) (List.map fst raw_aliases)

(* Collect the names of all IL types that were originally type families.
   The type-family-removal pass annotates each flattened type with
   HintD(TypH(id, [type_family_hint])). After flattening, functions that
   pattern-match on these types are genuinely partial in Lean because
   cross-product constructor combinations exist syntactically but were
   impossible in the original dependent type.
   e.g. "num_", "lane_" → were type families → lpacknum_ needs a catch-all. *)
let gather_type_family_type_names (il : script) : string list =
  let hint_id = Middlend.Typefamilyremoval.type_family_hint_id in
  let rec collect def =
    match def.it with
    | HintD { it = TypH (id, hints); _ }
      when List.exists (fun h -> h.hintid.it = hint_id) hints -> [id.it]
    | RecD defs -> List.concat_map collect defs
    | _ -> []
  in
  List.concat_map collect il

(* Collect names of functions generated by the type-family-removal pass as projections.
   These functions already have a complete pattern match (either the exact constructor arm
   or | _ => none for multi-instance families; just the constructor arm for single-instance
   families where the type is inhabited by exactly one constructor). Adding another catch-all
   arm would produce duplicate wildcards and a Lean error.
   e.g. "proj_cvtop___2", "proj_vtestop__0" *)
let gather_projection_func_names (il : script) : string list =
  let hint_id = Middlend.Typefamilyremoval.projection_hint_id in
  let rec collect def =
    match def.it with
    | HintD { it = DecH (id, hints); _ }
      when List.exists (fun h -> h.hintid.it = hint_id) hints -> [id.it]
    | RecD defs -> List.concat_map collect defs
    | _ -> []
  in
  List.concat_map collect il

(* Compute which DecD functions need a `| _ => Inhabited.default` catch-all arm.
   After type-family flattening, a function that pattern-matches on a formerly-indexed
   type argument has syntactically valid but semantically impossible constructor
   combinations — Lean's exhaustiveness checker rejects the definition.
   Mirrors the Rocq backend's `has_typ_fam` heuristic: add a catch-all when the function
   has more than one param and at least one ExpP param has a type-family type
   (directly, under IterT, or as a component of a TupT tuple type).
   NOTE: fvternop_-style genuine partiality (functions defined only for a subset of
   constructors of a NON-type-family type) is not handled here; that is a separate issue. *)
let gather_defs_needing_catchall
    (il : script)
    ~(proj_names : string list)
    : string list =
  let tf_names = gather_type_family_type_names il in
  if tf_names = [] then []
  else begin
    (* Matches Rocq's is_type_family: VarT in tf_set, IterT, or TupT containing one *)
    let rec is_tf_typ (t : Il.Ast.typ) =
      match t.it with
      | VarT (id, _) -> List.mem id.it tf_names
      | IterT (t', _) -> is_tf_typ t'
      | TupT xts -> List.exists (fun (_, t') -> is_tf_typ t') xts
      | _ -> false
    in
    (* Mirrors backend.ml's is_deconstruction *)
    let is_decon (arg : Il.Ast.arg) =
      match arg.it with
      | ExpA {it = VarE _; _} | TypA {it = VarT _; _} | DefA _ -> false
      | ExpA _ | TypA _ -> true
      | _ -> false
    in
    let check (name : string) (params : Il.Ast.param list) (clauses : Il.Ast.clause list) =
      (* (c) skip projection functions generated by the type-family-removal pass *)
      if List.mem name proj_names then false
      (* Rocq: requires > 1 param and at least one ExpP has a type-family type *)
      else if List.length params <= 1 then false
      else if not (List.exists (fun p ->
          match p.it with ExpP (_, t) -> is_tf_typ t | _ -> false) params)
        then false
      else begin
        let n = List.length params in
        (* (b) which param positions are ever destructured across all clauses *)
        let ever_decon =
          List.fold_left (fun acc clause ->
            let DefD (_, args, _, _) = clause.it in
            List.map2 (||) acc (List.map is_decon args)
          ) (List.init n (fun _ -> false)) clauses
        in
        if not (List.exists Fun.id ever_decon) then false
        else begin
          (* (d) is the last clause already an all-pass-through wildcard arm? *)
          match List.rev clauses with
          | [] -> false
          | last :: _ ->
            let DefD (_, last_args, _, _) = last.it in
            let last_is_catchall =
              List.for_all2 (fun decon arg -> not decon || not (is_decon arg))
                ever_decon last_args
            in
            not last_is_catchall
        end
      end
    in
    map_over_decs il (fun id params _typ clauses -> check id.it params clauses)
    |> List.filter_map (fun (name, needs) -> if needs then Some name else None)
  end

(* Collect all IL type names that need a Lean `Append` instance.
   A type X needs Append when the IL uses CompE (++) with an X-typed operand.
   e.g. CompE(e1 : VarT "store", e2 : VarT "store") → "store" needs Append *)
let gather_types_that_need_append_instances (il : script) : string list =
  let collected = ref [] in
  let module Visitor = Il.Iter.Make(
    struct
      include Il.Iter.Skip
      let visit_exp e =
        match e.it with
        | CompE (e1, e2) ->
          if e1.note.it <> e2.note.it then
            failwith "CompE types don't match!"
          else
            (match e1.note.it with
            | VarT (id, []) -> collected := id.it :: !collected   (* e.g. "store" *)
            | _ -> ())
        | _ -> ()
    end
  )
  in
  List.iter Visitor.def il;
  List.sort_uniq String.compare !collected

(* Collect, for each `mutual` block (RecD group) in the script, the case/rule
   id of every RelD relation bundled inside it. Standalone RelDs (not inside a
   RecD) form their own singleton group, since they can never collide with
   anything else in the same Lean `mutual` block.
   e.g. `mutual Instr_ok ... Instrs_ok ... end` with Instr_ok's rules named
   [...; "frame"; ...] and Instrs_ok's rules named [...; "frame"; ...]
     → one group: [("Instr_ok", [...; "frame"; ...]); ("Instrs_ok", [...; "frame"; ...])] *)
let gather_relation_case_groups (il : script) : (string * string list) list list =
  let relation_cases (id : id) (rules : rule list) : string * string list =
    (id.it, List.map (fun (r : rule) -> let RuleD (rid, _, _, _, _) = r.it in rid.it) rules)
  in
  let collect def : (string * string list) list list =
    match def.it with
    | RelD (id, _, _, _, rules) -> [[relation_cases id rules]]
    | RecD defs ->
        let group = List.concat_map (fun d -> match d.it with
          | RelD (id, _, _, _, rules) -> [relation_cases id rules]
          | _ -> []
        ) defs in
        (* Non-RelD members of this RecD (types, defs, ...) contribute no
           relation cases here but may still share the block; their own
           constructor names are not covered by this analysis (see NOTE
           on the field below). *)
        if group = [] then [] else [group]
    | _ -> []
  in
  List.concat_map collect il

(* For each RelD relation, the subset of its own rule-case ids that collide
   with a same-named case in ANOTHER RelD bundled in the same `mutual` block
   (RecD group). Keyed by relation id -- NOT a flat name set -- because
   collision is a per-group property: "frame" colliding inside the
   Instr_ok2/Instrs_ok2 group must not cause Instrs_ok's unrelated "frame"
   case (a different, non-overlapping mutual group with no internal "frame"
   collision) to be renamed too. A flat set would conflate the two groups and
   make Instrs_ok's naming depend on an edit to Instr_ok2/Instrs_ok2 elsewhere
   in the script -- exactly the kind of action-at-a-distance fragility this
   analysis exists to avoid.

   These are exactly the names that trigger the Lean `induction ... using`
   bug documented in test-lean/bug.lean: `getAltNumFields` resolves
   alternative names by an unqualified, first-match linear search over every
   constructor in the whole mutual group, so a same-named case in a sibling
   relation silently shadows this one and `introN` is asked for the wrong
   number of binders.
   e.g. Instr_ok2 and Instrs_ok2 both have a rule case named "frame"
     → [("Instr_ok2", ["frame"]); ("Instrs_ok2", ["frame"])] is in the result,
       so backend.ml prepends each relation's own name to that one case only,
       leaving every non-colliding case (the vast majority, including
       already-prefixed auto-derived ones like "fun_sum_case_1") untouched.
   NOTE: this only tracks RelD rule-case names. A VariantT datatype's plain
   constructors (built in create_typcase) bundled in the same mutual block are
   not included, so a clash between a rule case and a datatype constructor --
   or between two datatype constructors -- would not be caught here. Extending
   coverage to those would mean gathering their names the same way inside
   gather_relation_case_groups and merging them into the same per-group name
   list before the collision count below. *)
let gather_colliding_relation_case_names (il : script) : (string * string list) list =
  let groups = gather_relation_case_groups il in
  List.concat_map (fun (group : (string * string list) list) ->
    let all_case_names = List.concat_map snd group in
    let counts = Hashtbl.create 16 in
    List.iter (fun n ->
      Hashtbl.replace counts n (1 + (try Hashtbl.find counts n with Not_found -> 0))
    ) all_case_names;
    List.filter_map (fun (rel_id, case_names) ->
      let colliding = List.filter (fun n -> Hashtbl.find counts n > 1) case_names in
      if colliding = [] then None else Some (rel_id, colliding)
    ) group
  ) groups

(* The result of the whole-script pre-pass, consumed by code generation in backend.ml.
   Computed once before code emission and stored in the `analysis` ref below. *)
type whole_script_analysis =
  {
    types_needing_append_instances : string list;
    variant_type_names : string list;
    (* Maps alias type names to the underlying VariantT name they resolve to.
       e.g. [("Inn", "addrtype"); ("Fnn", "numtype")]
       Used in CaseE to emit addrtype.I32 instead of ambiguous .I32. *)
    alias_to_variant_map : (string * string) list;
    (* Maps function names to TypP names that require [BEq X].
       e.g. [("setminus1_", ["X"]); ("setminus_", ["X"])]
       Generates [BEq X] instance binders after (X : Type) in those functions' Lean signatures. *)
    defs_needing_beq : (string * string list) list;
    (* Maps function names to TypP names that require [Inhabited X].
       e.g. [("fun_relaxed2", ["r_X"]); ("fun_relaxed4", ["r_X"])]
       Generates [Inhabited r_X] instance binders after (r_X : Type) in those functions' Lean signatures. *)
    defs_needing_inhabited : (string * string list) list;
    (* Names of functions that need `| _ => Inhabited.default` appended to their match.
       After type-family flattening, cross-product constructor combinations are syntactically
       valid but semantically impossible; this catch-all makes the match exhaustive for Lean.
       Projection functions and functions that already have a wildcard last arm are excluded.
       e.g. ["lpacknum_"; "const"; "cvtop_"] *)
    defs_needing_catchall : string list;
    (* Maps a RelD relation's own id to the subset of its rule-case ids that
       collide with a same-named case in a sibling RelD bundled in the same
       `mutual` block (see gather_colliding_relation_case_names above).
       e.g. [("Instr_ok2", ["frame"]); ("Instrs_ok2", ["frame"])] when those
       two -- and only those two -- share a "frame" case in one mutual block.
       backend.ml looks up its own relation id here and prepends the
       relation's own name only to a case whose id appears in that relation's
       own entry, to work around the Lean `induction ... using` bug in
       test-lean/bug.lean without renaming every already-unique case, and
       without letting a collision in one mutual block affect naming in an
       unrelated one. *)
    colliding_relation_case_names : (string * string list) list;
  }

(* Run all whole-script analyses and bundle the results. *)
let analyze_whole_script (il : script) : whole_script_analysis =
  let variant_type_names : string list = gather_variant_type_names il in
  {
    types_needing_append_instances = gather_types_that_need_append_instances il;
    variant_type_names;
    alias_to_variant_map = gather_alias_to_variant_map il variant_type_names;
    defs_needing_beq = gather_defs_needing_beq il;
    defs_needing_inhabited = gather_defs_needing_inhabited il;
    defs_needing_catchall =
      (let proj_names = gather_projection_func_names il in
       gather_defs_needing_catchall il ~proj_names);
    colliding_relation_case_names = gather_colliding_relation_case_names il;
  }

(* Mutable cell holding the current script's analysis results.
   Initialised to empty values; overwritten by `analysis := analyze_whole_script il`
   before code generation begins. *)
let analysis : whole_script_analysis ref = ref {
  types_needing_append_instances = [];
  variant_type_names = [];
  alias_to_variant_map = [];
  defs_needing_beq = [];
  defs_needing_inhabited = [];
  defs_needing_catchall = [];
  colliding_relation_case_names = [];
}
