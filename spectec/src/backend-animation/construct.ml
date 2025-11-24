open Il.Ast
open Il.Print
open Util
open Error
open Source
open Il_util
module RI = Reference_interpreter
module RT = RI.Types
module BI = Backend_interpreter
open Xl.Atom


let error at msg = Util.Error.error at "ani.../int.../construct" msg
let error_value name exp = error exp.at ("Invalid " ^ name ^ ": " ^ string_of_exp exp)
let error_values name exps =
  let at = over_region (List.map (fun e -> e.at) exps) in
  error at ("Invalid " ^ name ^ ": " ^ String.concat ", " (List.map string_of_exp exps))


(* Constant *)

let default_table_max = 4294967295L
let default_memory_max = 65536L

(* Currently support only version 3. *)
let version = ref 3



(* Construct minor *)

let il_of_z_nat z : exp = natE z
let il_of_z_int z : exp = intE z

let il_of_uN z : exp = mk_case' "uN" [[];[]] [natE z]
let il_of_iN z : exp = mk_case' "iN" [[];[]] [natE z]


let il_of_fmagN layout i : exp =
  let n = Z.logand i (BI.Construct.mask_exp layout) in
  let m = Z.logand i (BI.Construct.mask_mant layout) in
  let t = VarT ("fNmag" $ no, [ExpA (varE ~note:(t_var "N") "N") $ no]) $ no in
  if n = Z.zero then
    mk_case t [["SUBNORM"];[]] [il_of_z_nat m]
  else if n <> BI.Construct.mask_exp layout then
    mk_case t [["NORM"];[];[]] [il_of_z_nat m; il_of_z_int Z.(shift_right n layout.mantissa - BI.Construct.bias layout)]
  else if m = Z.zero then
    mk_case t [["INF"]] []
  else
    mk_case t [["NAN"];[]] [il_of_z_nat m]

let il_of_floatN layout i =
  let t = VarT ("fN" $ no, [ExpA (varE ~note:(t_var "N") "N") $ no]) $ no in
  let i' = Z.logand i (BI.Construct.mask_mag layout) in
  let mag = il_of_fmagN layout i in
  mk_case t [[if i' = i then "POS" else "NEG"];[]] [mag]


let il_of_nat i = Z.of_int i |> il_of_z_nat
let il_of_nat8  i8  = Z.of_int (RI.I8.to_int_u  i8 ) |> il_of_z_nat
let il_of_nat16 i16 = Z.of_int (RI.I16.to_int_u i16) |> il_of_z_nat
let il_of_nat32 i32 = Z.of_int32_unsigned i32 |> il_of_z_nat
let il_of_nat64 i64 = Z.of_int64_unsigned i64 |> il_of_z_nat

let il_of_name name = textE (Utf8.encode name)
let il_of_byte byte = Char.code byte |> il_of_nat
let il_of_bytes bytes = String.to_seq bytes |> il_of_seq il_of_byte (t_star "byte")
let il_of_float32 f32 = RI.F32.to_bits f32 |> Z.of_int32_unsigned |> il_of_floatN BI.Construct.layout32
let il_of_float64 f64 = RI.F64.to_bits f64 |> Z.of_int64_unsigned |> il_of_floatN BI.Construct.layout64
let il_of_vec128 vec = BI.Construct.vec128_to_z vec |> il_of_z_nat


let il_of_uN_32 (n: RI.I32.t) = mk_case' "uN" [[];[]] [il_of_nat32 n]
let il_of_uN_64 (n: RI.I64.t) = mk_case' "uN" [[];[]] [il_of_nat64 n]
let il_of_idx (idx: RI.Ast.idx) = il_of_uN_32 idx.it
let il_of_memidx idx = il_of_idx idx


(* syntax list(syntax X) = X*  -- if ... *)
let il_of_list' t ls = mk_case' "list" [[];[]] [listE t ls]


let rec il_of_null = function
  | RT.NoNull -> mk_none (t_var "nul")
  | RT.Null   -> mk_some (t_var "nul") (mk_nullary' "nul" "NULL")

and il_of_final = function
  | RT.NoFinal -> mk_none (t_var "fin")
  | RT.Final   -> mk_some (t_var "fin") (mk_nullary' "fin" "FINAL")

and il_of_mut = function
  | RT.Cons -> mk_none (t_var "mut")
  | RT.Var  -> mk_some (t_var "mut") (mk_nullary' "mut" "MUT")

and il_of_packtype = function
  | RT.I8T  -> mk_nullary' "storagetype" "I8"
  | RT.I16T -> mk_nullary' "storagetype" "I16"

and il_of_storagetype = function
  | RT.ValStorageT  vt -> il_of_valtype  vt
  | RT.PackStorageT pt -> il_of_packtype pt

and il_of_fieldtype = function
  | RT.FieldT (mut, st) -> mk_case' "fieldtype" [[];[];[]] [il_of_mut mut; il_of_storagetype st]

and il_of_resulttype rt = il_of_list' (t_star "valtype") (List.map il_of_valtype rt)

and il_of_comptype = function
  | RT.StructT ftl      -> mk_case' "comptype" [["STRUCT"];[]]      [il_of_list (t_list "fieldtype") il_of_fieldtype ftl]
  | RT.ArrayT  ft       -> mk_case' "comptype" [["ARRAY"];[]]       [il_of_fieldtype ft]
  | RT.FuncT (rt1, rt2) -> mk_case' "comptype" [["FUNC"];["->"];[]] [il_of_resulttype rt1; il_of_resulttype rt2]

and il_of_subtype = function
  | RT.SubT (fin, tul, st) ->
    mk_case' "subtype" [["SUB"];[];[];[]] [il_of_final fin; il_of_list (t_star "typeuse") il_of_typeuse tul; il_of_comptype st]

and il_of_rectype = function
  | RT.RecT stl -> mk_case' "rectype" [["REC"];[]] [il_of_list' (t_list "subtype") (List.map il_of_subtype stl)]

and il_of_deftype = function
  | RT.DefT (rt, i) -> mk_case' "deftype" [["_DEF"];[];[]] [il_of_rectype rt; il_of_nat32 i]

and il_of_typeuse = function
  | RT.Idx idx -> mk_case' "typeuse" [["_IDX"];[]] [il_of_uN_32 idx]
  | RT.Rec n   -> mk_case' "typeuse" [["REC" ];[]] [il_of_nat32 n]
  | RT.Def dt  -> il_of_deftype dt

and il_of_typeuse_of_idx idx = mk_case' "typeuse" [["_IDX"];[]] [il_of_idx idx]

and il_of_heaptype = function
  | RT.UseHT tu -> il_of_typeuse tu
  | RT.BotHT    -> mk_nullary' "absheaptype" "BOT"
  | ht -> RT.string_of_heaptype ht |> mk_nullary' "absheaptype"

and il_of_reftype (null, ht) =
  mk_case' "reftype" [["REF"];[];[]] [il_of_null null; il_of_heaptype ht]

and il_of_addrtype at = RT.string_of_addrtype at |> mk_nullary' "addrtype"

and il_of_numtype nt = RT.string_of_numtype nt |> mk_nullary' "numtype"

and il_of_vectype vt = RT.string_of_vectype vt |> mk_nullary' "vectype"

and il_of_valtype = function
  | RT.RefT rt -> il_of_reftype rt
  | RT.NumT nt -> il_of_numtype nt
  | RT.VecT vt -> il_of_vectype vt
  | RT.BotT    -> mk_nullary' "valtype" "BOT"

let il_of_blocktype = function
  | RI.Ast.VarBlockType idx    -> mk_case' "blocktype" [["_IDX"   ];[]] [il_of_idx idx]
  | RI.Ast.ValBlockType vt_opt -> mk_case' "blocktype" [["_RESULT"];[]] [il_of_opt (t_opt "valtype") il_of_valtype vt_opt]

let il_of_limits default (limits: RT.limits) =
  let omax =
    match limits.max with
    | Some v -> il_of_uN_64 v |> mk_some (t_opt "u64")
    | None   -> mk_none (t_opt "u64")
  in
  mk_case' "limits" [["["];[".."];["]"]] [il_of_uN_64 limits.min; omax]

let il_of_tagtype = function
  | RT.TagT tu -> il_of_typeuse tu

let il_of_globaltype = function
  | RT.GlobalT (mut, vt) -> mk_case' "globaltype" [[];[];[]] [il_of_mut mut; il_of_valtype vt]

let il_of_tabletype = function
  | RT.TableT (at, limits, rt) ->
    mk_case' "tabletype" [[];[];[];[]] [il_of_addrtype at; il_of_limits default_table_max limits; il_of_reftype rt]

let il_of_memorytype = function
  | RT.MemoryT (at, limits) ->
    mk_case' "memtype" [[];[];["PAGE"]] [il_of_addrtype at; il_of_limits default_memory_max limits]


(* Construct value *)

let il_of_num value =
  let const_info = {def = "instr"; case = "CONST"} in
  match value with
  | RI.Value.I32 i32 -> mk_case' "instr" [["CONST"];[];[]] [mk_nullary' "numtype" "I32"; il_of_uN_32 i32]
  | RI.Value.I64 i64 -> mk_case' "instr" [["CONST"];[];[]] [mk_nullary' "numtype" "I64"; il_of_uN_64 i64]
  | RI.Value.F32 f32 -> mk_case' "instr" [["CONST"];[];[]] [mk_nullary' "numtype" "F32"; il_of_float32 f32]
  | RI.Value.F64 f64 -> mk_case' "instr" [["CONST"];[];[]] [mk_nullary' "numtype" "F64"; il_of_float64 f64]

let il_of_vec = function
  | RI.Value.V128 v128 -> mk_case' "instr" [["VCONST"];[];[]] [mk_nullary' "vectype" "V128"; il_of_vec128 v128]

let il_of_vec_shape shape (lanes: int64 list) =
  il_of_vec (V128 (
    match shape with
    | RI.V128.I8x16() -> RI.V128.I8x16.of_lanes (List.map RI.I8.of_int_s (List.map Int64.to_int lanes))
    | RI.V128.I16x8() -> RI.V128.I16x8.of_lanes (List.map RI.I16.of_int_s (List.map Int64.to_int lanes))
    | RI.V128.I32x4() -> RI.V128.I32x4.of_lanes (List.map Int64.to_int32 lanes)
    | RI.V128.I64x2() -> RI.V128.I64x2.of_lanes lanes
    | RI.V128.F32x4() -> RI.V128.F32x4.of_lanes (List.map (fun i -> i |> Int64.to_int32 |> RI.F32.of_bits) lanes)
    | RI.V128.F64x2() -> RI.V128.F64x2.of_lanes (List.map RI.F64.of_bits lanes)
  ))

let rec il_of_ref = function
  | RI.Value.NullRef ht   -> mk_case' "instr" [["REF.NULL"];[]] [il_of_heaptype ht]
  | RI.Script.HostRef i32 -> mk_case' "instr" [["REF.HOST_ADDR"];[]] [il_of_nat32 i32]
  | RI.Extern.ExternRef r -> mk_case' "instr" [["REF.EXTERN"];[]] [il_of_ref r]
  | r -> error no ("il_of_ref: " ^ RI.Value.string_of_ref r)


let il_of_value (v: RI.Value.value) = match v with
  | Num n -> il_of_num n
  | Vec v -> il_of_vec v
  | Ref r -> il_of_ref r


(* Construct operation *)

let il_of_sx = function
  | RI.Pack.S -> mk_nullary' "sx" "S"
  | RI.Pack.U -> mk_nullary' "sx" "U"

let il_of_op f1 f2 = function
  | RI.Value.I32 op -> [mk_nullary' "numtype" "I32"; f1 op]
  | RI.Value.I64 op -> [mk_nullary' "numtype" "I64"; f1 op]
  | RI.Value.F32 op -> [mk_nullary' "numtype" "F32"; f2 op]
  | RI.Value.F64 op -> [mk_nullary' "numtype" "F64"; f2 op]



let il_of_unop =
  let open RI in
  let open Ast in
  let il_of_int_unop op =
    let t = t_app "unop_" [expA (subE (varE ~note:(t_var "Inn") "Inn") (t_var "Inn") (t_var "numtype"))] in
    match op with
    | IntOp.Clz    -> mk_nullary t "CLZ"
    | IntOp.Ctz    -> mk_nullary t "CTZ"
    | IntOp.Popcnt -> mk_nullary t "POPCNT"
    | IntOp.ExtendS Pack.Pack8  -> mk_case t [["EXTEND"];[]] [mk_nullary' "sz" "`8" ]
    | IntOp.ExtendS Pack.Pack16 -> mk_case t [["EXTEND"];[]] [mk_nullary' "sz" "`16"]
    | IntOp.ExtendS Pack.Pack32 -> mk_case t [["EXTEND"];[]] [mk_nullary' "sz" "`32"]
    | IntOp.ExtendS Pack.Pack64 -> mk_case t [["EXTEND"];[]] [mk_nullary' "sz" "`64"]
  in
  let il_of_float_unop op =
    let t = t_app "unop_" [expA (subE (varE ~note:(t_var "Fnn") "Fnn") (t_var "Fnn") (t_var "numtype"))] in
    match op with
    | FloatOp.Neg     -> mk_nullary t "NEG"
    | FloatOp.Abs     -> mk_nullary t "ABS"
    | FloatOp.Ceil    -> mk_nullary t "CEIL"
    | FloatOp.Floor   -> mk_nullary t "FLOOR"
    | FloatOp.Trunc   -> mk_nullary t "TRUNC"
    | FloatOp.Nearest -> mk_nullary t "NEAREST"
    | FloatOp.Sqrt    -> mk_nullary t "SQRT"
  in
  il_of_op il_of_int_unop il_of_float_unop

let il_of_binop =
  let open RI.Ast in
  let il_of_int_binop bop =
    let t = t_app "binop_" [expA (subE (varE ~note:(t_var "Inn") "Inn") (t_var "Inn") (t_var "numtype"))] in
    match bop with
    | IntOp.Add    -> mk_nullary t "ADD"
    | IntOp.Sub    -> mk_nullary t "SUB"
    | IntOp.Mul    -> mk_nullary t "MUL"
    | IntOp.Div sx -> mk_case t [["DIV"];[]] [il_of_sx sx]
    | IntOp.Rem sx -> mk_case t [["REM"];[]] [il_of_sx sx]
    | IntOp.And    -> mk_nullary t "AND"
    | IntOp.Or     -> mk_nullary t "OR"
    | IntOp.Xor    -> mk_nullary t "XOR"
    | IntOp.Shl    -> mk_nullary t "SHL"
    | IntOp.Shr sx -> mk_case t [["SHR"];[]] [il_of_sx sx]
    | IntOp.Rotl   -> mk_nullary t "ROTL"
    | IntOp.Rotr   -> mk_nullary t "ROTR"
  in
  let il_of_float_binop bop =
    let t = t_app "binop_" [expA (subE (varE ~note:(t_var "Fnn") "Fnn") (t_var "Fnn") (t_var "numtype"))] in
    match bop with
    | FloatOp.Add      -> mk_nullary t "ADD"
    | FloatOp.Sub      -> mk_nullary t "SUB"
    | FloatOp.Mul      -> mk_nullary t "MUL"
    | FloatOp.Div      -> mk_nullary t "DIV"
    | FloatOp.Min      -> mk_nullary t "MIN"
    | FloatOp.Max      -> mk_nullary t "MAX"
    | FloatOp.CopySign -> mk_nullary t "COPYSIGN"
  in
  il_of_op il_of_int_binop il_of_float_binop

let il_of_testop: RI.Ast.testop -> exp list =
  let il_of_int_testop : RI.Ast.IntOp.testop -> exp = function
    | Eqz -> let t = t_app "testop_" [expA (subE (varE ~note:(t_var "Inn") "Inn") (t_var "Inn") (t_var "numtype"))] in
             mk_nullary t "EQZ"
  in
  let il_of_float_testop: RI.Ast.FloatOp.testop -> exp = function
    | _ -> .
  in
  il_of_op il_of_int_testop il_of_float_testop

let il_of_relop =
  let open RI.Ast in
  let il_of_int_relop rop =
    let t = t_app "relop_" [expA (subE (varE ~note:(t_var "Inn") "Inn") (t_var "Inn") (t_var "numtype"))] in
    match rop with
    | IntOp.Eq    -> mk_nullary t "EQ"
    | IntOp.Ne    -> mk_nullary t "NE"
    | IntOp.Lt sx -> mk_case t [["LT"];[]] [il_of_sx sx]
    | IntOp.Gt sx -> mk_case t [["GT"];[]] [il_of_sx sx]
    | IntOp.Le sx -> mk_case t [["LE"];[]] [il_of_sx sx]
    | IntOp.Ge sx -> mk_case t [["GE"];[]] [il_of_sx sx]
  in
  let il_of_float_relop rop =
    let t = t_app "relop_" [expA (subE (varE ~note:(t_var "Fnn") "Fnn") (t_var "Fnn") (t_var "numtype"))] in
    match rop with
    | FloatOp.Eq -> mk_nullary t "EQ"
    | FloatOp.Ne -> mk_nullary t "NE"
    | FloatOp.Lt -> mk_nullary t "LT"
    | FloatOp.Gt -> mk_nullary t "GT"
    | FloatOp.Le -> mk_nullary t "LE"
    | FloatOp.Ge -> mk_nullary t "GE"
  in
  il_of_op il_of_int_relop il_of_float_relop

let il_of_cvtop cop =
  let open RI.Value in
  let open RI.Ast in
  let t_Inn = t_var "Inn" in
  let t_Fnn = t_var "Fnn" in
  let tII = t_app "cvtop__" [expA (subE (varE ~note:(t_var "Inn") "Inn_1") t_Inn (t_var "numtype"));
                             expA (subE (varE ~note:(t_var "Inn") "Inn_2") t_Inn (t_var "numtype"))] in
  let tFF = t_app "cvtop__" [expA (subE (varE ~note:(t_var "Fnn") "Fnn_1") t_Fnn (t_var "numtype"));
                             expA (subE (varE ~note:(t_var "Fnn") "Fnn_2") t_Fnn (t_var "numtype"))] in
  let tIF = t_app "cvtop__" [expA (subE (varE ~note:(t_var "Inn") "Inn_1") t_Inn (t_var "numtype"));
                             expA (subE (varE ~note:(t_var "Fnn") "Fnn_2") t_Fnn (t_var "numtype"))] in
  let tFI = t_app "cvtop__" [expA (subE (varE ~note:(t_var "Fnn") "Fnn_1") t_Fnn (t_var "numtype"));
                             expA (subE (varE ~note:(t_var "Inn") "Inn_2") t_Inn (t_var "numtype"))] in
  let il_of_int_cvtop num_bits cop =
    match cop with
    | IntOp.ExtendI32 sx     -> mk_nullary' "numtype" "I32", mk_case tII [["EXTEND"   ];[]] [il_of_sx sx]
    | IntOp.WrapI64          -> mk_nullary' "numtype" "I64", mk_nullary tII "WRAP"
    | IntOp.TruncF32 sx      -> mk_nullary' "numtype" "F32", mk_case tIF [["TRUNC"    ];[]] [il_of_sx sx]
    | IntOp.TruncF64 sx      -> mk_nullary' "numtype" "F64", mk_case tIF [["TRUNC"    ];[]] [il_of_sx sx]
    | IntOp.TruncSatF32 sx   -> mk_nullary' "numtype" "F32", mk_case tIF [["TRUNC_SAT"];[]] [il_of_sx sx]
    | IntOp.TruncSatF64 sx   -> mk_nullary' "numtype" "F64", mk_case tIF [["TRUNC_SAT"];[]] [il_of_sx sx]
    | IntOp.ReinterpretFloat -> mk_nullary' "numtype" ("F" ^ num_bits), mk_nullary tIF "REINTERPRET"
  in
  let il_of_float_cvtop num_bits cop =
    match cop with
    | FloatOp.ConvertI32 sx  -> mk_nullary' "numtype" "I32", mk_case tFI [["CONVERT"];[]] [il_of_sx sx]
    | FloatOp.ConvertI64 sx  -> mk_nullary' "numtype" "I64", mk_case tFI [["CONVERT"];[]] [il_of_sx sx]
    | FloatOp.PromoteF32     -> mk_nullary' "numtype" "F32", mk_case tFF [["PROMOTE"]] []
    | FloatOp.DemoteF64      -> mk_nullary' "numtype" "F64", mk_case tFF [["DEMOTE" ]] []
    | FloatOp.ReinterpretInt -> mk_nullary' "numtype" ("I" ^ num_bits), mk_nullary tFI "REINTERPRET"
  in
  match cop with
  | I32 op -> let to_, op' = il_of_int_cvtop "32" op in
              [mk_nullary t_Inn "I32"; to_; op']
  | I64 op -> let to_, op' = il_of_int_cvtop "64" op in
              [mk_nullary t_Inn "I64"; to_; op']
  | F32 op -> let to_, op' = il_of_float_cvtop "32" op in
              [mk_nullary t_Fnn "F32"; to_; op']
  | F64 op -> let to_, op' = il_of_float_cvtop "64" op in
              [mk_nullary t_Fnn "F64"; to_; op']


(* Vector operator *)

let num i = `Nat (Z.of_int i)
let two = num 2
let four = num 4
let eight = num 8
let sixteen = num 16
let thirtytwo = num 32
let sixtyfour = num 64

let il_of_half = function
  | RI.Ast.V128Op.Low  -> mk_nullary' "half" "LOW"
  | RI.Ast.V128Op.High -> mk_nullary' "half" "HIGH"

(*
let al_of_vop f1 f2 = function
  | V128 vop -> (
    match vop with
    | V128.I8x16 op -> [ CaseV ("X", [ nullary "I8"; numV sixteen ]); f1 op ]
    | V128.I16x8 op -> [ CaseV ("X", [ nullary "I16"; numV eight ]); f1 op ]
    | V128.I32x4 op -> [ CaseV ("X", [ nullary "I32"; numV four ]); f1 op ]
    | V128.I64x2 op -> [ CaseV ("X", [ nullary "I64"; numV two ]); f1 op ]
    | V128.F32x4 op -> [ CaseV ("X", [ nullary "F32"; numV four ]); f2 op ]
    | V128.F64x2 op -> [ CaseV ("X", [ nullary "F64"; numV two ]); f2 op ]
  )

let al_of_vop_opt f1 f2 = function
  | V128 vop -> (
    match vop with
    | V128.I8x16 op -> Option.map (fun v -> [ CaseV ("X", [ nullary "I8"; numV sixteen ]); v ]) (f1 op)
    | V128.I16x8 op -> Option.map (fun v -> [ CaseV ("X", [ nullary "I16"; numV eight ]); v ]) (f1 op)
    | V128.I32x4 op -> Option.map (fun v -> [ CaseV ("X", [ nullary "I32"; numV four ]); v ]) (f1 op)
    | V128.I64x2 op -> Option.map (fun v -> [ CaseV ("X", [ nullary "I64"; numV two ]); v ]) (f1 op)
    | V128.F32x4 op -> Option.map (fun v -> [ CaseV ("X", [ nullary "F32"; numV four ]); v ]) (f2 op)
    | V128.F64x2 op -> Option.map (fun v -> [ CaseV ("X", [ nullary "F64"; numV two ]); v ]) (f2 op)
  )

let al_of_viop f1:
    ('a, 'a, 'a, 'a, void, void) V128.laneop vecop -> value list = function
  | V128 vop -> (
    match vop with
    | V128.I8x16 op -> [ CaseV ("X", [ nullary "I8"; numV sixteen ]); f1 op ]
    | V128.I16x8 op -> [ CaseV ("X", [ nullary "I16"; numV eight ]); f1 op ]
    | V128.I32x4 op -> [ CaseV ("X", [ nullary "I32"; numV four ]); f1 op ]
    | V128.I64x2 op -> [ CaseV ("X", [ nullary "I64"; numV two ]); f1 op ]
    | _ -> .
  )

let al_of_vbitmaskop = function
  | V128 (vop : V128Op.bitmaskop) -> (
    match vop with
    | V128.I8x16 _ -> [ CaseV ("X", [ nullary "I8"; numV sixteen ]) ]
    | V128.I16x8 _ -> [ CaseV ("X", [ nullary "I16"; numV eight ]) ]
    | V128.I32x4 _ -> [ CaseV ("X", [ nullary "I32"; numV four ]) ]
    | V128.I64x2 _ -> [ CaseV ("X", [ nullary "I64"; numV two ]) ]
    | _ -> .
  )

let al_of_int_vtestop : V128Op.itestop -> value = function
  | V128Op.AllTrue -> nullary "ALL_TRUE"

let al_of_float_vtestop : Ast.void -> value = function
  | _ -> .

let al_of_vtestop = al_of_vop al_of_int_vtestop al_of_float_vtestop

let al_of_int_vrelop : V128Op.irelop -> value = function
  | V128Op.Eq -> nullary "EQ"
  | V128Op.Ne -> nullary "NE"
  | V128Op.Lt sx -> caseV ("LT", [al_of_sx sx])
  | V128Op.Le sx -> caseV ("LE", [al_of_sx sx])
  | V128Op.Gt sx -> caseV ("GT", [al_of_sx sx])
  | V128Op.Ge sx -> caseV ("GE", [al_of_sx sx])

let al_of_float_vrelop : V128Op.frelop -> value = function
  | V128Op.Eq -> nullary "EQ"
  | V128Op.Ne -> nullary "NE"
  | V128Op.Lt -> nullary "LT"
  | V128Op.Le -> nullary "LE"
  | V128Op.Gt -> nullary "GT"
  | V128Op.Ge -> nullary "GE"

let al_of_vrelop = al_of_vop al_of_int_vrelop al_of_float_vrelop

let al_of_int_vunop : V128Op.iunop -> value = function
  | V128Op.Abs -> nullary "ABS"
  | V128Op.Neg -> nullary "NEG"
  | V128Op.Popcnt -> nullary "POPCNT"

let al_of_float_vunop : V128Op.funop -> value = function
  | V128Op.Abs -> nullary "ABS"
  | V128Op.Neg -> nullary "NEG"
  | V128Op.Sqrt -> nullary "SQRT"
  | V128Op.Ceil -> nullary "CEIL"
  | V128Op.Floor -> nullary "FLOOR"
  | V128Op.Trunc -> nullary "TRUNC"
  | V128Op.Nearest -> nullary "NEAREST"

let al_of_vunop = al_of_vop al_of_int_vunop al_of_float_vunop

let al_of_int_vbinop_opt : V128Op.ibinop -> value option = function
  | V128Op.Add -> Some (nullary "ADD")
  | V128Op.Sub -> Some (nullary "SUB")
  | V128Op.Mul -> Some (nullary "MUL")
  | V128Op.Min sx -> Some (caseV ("MIN", [al_of_sx sx]))
  | V128Op.Max sx -> Some (caseV ("MAX", [al_of_sx sx]))
  | V128Op.AvgrU -> Some (nullary "AVGR")
  | V128Op.AddSat sx -> Some (caseV ("ADD_SAT", [al_of_sx sx]))
  | V128Op.SubSat sx -> Some (caseV ("SUB_SAT", [al_of_sx sx]))
  | V128Op.Q15MulRSatS -> Some (caseV ("Q15MULR_SAT", [(*nullary "S"*)]))
  | V128Op.RelaxedQ15MulRS -> Some (caseV ("RELAXED_Q15MULR", [(*nullary "S"*)]))
  | _ -> None

let al_of_float_vbinop_opt : V128Op.fbinop -> value option = function
  | V128Op.Add -> Some (nullary "ADD")
  | V128Op.Sub -> Some (nullary "SUB")
  | V128Op.Mul -> Some (nullary "MUL")
  | V128Op.Div -> Some (nullary "DIV")
  | V128Op.Min -> Some (nullary "MIN")
  | V128Op.Max -> Some (nullary "MAX")
  | V128Op.Pmin -> Some (nullary "PMIN")
  | V128Op.Pmax -> Some (nullary "PMAX")
  | V128Op.RelaxedMin -> Some (nullary "RELAXED_MIN")
  | V128Op.RelaxedMax -> Some (nullary "RELAXED_MAX")

let al_of_vbinop_opt = al_of_vop_opt al_of_int_vbinop_opt al_of_float_vbinop_opt

let al_of_int_vternop_opt : V128Op.iternop -> value option = function
  | V128Op.RelaxedLaneselect -> Some (nullary "RELAXED_LANESELECT")
  | _ -> None

let al_of_float_vternop_opt : V128Op.fternop -> value option = function
  | V128Op.RelaxedMadd -> Some (nullary "RELAXED_MADD")
  | V128Op.RelaxedNmadd -> Some (nullary "RELAXED_NMADD")

let al_of_vternop_opt = al_of_vop_opt al_of_int_vternop_opt al_of_float_vternop_opt

let al_of_special_vbinop = function
  | V128 (V128.I8x16 (V128Op.Swizzle)) when !version <= 2 -> CaseV ("VSWIZZLE", [ CaseV ("X", [ nullary "I8"; numV sixteen ]); ])
  | V128 (V128.I8x16 (V128Op.Swizzle)) -> CaseV ("VSWIZZLOP", [ CaseV ("X", [ nullary "I8"; numV sixteen ]); nullary "SWIZZLE" ])
  | V128 (V128.I8x16 (V128Op.RelaxedSwizzle)) -> CaseV ("VSWIZZLOP", [ CaseV ("X", [ nullary "I8"; numV sixteen ]); nullary "RELAXED_SWIZZLE" ])
  | V128 (V128.I8x16 (V128Op.Shuffle l)) -> CaseV ("VSHUFFLE", [ CaseV ("X", [ nullary "I8"; numV sixteen ]); al_of_list al_of_nat8 l ])
  | V128 (V128.I8x16 (V128Op.Narrow sx)) -> CaseV ("VNARROW", [ CaseV ("X", [ nullary "I8"; numV sixteen ]); CaseV ("X", [ nullary "I16"; numV eight ]); al_of_sx sx ])
  | V128 (V128.I16x8 (V128Op.Narrow sx)) -> CaseV ("VNARROW", [ CaseV ("X", [ nullary "I16"; numV eight]); CaseV ("X", [ nullary "I32"; numV four ]); al_of_sx sx ])
  | V128 (V128.I16x8 (V128Op.ExtMul (half, sx))) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I16"; numV eight ]); CaseV ("X", [ nullary "I8"; numV sixteen ]); caseV ("EXTMUL", [al_of_half half; al_of_sx sx]) ])
  | V128 (V128.I32x4 (V128Op.ExtMul (half, sx))) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I32"; numV four ]); CaseV ("X", [ nullary "I16"; numV eight ]); caseV ("EXTMUL", [al_of_half half; al_of_sx sx]) ])
  | V128 (V128.I64x2 (V128Op.ExtMul (half, sx))) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I64"; numV two ]); CaseV ("X", [ nullary "I32"; numV four ]); caseV ("EXTMUL", [al_of_half half; al_of_sx sx]) ])
  | V128 (V128.I32x4 (V128Op.DotS)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I32"; numV four ]); CaseV ("X", [ nullary "I16"; numV eight ]); caseV ("DOT", [(*al_of_extension Pack.SX*)]) ])
  | V128 (V128.I16x8 (V128Op.RelaxedDot)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I16"; numV eight ]); CaseV ("X", [ nullary "I8"; numV sixteen ]); caseV ("RELAXED_DOT", [(*al_of_extension Pack.SX*)]) ])
  | vop -> error_instr "al_of_special_vbinop" (VecBinary vop)

let al_of_special_vternop = function
  | V128 (V128.I32x4 V128Op.RelaxedDotAddS) -> CaseV ("VEXTTERNOP", [ CaseV ("X", [ nullary "I32"; numV four ]); CaseV ("X", [ nullary "I8"; numV sixteen ]); caseV ("RELAXED_DOT_ADD", [(*al_of_extension Pack.SX*)]) ])
  | vop -> error_instr "al_of_special_vternop" (VecTernary vop)

let al_of_int_vcvtop_opt = function
  | V128Op.Extend (half, sx) -> Some (None, caseV ("EXTEND", [al_of_half half; al_of_sx sx]))
  | V128Op.TruncSatF32x4 sx -> Some (Some (CaseV ("X", [ nullary "F32"; numV four ])), caseV ("TRUNC_SAT", [al_of_sx sx; noneV]))
  | V128Op.TruncSatZeroF64x2 sx -> Some (Some (CaseV ("X", [ nullary "F64"; numV two ])), caseV ("TRUNC_SAT", [al_of_sx sx; someV (nullary "ZERO")]))
  | V128Op.RelaxedTruncF32x4 sx -> Some (Some (CaseV ("X", [ nullary "F32"; numV four ])), caseV ("RELAXED_TRUNC", [al_of_sx sx; noneV]))
  | V128Op.RelaxedTruncZeroF64x2 sx -> Some (Some (CaseV ("X", [ nullary "F64"; numV two ])), caseV ("RELAXED_TRUNC", [al_of_sx sx; someV (nullary "ZERO")]))
  | _ -> None

let al_of_float32_vcvtop_opt = function
  | V128Op.DemoteZeroF64x2 -> Some (Some (CaseV ("X", [ nullary "F64"; numV two ])), caseV ("DEMOTE", [nullary "ZERO"]))
  | V128Op.ConvertI32x4 sx -> Some (Some (CaseV ("X", [ nullary "I32"; numV four ])), caseV ("CONVERT", [noneV; al_of_sx sx]))
  | _ -> None

let al_of_float64_vcvtop_opt = function
  | V128Op.PromoteLowF32x4 -> Some (Some (CaseV ("X", [ nullary "F32"; numV four ])), nullary "PROMOTE")
  | V128Op.ConvertI32x4 sx -> Some (Some (CaseV ("X", [ nullary "I32"; numV four ])), caseV ("CONVERT", [someV (nullary "LOW"); al_of_sx sx]))
  | _ -> None

let al_of_vcvtop_opt = function
  | V128 vop -> (
    match vop with
    | V128.I8x16 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> error_instr "al_of_vcvtop" (VecConvert (V128 vop)) in
        [ CaseV ("X", [ nullary "I8"; numV sixteen ]); sh; op' ]
      ) (al_of_int_vcvtop_opt op)
    )
    | V128.I16x8 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> CaseV ("X", [ nullary "I8"; numV sixteen ]) in
        [ CaseV ("X", [ nullary "I16"; numV eight ]); sh; op' ]
      ) (al_of_int_vcvtop_opt op)
    )
    | V128.I32x4 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> CaseV ("X", [ nullary "I16"; numV eight ]) in
        [ CaseV ("X", [ nullary "I32"; numV four ]); sh; op' ]
      ) (al_of_int_vcvtop_opt op)
    )
    | V128.I64x2 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> CaseV ("X", [ nullary "I32"; numV four ]) in
        [ CaseV ("X", [ nullary "I64"; numV two ]); sh; op' ]
      ) (al_of_int_vcvtop_opt op)
    )
    | V128.F32x4 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> error_instr "al_of_vcvtop" (VecConvert (V128 vop)) in
        [ CaseV ("X", [ nullary "F32"; numV four ]); sh; op' ]
      ) (al_of_float32_vcvtop_opt op)
    )
    | V128.F64x2 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> error_instr "al_of_vcvtop" (VecConvert (V128 vop)) in
        [ CaseV ("X", [ nullary "F64"; numV two ]); sh; op' ]
      ) (al_of_float64_vcvtop_opt op)
    )
  )


let al_of_special_vcvtop = function
  | V128 (V128.I16x8 (V128Op.ExtAddPairwise sx)) -> CaseV ("VEXTUNOP", [ CaseV ("X", [ nullary "I16"; numV eight]); CaseV ("X", [ nullary "I8"; numV sixteen ]); caseV ("EXTADD_PAIRWISE", [al_of_sx sx]) ])
  | V128 (V128.I32x4 (V128Op.ExtAddPairwise sx)) -> CaseV ("VEXTUNOP", [ CaseV ("X", [ nullary "I32"; numV four]); CaseV ("X", [ nullary "I16"; numV eight ]); caseV ("EXTADD_PAIRWISE", [al_of_sx sx]) ])
  | vop -> error_instr "al_of_special_vcvtop" (VecConvert vop)

let al_of_int_vshiftop : V128Op.ishiftop -> value = function
  | V128Op.Shl -> nullary "SHL"
  | V128Op.Shr sx -> caseV ("SHR", [al_of_sx sx])

let al_of_vshiftop = al_of_viop al_of_int_vshiftop

let al_of_vvtestop : vvtestop -> value list = function
  | V128 vop -> (
    match vop with
    | V128Op.AnyTrue ->
      [ nullary "V128"; nullary "ANY_TRUE" ]
  )

let al_of_vvunop : vvunop -> value list = function
  | V128 vop -> (
    match vop with
    | V128Op.Not -> [ nullary "V128"; nullary "NOT" ]
  )

let al_of_vvbinop : vvbinop -> value list = function
  | V128 vop -> (
    match vop with
    | V128Op.And -> [ nullary "V128"; nullary "AND" ]
    | V128Op.Or -> [ nullary "V128"; nullary "OR" ]
    | V128Op.Xor -> [ nullary "V128"; nullary "XOR" ]
    | V128Op.AndNot -> [ nullary "V128"; nullary "ANDNOT" ]
  )

let al_of_vvternop : vvternop -> value list = function
  | V128 vop -> (
    match vop with
    | V128Op.Bitselect ->
      [ nullary "V128"; nullary "BITSELECT" ]
  )

let al_of_vsplatop : vsplatop -> value list = function
  | V128 vop -> (
    match vop with
    | V128.I8x16 _ -> [ CaseV ("X", [ nullary "I8"; numV sixteen ]) ]
    | V128.I16x8 _ -> [ CaseV ("X", [ nullary "I16"; numV eight ]) ]
    | V128.I32x4 _ -> [ CaseV ("X", [ nullary "I32"; numV four ]) ]
    | V128.I64x2 _ -> [ CaseV ("X", [ nullary "I64"; numV two ]) ]
    | V128.F32x4 _ -> [ CaseV ("X", [ nullary "F32"; numV four ]) ]
    | V128.F64x2 _ -> [ CaseV ("X", [ nullary "F64"; numV two ]) ]
  )

let al_of_vextractop : vextractop -> value list = function
  | V128 vop -> (
    match vop with
    | V128.I8x16 vop' -> (
      match vop' with
      | Extract (n, sx) ->
        [ CaseV ("X", [ nullary "I8"; numV sixteen ]); optV (Some (al_of_sx sx)); al_of_nat8 n; ]
    )
    | V128.I16x8 vop' -> (
      match vop' with
      | Extract (n, sx) ->
        [ CaseV ("X", [ nullary "I16"; numV eight ]); optV (Some (al_of_sx sx)); al_of_nat8 n; ]
    )
    | V128.I32x4 vop' -> (
      match vop' with
      | Extract (n, _) -> [ CaseV ("X", [ nullary "I32"; numV four ]); optV None; al_of_nat8 n ]
    )
    | V128.I64x2 vop' -> (
      match vop' with
      | Extract (n, _) -> [ CaseV ("X", [ nullary "I64"; numV two ]); optV None; al_of_nat8 n ]
    )
    | V128.F32x4 vop' -> (
      match vop' with
      | Extract (n, _) -> [ CaseV ("X", [ nullary "F32"; numV four ]); optV None; al_of_nat8 n ]
    )
    | V128.F64x2 vop' -> (
      match vop' with
      | Extract (n, _) -> [ CaseV ("X", [ nullary "F64"; numV two ]); optV None; al_of_nat8 n ]
    )
  )

let al_of_vreplaceop : vreplaceop -> value list = function
  | V128 vop -> (
    match vop with
    | V128.I8x16 (Replace n) -> [ CaseV ("X", [ nullary "I8"; numV sixteen ]); al_of_nat8 n ]
    | V128.I16x8 (Replace n) -> [ CaseV ("X", [ nullary "I16"; numV eight ]); al_of_nat8 n ]
    | V128.I32x4 (Replace n) -> [ CaseV ("X", [ nullary "I32"; numV four ]); al_of_nat8 n ]
    | V128.I64x2 (Replace n) -> [ CaseV ("X", [ nullary "I64"; numV two ]); al_of_nat8 n ]
    | V128.F32x4 (Replace n) -> [ CaseV ("X", [ nullary "F32"; numV four ]); al_of_nat8 n ]
    | V128.F64x2 (Replace n) -> [ CaseV ("X", [ nullary "F64"; numV two ]); al_of_nat8 n ]
  )
*)


let il_of_packsize = function
  | RI.Pack.Pack8  -> il_of_nat 8
  | RI.Pack.Pack16 -> il_of_nat 16
  | RI.Pack.Pack32 -> il_of_nat 32
  | RI.Pack.Pack64 -> il_of_nat 64

let il_of_packshape = function
  | RI.Pack.Pack8x8  -> [mk_nat 8 ; mk_nat 8]
  | RI.Pack.Pack16x4 -> [mk_nat 16; mk_nat 4]
  | RI.Pack.Pack32x2 -> [mk_nat 32; mk_nat 2]

let il_of_memop f idx (memop: (RI.Types.numtype, 'p) RI.Ast.memop) =
  let str = [("ALIGN" , memop.align  |> Z.of_int |> il_of_uN);
             ("OFFSET", memop.offset |> il_of_uN_64)]
  in
  [il_of_numtype memop.ty; f memop.pack; il_of_memidx idx; mk_str "memarg" str]

let il_of_packsize_sx (ps, sx) =
  let t = t_app "loadop_" [expA (subE (varE ~note:(t_var "Inn") "Inn") (t_var "Inn") (t_var "numtype"))] in
  mk_case t [[];["_"];[]] [il_of_packsize ps; il_of_sx sx]

let il_of_loadop : RI.Ast.idx -> RI.Ast.loadop -> exp list =
  let t = t_app "loadop_" [expA (subE (varE ~note:(t_var "Inn") "Inn") (t_var "Inn") (t_var "numtype"))] |> optT in
  il_of_opt t il_of_packsize_sx |> il_of_memop

let il_of_storeop =
  let t = t_app "storeop_" [expA (subE (varE ~note:(t_var "Inn") "Inn") (t_var "Inn") (t_var "numtype"))] |> optT in
  il_of_opt t il_of_packsize |> il_of_memop

(*
let al_of_vloadop idx vloadop =
  let str =
    Record.empty
    |> Record.add "ALIGN" (al_of_nat vloadop.align)
    |> Record.add "OFFSET" (al_of_nat64 vloadop.offset)
  in

  let vmemop = match vloadop.pack with
  | Option.Some (packsize, vext) -> (
    match vext with
    | Pack.ExtLane (packshape, sx) ->
      CaseV ("SHAPE", al_of_packshape packshape @ [al_of_sx sx])
    | Pack.ExtSplat -> CaseV ("SPLAT", [ al_of_packsize packsize ])
    | Pack.ExtZero -> CaseV ("ZERO", [ al_of_packsize packsize ])
  ) |> Option.some |> optV
  | None -> OptV None in

  al_of_vectype V128T :: vmemop :: al_of_memidx idx @ [ StrV str ]

let al_of_vstoreop idx vstoreop =
  let str =
    Record.empty
    |> Record.add "ALIGN" (al_of_nat vstoreop.align)
    |> Record.add "OFFSET" (al_of_nat64 vstoreop.offset)
  in

  al_of_vectype V128T :: al_of_memidx idx @ [ StrV str ]

let al_of_vlaneop idx vlaneop laneidx =
  let packsize = vlaneop.pack in

  let str =
    Record.empty
    |> Record.add "ALIGN" (al_of_nat vlaneop.align)
    |> Record.add "OFFSET" (al_of_nat64 vlaneop.offset)
  in

  [ al_of_vectype V128T; al_of_packsize packsize ] @ al_of_memidx idx @ [ StrV str; al_of_nat8 laneidx ]
*)



(* Construct instruction *)

let il_of_catch (catch: RI.Ast.catch) =
  let mk_catch c n = mk_case (t_var "catch") ([c] :: List.init n (Fun.const [])) in
  match catch.it with
  | Catch    (idx1, idx2) -> mk_catch "CATCH"         2 [il_of_idx idx1; il_of_idx idx2]
  | CatchRef (idx1, idx2) -> mk_catch "CATCH_REF"     2 [il_of_idx idx1; il_of_idx idx2]
  | CatchAll    idx       -> mk_catch "CATCH_ALL"     1 [il_of_idx idx]
  | CatchAllRef idx       -> mk_catch "CATCH_ALL_REF" 1 [il_of_idx idx]

let rec il_of_instr (instr: RI.Ast.instr) =
  let mk_instr0 = mk_nullary' "instr" in
  let mk_instr c n = mk_case' "instr" ([c] :: List.init n (Fun.const [])) in
  match instr.it with
  (* wasm values *)
  | Const num -> il_of_num num.it
  | VecConst vec -> il_of_vec vec.it
  | RefNull ht -> mk_instr "REF.NULL" 1 [il_of_heaptype ht]
  (* wasm instructions *)
  | Unreachable -> mk_instr0 "UNREACHABLE"
  | Nop  -> mk_instr0 "NOP"
  | Drop -> mk_instr0 "DROP"
  | Unary   op -> mk_instr "UNOP"   2 (il_of_unop     op)
  | Binary  op -> mk_instr "BINOP"  2 (il_of_binop    op)
  | Test    op -> mk_instr "TESTOP" 2 (il_of_testop   op)
  | Compare op -> mk_instr "RELOP"  2 (il_of_relop    op)
  | Convert op -> mk_instr "CVTOP"  3 (il_of_cvtop    op)
  (*
  | VecTest        vop -> mk_instr "VTESTOP" 2 (il_of_vtestop vop)
  | VecCompare     vop -> mk_instr "VRELOP"  2 (il_of_vrelop vop)
  | VecUnary       vop -> mk_instr "VUNOP"   2 (il_of_vunop vop)
  | VecBinary      vop -> (match il_of_vbinop_opt  vop with Some l -> CaseV ("VBINOP" , l) | None -> il_of_special_vbinop  vop)
  | VecTernary     vop -> (match il_of_vternop_opt vop with Some l -> CaseV ("VTERNOP", l) | None -> il_of_special_vternop vop)
  | VecConvert     vop -> (match il_of_vcvtop_opt  vop with Some l -> CaseV ("VCVTOP" , l) | None -> il_of_special_vcvtop  vop)
  | VecShift       vop -> mk_instr "VSHIFTOP"      2 (il_of_vshiftop vop)
  | VecBitmask     vop -> mk_instr "VBITMASK"      1 (il_of_vbitmaskop vop)
  | VecTestBits    vop -> mk_instr "VVTESTOP"      2 (il_of_vvtestop vop)
  | VecUnaryBits   vop -> mk_instr "VVUNOP"        2 (il_of_vvunop vop)
  | VecBinaryBits  vop -> mk_instr "VVBINOP"       2 (il_of_vvbinop vop)
  | VecTernaryBits vop -> mk_instr "VVTERNOP"      2 (il_of_vvternop vop)
  | VecSplat       vop -> mk_instr "VSPLAT"        1 (il_of_vsplatop vop)
  | VecExtract     vop -> mk_instr "VEXTRACT_LANE" 3 (il_of_vextractop vop)
  | VecReplace     vop -> mk_instr "VREPLACE_LANE" 2 (il_of_vreplaceop vop)
  *)
  | RefIsNull -> mk_instr0 "REF.IS_NULL"
  | RefFunc idx     -> mk_instr "REF.FUNC" 1 [il_of_idx idx]
  | Select  vtl_opt -> mk_instr "SELECT"   1 [il_of_opt (optT (t_star "valtype")) (il_of_list (t_star "valtype") il_of_valtype) vtl_opt]
  | LocalGet  idx   -> mk_instr "LOCAL.GET"  1 [il_of_idx idx]
  | LocalSet  idx   -> mk_instr "LOCAL.SET"  1 [il_of_idx idx]
  | LocalTee  idx   -> mk_instr "LOCAL.TEE"  1 [il_of_idx idx]
  | GlobalGet idx   -> mk_instr "GLOBAL.GET" 1 [il_of_idx idx]
  | GlobalSet idx   -> mk_instr "GLOBAL.SET" 1 [il_of_idx idx]
  | TableGet  idx   -> mk_instr "TABLE.GET"  1 [il_of_idx idx]
  | TableSet  idx   -> mk_instr "TABLE.SET"  1 [il_of_idx idx]
  | TableSize idx   -> mk_instr "TABLE.SIZE" 1 [il_of_idx idx]
  | TableGrow idx   -> mk_instr "TABLE.GROW" 1 [il_of_idx idx]
  | TableFill idx   -> mk_instr "TABLE.FILL" 1 [il_of_idx idx]
  | TableCopy (idx1, idx2) -> mk_instr "TABLE.COPY" 2 [il_of_idx idx1; il_of_idx idx2]
  | TableInit (idx1, idx2) -> mk_instr "TABLE.INIT" 2 [il_of_idx idx1; il_of_idx idx2]
  | ElemDrop idx -> mk_instr "ELEM.DROP" 1 [il_of_idx idx]
  | Block (bt, instrs) -> mk_instr "BLOCK" 2 [il_of_blocktype bt; il_of_list (t_star "instr") il_of_instr instrs]
  | Loop  (bt, instrs) -> mk_instr "LOOP"  2 [il_of_blocktype bt; il_of_list (t_star "instr") il_of_instr instrs]
  | If (bt, instrs1, instrs2) ->
    mk_case (t_var "instr") [["IF"];[];["ELSE"];[]] [
      il_of_blocktype bt;
      il_of_list (t_star "instr") il_of_instr instrs1;
      il_of_list (t_star "instr") il_of_instr instrs2;
    ]
  | Br   idx -> mk_instr "BR"    1 [il_of_idx idx]
  | BrIf idx -> mk_instr "BR_IF" 1 [il_of_idx idx]
  | BrTable (idxs, idx) -> mk_instr "BR_TABLE" 2 [il_of_list (t_star "labelidx") il_of_idx idxs; il_of_idx idx]
  | BrOnNull    idx -> mk_instr "BR_ON_NULL"     1 [il_of_idx idx]
  | BrOnNonNull idx -> mk_instr "BR_ON_NON_NULL" 1 [il_of_idx idx]
  | BrOnCast     (idx, rt1, rt2) -> mk_instr "BR_ON_CAST"      3 [il_of_idx idx; il_of_reftype rt1; il_of_reftype rt2]
  | BrOnCastFail (idx, rt1, rt2) -> mk_instr "BR_ON_CAST_FAIL" 3 [il_of_idx idx; il_of_reftype rt1; il_of_reftype rt2]
  | Return -> mk_instr0 "RETURN"
  | Call    idx -> mk_instr "CALL"     1 [il_of_idx idx]
  | CallRef idx -> mk_instr "CALL_REF" 1 [il_of_typeuse_of_idx idx]
  | CallIndirect (idx1, idx2) -> mk_instr "CALL_INDIRECT" 2 [il_of_idx idx1; il_of_typeuse_of_idx idx2]
  | ReturnCall    idx -> mk_instr "RETURN_CALL"     1 [il_of_idx idx]
  | ReturnCallRef idx -> mk_instr "RETURN_CALL_REF" 1 [il_of_typeuse_of_idx idx]
  | ReturnCallIndirect (idx1, idx2) -> mk_instr "RETURN_CALL_INDIRECT" 2 [il_of_idx idx1; il_of_typeuse_of_idx idx2]
  | Throw idx -> mk_instr "THROW" 1 [il_of_idx idx]
  | ThrowRef  -> mk_instr0 "THROW_REF"
  | TryTable (bt, catches, instrs) ->
    mk_instr "TRY_TABLE" 3 [
      il_of_blocktype bt;
      il_of_list (t_app "list" [t_var "catch" |> typA]) il_of_catch catches;
      il_of_list (t_star "instr") il_of_instr instrs
    ]
  | Load    (idx, loadop )         -> mk_instr "LOAD"        4 (il_of_loadop   idx loadop)
  | Store   (idx, storeop)         -> mk_instr "STORE"       4 (il_of_storeop  idx storeop)
  (*
  | VecLoad (idx, vloadop)         -> mk_instr "VLOAD"       4 (il_of_vloadop  idx vloadop)
  | VecLoadLane  (idx, vlaneop, i) -> mk_instr "VLOAD_LANE"  5 (il_of_vlaneop  idx vlaneop i)
  | VecStore     (idx, vstoreop  ) -> mk_instr "VSTORE"      3 (il_of_vstoreop idx vstoreop)
  | VecStoreLane (idx, vlaneop, i) -> mk_instr "VSTORE_LANE" 5 (il_of_vlaneop  idx vlaneop i)
  *)
  | MemorySize idx -> mk_instr "MEMORY.SIZE" 1 [il_of_memidx idx]
  | MemoryGrow idx -> mk_instr "MEMORY.GROW" 1 [il_of_memidx idx]
  | MemoryFill idx -> mk_instr "MEMORY.FILL" 1 [il_of_memidx idx]
  | MemoryCopy (idx1, idx2) -> mk_instr "MEMORY.COPY" 2 [il_of_memidx idx1; il_of_memidx idx2]
  | MemoryInit (idx1, idx2) -> mk_instr "MEMORY.INIT" 2 [il_of_memidx idx1; il_of_idx    idx2]
  | DataDrop idx -> mk_instr "DATA.DROP" 1 [il_of_idx idx]
  | RefAsNonNull -> mk_instr0 "REF.AS_NON_NULL"
  | RefTest rt -> mk_instr "REF.TEST" 1 [il_of_reftype rt]
  | RefCast rt -> mk_instr "REF.CAST" 1 [il_of_reftype rt]
  | RefEq  -> mk_instr0 "REF.EQ"
  | RefI31 -> mk_instr0 "REF.I31"
  | I31Get sx -> mk_instr "I31.GET" 1 [il_of_sx sx]
  | StructNew (idx, Explicit) -> mk_instr "STRUCT.NEW"         1 [il_of_idx idx]
  | StructNew (idx, Implicit) -> mk_instr "STRUCT.NEW_DEFAULT" 1 [il_of_idx idx]
  | StructGet (idx1, idx2, sx_opt) ->
    mk_instr "STRUCT.GET" 3 [
      il_of_opt (t_opt "sx") il_of_sx sx_opt;
      il_of_idx idx1;
      il_of_nat32 idx2;
    ]
  | StructSet (idx1, idx2)     -> mk_instr "STRUCT.SET"        2 [il_of_idx idx1; il_of_nat32 idx2]
  | ArrayNew (idx, Explicit)   -> mk_instr "ARRAY.NEW"         1 [il_of_idx idx]
  | ArrayNew (idx, Implicit)   -> mk_instr "ARRAY.NEW_DEFAULT" 1 [il_of_idx idx]
  | ArrayNewFixed (idx, i32)   -> mk_instr "ARRAY.NEW_FIXED"   2 [il_of_idx idx ; il_of_nat32 i32]
  | ArrayNewElem (idx1, idx2)  -> mk_instr "ARRAY.NEW_ELEM"    2 [il_of_idx idx1; il_of_idx idx2]
  | ArrayNewData (idx1, idx2)  -> mk_instr "ARRAY.NEW_DATA"    2 [il_of_idx idx1; il_of_idx idx2]
  | ArrayGet (idx, sx_opt)     -> mk_instr "ARRAY.GET"         2 [il_of_opt (t_opt "sx") il_of_sx sx_opt; il_of_idx idx]
  | ArraySet idx               -> mk_instr "ARRAY.SET"         1 [il_of_idx idx]
  | ArrayLen                   -> mk_instr0 "ARRAY.LEN"
  | ArrayCopy (idx1, idx2)     -> mk_instr "ARRAY.COPY"        2 [il_of_idx idx1; il_of_idx idx2]
  | ArrayFill idx              -> mk_instr "ARRAY.FILL"        1 [il_of_idx idx]
  | ArrayInitData (idx1, idx2) -> mk_instr "ARRAY.INIT_DATA"   2 [il_of_idx idx1; il_of_idx idx2]
  | ArrayInitElem (idx1, idx2) -> mk_instr "ARRAY.INIT_ELEM"   2 [il_of_idx idx1; il_of_idx idx2]
  | ExternConvert Internalize  -> mk_instr0 "ANY.CONVERT_EXTERN"
  | ExternConvert Externalize  -> mk_instr0 "EXTERN.CONVERT_ANY"
  | _ -> mk_instr0 "TODO: Unconstructed Wasm instruction (il_of_instr)"

let il_of_const (const: RI.Ast.const) = il_of_list (t_star "instr") il_of_instr const.it


(* Construct module *)

let il_of_type (ty: RI.Ast.type_) =
  mk_case' "type" [["TYPE"];[]] [il_of_rectype ty.it]

let il_of_local (local: RI.Ast.local) =
  let Local t = local.it in
  mk_case' "local" [["LOCAL"];[]] [il_of_valtype t]

let il_of_func (func: RI.Ast.func) =
  let Func (idx, locals, body) = func.it in
  mk_case' "func" [["FUNC"];[];[];[]] [
    il_of_idx idx;
    il_of_list (t_star "local") il_of_local locals;
    il_of_list (t_var "expr") il_of_instr body;
  ]

let il_of_global (global: RI.Ast.global) =
  let Global (gt, expr) = global.it in
  mk_case' "global" [["GLOBAL"];[];[]] [il_of_globaltype gt; il_of_const expr]

let il_of_table (table: RI.Ast.table) =
  let Table (tt, expr) = table.it in
  mk_case' "table" [["TABLE"];[];[]] [il_of_tabletype tt; il_of_const expr]

let il_of_memory (memory: RI.Ast.memory) =
  let Memory mt = memory.it in
  mk_case' "mem" [["MEMORY"];[]] [il_of_memorytype mt]

let il_of_tag (tag: RI.Ast.tag) =
  let Tag tt = tag.it in
  mk_case' "tag" [["TAG"];[]] [il_of_tagtype tt]

let il_of_segmentmode (segmentmode: RI.Ast.segmentmode) =
  match segmentmode.it with
  | Passive -> mk_nullary' "datamode" "PASSIVE"
  | Active (index, offset) ->
    mk_case' "datamode" [["ACTIVE"];[];[]] [il_of_idx index; il_of_const offset]
  | Declarative -> error no "datamode: no Declarative constructor"

let il_of_elem (elem: RI.Ast.elem) =
  let Elem (rt, consts, mode) = elem.it in
  mk_case' "elem" [["ELEM"];[];[];[]] [
    il_of_reftype rt;
    il_of_list (t_star "expr") il_of_const consts;
    il_of_segmentmode mode;
  ]

let il_of_data (data: RI.Ast.data) =
  let Data (bytes, mode) = data.it in
  mk_case' "data" [["DATA"];[];[]] [ il_of_bytes bytes; il_of_segmentmode mode ]

let il_of_externtype = function
  | RT.ExternFuncT   (typeuse   ) -> mk_case' "externtype" [["FUNC"  ];[]] [il_of_typeuse    typeuse   ]
  | RT.ExternGlobalT (globaltype) -> mk_case' "externtype" [["GLOBAL"];[]] [il_of_globaltype globaltype]
  | RT.ExternTableT  (tabletype ) -> mk_case' "externtype" [["TABLE" ];[]] [il_of_tabletype  tabletype ]
  | RT.ExternMemoryT (memtype   ) -> mk_case' "externtype" [["MEM"   ];[]] [il_of_memorytype memtype   ]
  | RT.ExternTagT    (tagtype   ) -> mk_case' "externtype" [["TAG"   ];[]] [il_of_tagtype    tagtype   ]

let il_of_import (import: RI.Ast.import)=
  let Import (module_name, item_name, xt) = import.it in
  mk_case' "import" [["IMPORT"];[];[];[]] [il_of_name module_name; il_of_name item_name; il_of_externtype xt]

let il_of_externidx (xt: RI.Ast.externidx) = match xt.it with
  | FuncX   idx -> mk_case' "externidx" [["FUNC"  ];[]] [il_of_idx idx]
  | TableX  idx -> mk_case' "externidx" [["TABLE" ];[]] [il_of_idx idx]
  | MemoryX idx -> mk_case' "externidx" [["MEM"   ];[]] [il_of_idx idx]
  | GlobalX idx -> mk_case' "externidx" [["GLOBAL"];[]] [il_of_idx idx]
  | TagX    idx -> mk_case' "externidx" [["TAG"   ];[]] [il_of_idx idx]

let il_of_start (start: RI.Ast.start) =
  let Start idx = start.it in
  mk_case' "start" [["START"];[]] [il_of_idx idx]

let il_of_export (export: RI.Ast.export) =
  let Export (name, exix) = export.it in
  mk_case' "export" [["EXPORT"];[];[]] [il_of_name name; il_of_externidx exix]


(* Wasm-3: MODULE type* import* tag* global* mem* table* func* data* elem* start? export* *)
let il_of_module (module_: RI.Ast.module_) =
  let es = [
            il_of_list (t_star "type"  ) il_of_type module_.it.types;
            il_of_list (t_star "import") il_of_import module_.it.imports;
            il_of_list (t_star "tag"   ) il_of_tag module_.it.tags;
            il_of_list (t_star "global") il_of_global module_.it.globals;
            il_of_list (t_star "mem"   ) il_of_memory module_.it.memories;
            il_of_list (t_star "table" ) il_of_table module_.it.tables;
            il_of_list (t_star "func"  ) il_of_func module_.it.funcs;
            il_of_list (t_star "data"  ) il_of_data module_.it.datas;
            il_of_list (t_star "elem"  ) il_of_elem module_.it.elems;
            il_of_opt  (t_opt  "start" ) il_of_start module_.it.start;
            il_of_list (t_star "export") il_of_export module_.it.exports;
          ]
  in
  mk_case' "module" [["MODULE"];[];[];[];[];[];[];[];[];[];[];[]] es



(* Destruct *)


(* This function also strips any SubE nodes. *)
let rec match_caseE name exp : string list list * exp list =
  match exp.it with
  | CaseE (tag, { it = TupE es; _ }) -> mixop_to_text tag, es
  | SubE (exp', _, _) -> match_caseE name exp'
  | _ -> error_value (name ^ " (match_caseE)") exp


(* Destruct data structure *)

let il_to_opt (f: exp -> 'a) exp : 'a option = unwrap_opt exp |> Option.map f

let il_to_list (f: exp -> 'a) exp : 'a list = elts_of_list exp |> List.map f

(* For `syntax list(x)`. *)
let il_to_list' (f: exp -> 'a) exp : 'a list =
  match match_caseE "list" exp with
  | [[];[]], [l] -> il_to_list f l
  | _ -> error_value "list" exp

let il_to_seq f s = il_to_list f s |> List.to_seq

let il_to_phrase (f: exp -> 'a) exp : 'a RI.Source.phrase = RI.Source.(f exp @@ no_region)


(* Destruct minor *)

type layout = { width : int; exponent : int; mantissa : int }
let layout32 = { width = 32; exponent = 8; mantissa = 23 }
let layout64 = { width = 64; exponent = 11; mantissa = 52 }

let mask_sign layout = Z.shift_left Z.one (layout.width - 1)
let mask_mag layout = Z.pred (mask_sign layout)
let mask_mant layout = Z.(pred (shift_left one layout.mantissa))
let mask_exp layout = Z.(mask_mag layout - mask_mant layout)
let bias layout = let em1 = layout.exponent - 1 in Z.((one + one)**em1 - one)

let il_to_z_nat num : Z.t =
  match num with
  | `Nat n -> n
  | _ -> error no ("Invalid nat: " ^ Xl.Num.to_string num)
let il_to_z_int num : Z.t =
  match num with
  | `Int i -> i
  | _ -> error no ("Invalid int: " ^ Xl.Num.to_string num)
let z_to_intN signed unsigned z = if z < Z.zero then signed z else unsigned z

let il_to_fmagN layout exp : Z.t =
  match match_caseE "fmagN" exp with
  | [["NORM"];[];[]], [m; n] ->
    Z.(shift_left (il_to_z_int (unwrap_num n) + bias layout) layout.mantissa + il_to_z_nat (unwrap_num m))
  | [["SUBNORM"];[]], [m] -> il_to_z_nat (unwrap_num m)
  | [["INF"]], [] -> mask_exp layout
  | [["NAN"];[]], [m] -> Z.(mask_exp layout + il_to_z_nat (unwrap_num m))
  | _ -> error_value "fmagN" exp

let il_to_floatN layout exp : Z.t =
  match match_caseE "floatN" exp with
  | [["POS"];[]], [mag] -> il_to_fmagN layout mag
  | [["NEG"];[]], [mag] -> Z.(mask_sign layout + il_to_fmagN layout mag)
  | _ -> error_value "floatN" exp

let e64 = Z.(shift_left one 64)
let z_to_vec128 i =
  let hi, lo = Z.div_rem i e64 in
  RI.V128.I64x2.of_lanes [Z.to_int64_unsigned lo; Z.to_int64_unsigned hi]

let il_to_int exp : int =
  match exp.it with
  | NumE e -> il_to_z_nat e |> Z.to_int
  | _ -> error_value "int" exp
(*
let al_to_nat8 (v: value): I8.t = al_to_z_nat v |> Z.to_int |> I8.of_int_u
let al_to_int8 (v: value): I8.t = al_to_z_nat v |> Z.to_int |> I8.of_int_s
let al_to_int16 (v: value): I16.t = al_to_z_nat v |> Z.to_int |> I16.of_int_s
*)

let il_to_nat32   exp : RI.I32.t = unwrap_num exp |> il_to_z_nat |> z_to_intN Z.to_int32 Z.to_int32_unsigned
let il_to_nat64   exp : RI.I64.t = unwrap_num exp |> il_to_z_nat |> z_to_intN Z.to_int64 Z.to_int64_unsigned
let il_to_vec128  exp : RI.V128.t = unwrap_num exp |> il_to_z_nat |> z_to_vec128
let il_to_float32 exp : RI.F32.t = il_to_floatN layout32 exp |> Z.to_int32_unsigned |> RI.F32.of_bits
let il_to_float64 exp : RI.F64.t = il_to_floatN layout64 exp |> Z.to_int64_unsigned |> RI.F64.of_bits

let il_to_uN_32 exp : RI.I32.t = il_to_nat32 (unwrap_case exp)
let il_to_uN_64 exp : RI.I64.t = il_to_nat64 (unwrap_case exp)

let il_to_idx exp : RI.Ast.idx = il_to_phrase il_to_uN_32 exp
let il_to_byte exp : Char.t = il_to_nat exp |> Z.to_int |> Char.chr
let il_to_bytes exp : string = il_to_seq il_to_byte exp |> String.of_seq
let il_to_string exp =
  match exp.it with
  | TextE str -> str
  | _ -> error_value "text" exp
let il_to_name name = name |> il_to_string |> Utf8.decode
let il_to_bool exp = match exp.it with
  | BoolE b -> b
  | _ -> error_value "bool" exp


(* Destruct type *)


let il_to_null exp : RI.Types.null =
  match exp.it with
  | OptE None -> NoNull
  | OptE _ -> Null
  | _ -> error_value "null" exp

let il_to_final exp : RI.Types.final =
  match exp.it with
  | OptE None -> NoFinal
  | OptE _ -> Final
  | _ -> error_value "final" exp

let il_to_mut exp : RI.Types.mut =
  match exp.it with
  | OptE None -> Cons
  | OptE _ -> Var
  | _ -> error_value "mut" exp

let rec il_to_storagetype exp : RI.Types.storagetype =
  match match_caseE "storagetype" exp with
  | [["I8"]] , [] -> PackStorageT I8T
  | [["I16"]], [] -> PackStorageT I16T
  | _ -> ValStorageT (il_to_valtype exp)

and il_to_fieldtype exp : RI.Types.fieldtype =
  match match_caseE "fieldtype" exp with
  | [[];[]], [mut; st] -> FieldT (il_to_mut mut, il_to_storagetype st)
  | _ -> error_value "fieldtype" exp

and il_to_resulttype exp : RI.Types.resulttype =
  il_to_list' il_to_valtype exp

and il_to_comptype exp : RI.Types.comptype =
  match match_caseE "comptype" exp with
  | [["STRUCT"];[]], [ftl] -> StructT (il_to_list' il_to_fieldtype ftl)
  | [["ARRAY"];[]], [ft] -> ArrayT (il_to_fieldtype ft)
  | [["FUNC"];["->"];[]], [rt1; rt2] -> FuncT (il_to_resulttype rt1, il_to_resulttype rt2)
  | _ -> error_value "comptype" exp

and il_to_subtype exp : RI.Types.subtype =
  match match_caseE "subtype" exp with
  | [["SUB"];[];[];[]], [fin; tul; st] ->
    SubT (il_to_final fin, il_to_list il_to_typeuse tul, il_to_comptype st)
  | _ -> error_value "subtype" exp

and il_to_rectype exp : RI.Types.rectype =
  match match_caseE "rectype" exp with
  | [["REC"];[]], [stl] -> RecT (il_to_list' il_to_subtype stl)
  | _ -> error_value "rectype" exp

and il_to_deftype exp : RI.Types.deftype =
  match match_caseE "deftype" exp with
  | [["_DEF"];[];[]], [rt; i32] -> DefT (il_to_rectype rt, il_to_nat32 i32)
  | _ -> error_value "deftype" exp

and il_to_typeuse exp : RI.Types.typeuse =
  match match_caseE "typeuse" exp with
  | [["_IDX"];[]]   , [ idx ] -> Idx (il_to_idx idx).it
  | [["REC"];[]]    , [ n ]   -> Rec (il_to_nat32 n)
  | [["_DEF"];[];[]], _       -> Def (il_to_deftype exp)
  | v -> error_value "typeuse" exp

and il_to_idx_of_typeuse exp : RI.Ast.idx =
  match match_caseE "idx_of_typeuse" exp with
  | [["_IDX"];[]], [idx] -> il_to_idx idx
  | _ -> error_value "idx_of_typeuse" exp

and il_to_heaptype exp : RI.Types.heaptype =
  match exp.it with
  | CaseE (tag, _) ->
    (match mixop_to_text tag with
    | [["BOT"]]                      -> BotHT
    | [["ANY"]]                      -> AnyHT
    | [["NONE"]]                     -> NoneHT
    | [["EQ"]]                       -> EqHT
    | [["I31"]]                      -> I31HT
    | [["STRUCT"]]                   -> StructHT
    | [["ARRAY"]]                    -> ArrayHT
    | [["FUNC"]] | [["FUNCREF"]]     -> FuncHT
    | [["NOFUNC"]]                   -> NoFuncHT
    | [["EXN"]] | [["EXNREF"]]       -> ExnHT
    | [["NOEXN"]]                    -> NoExnHT
    | [["EXTERN"]] | [["EXTERNREF"]] -> ExternHT
    | [["NOEXTERN"]]                 -> NoExternHT
    | ([["_IDX"];[]] | [["REC"];[]] | [["_DEF"];[];[]]) -> UseHT (il_to_typeuse exp)
    | _ -> error exp.at ("Invalid heaptype: " ^ string_of_exp exp)
    )
  | _ -> error exp.at ("Invalid heaptype: " ^ string_of_exp exp)

and il_to_reftype exp : RI.Types.reftype =
  match match_caseE "reftype" exp with
  | [["REF"];[];[]], [n; ht] -> il_to_null n, il_to_heaptype ht
  | _ -> error_value "reftype" exp

and il_to_addrtype exp : RI.Types.addrtype =
  match match_caseE "addrtype" exp with
  | [["I32"]], [] -> I32AT
  | [["I64"]], [] -> I64AT
  | _ -> error_value "addrtype" exp

and il_to_numtype exp : RI.Types.numtype =
  match match_caseE "numtype" exp with
  | [["I32"]], [] -> I32T
  | [["I64"]], [] -> I64T
  | [["F32"]], [] -> F32T
  | [["F64"]], [] -> F64T
  | _ -> error_value "numtype" exp

and il_to_packtype exp : RI.Types.packtype =
  match match_caseE "packtype" exp with
  | [["I8" ]], [] -> I8T
  | [["I16"]], [] -> I16T
  | _ -> error_value "packtype" exp

and il_to_valtype exp : RI.Types.valtype =
  match match_caseE "valtype" exp with
  | [["I32"]], _ | [["I64"]], _ | [["F32"]], _ | [["F64"]], _ -> NumT (il_to_numtype exp)
  | [["V128"]], [] -> VecT V128T
  | [["REF"];[];[]], _ -> RefT (il_to_reftype exp)
  | [["BOT"]], [] -> BotT
  | _ -> error_value "valtype" exp

let il_to_blocktype exp : RI.Ast.blocktype =
  match match_caseE "blocktype" exp with
  | [["_IDX"];[]], [idx] -> VarBlockType (il_to_idx idx)
  | [["_RESULT"];[]], [vt_opt] -> ValBlockType (il_to_opt il_to_valtype vt_opt)
  | _ -> error_value "blocktype" exp

let il_to_limits (default: int64) exp : RI.Types.limits =
  match match_caseE "limits" exp with
  | [["["];[".."];["]"]], [min; omax] ->
    { min = il_to_uN_64 min; max = il_to_opt il_to_uN_64 omax }
  | _ -> error_value "limits" exp

let il_to_globaltype exp : RI.Types.globaltype =
  match match_caseE "globaltype" exp with
  | [[];[];[]], [mut; vt] -> GlobalT (il_to_mut mut, il_to_valtype vt)
  | _ -> error_value "globaltype" exp

let il_to_tabletype exp : RI.Types.tabletype =
  match match_caseE "tabletype" exp with
  | [[];[];[];[]], [at; limits; rt] ->
    TableT (il_to_addrtype at, il_to_limits default_table_max limits, il_to_reftype rt)
  | _ -> error_value "tabletype" exp

let il_to_memorytype exp : RI.Types.memorytype =
  match match_caseE "memorytype" exp with
  | [[];[];["PAGE"]], [at; limits] -> MemoryT (il_to_addrtype at, il_to_limits default_memory_max limits)
  | _ -> error_value "memorytype" exp

let il_to_tagtype exp : RI.Types.tagtype = TagT (il_to_typeuse exp)


(* Destruct operator *)

let num i = `Nat (Z.of_int i)
let two = num 2
let four = num 4
let eight = num 8
let sixteen = num 16
let thirtytwo = num 32
let sixtyfour = num 64

let il_to_sx exp : RI.Pack.sx =
  match match_caseE "sx" exp with
  | [["S"]], [] -> RI.Pack.S
  | [["U"]], [] -> RI.Pack.U
  | _ -> error_value "sx" exp

let il_to_op f1 f2 exps : ('i32, 'i64, 'f32, 'f64) RI.Value.op =
  match exps with
  | [numtype; op] ->
    (match match_caseE "op numtype" numtype with
    | [["I32"]], [] -> RI.Value.I32 (f1 op)
    | [["I64"]], [] -> RI.Value.I64 (f1 op)
    | [["F32"]], [] -> RI.Value.F32 (f2 op)
    | [["F64"]], [] -> RI.Value.F64 (f2 op)
    | _ -> error_value "op numtype" numtype
    )
  | _ -> error_values "op" exps

let il_to_int_unop exp : RI.Ast.IntOp.unop =
  let open RI in
  let open Ast in
  match match_caseE "interger unop" exp with
  | [["CLZ"]], []    -> IntOp.Clz
  | [["CTZ"]], []    -> IntOp.Ctz
  | [["POPCNT"]], [] -> IntOp.Popcnt
  | [["EXTEND"];[]], [z] when unwrap_num z = eight     -> IntOp.ExtendS Pack.Pack8
  | [["EXTEND"];[]], [z] when unwrap_num z = sixteen   -> IntOp.ExtendS Pack.Pack16
  | [["EXTEND"];[]], [z] when unwrap_num z = thirtytwo -> IntOp.ExtendS Pack.Pack32
  | [["EXTEND"];[]], [z] when unwrap_num z = sixtyfour -> IntOp.ExtendS Pack.Pack64
  | _ -> error_value "integer unop" exp
let il_to_float_unop exp : RI.Ast.FloatOp.unop =
  let open RI in
  let open Ast in
  match match_caseE "float unop" exp with
  | [["NEG"]]    , [] -> FloatOp.Neg
  | [["ABS"]]    , [] -> FloatOp.Abs
  | [["CEIL"]]   , [] -> FloatOp.Ceil
  | [["FLOOR"]]  , [] -> FloatOp.Floor
  | [["TRUNC"]]  , [] -> FloatOp.Trunc
  | [["NEAREST"]], [] -> FloatOp.Nearest
  | [["SQRT"]]   , [] -> FloatOp.Sqrt
  | _ -> error_value "float unop" exp
let il_to_unop : exp list -> RI.Ast.unop = il_to_op il_to_int_unop il_to_float_unop


let il_to_int_binop exp : RI.Ast.IntOp.binop =
  let open RI in
  let open Ast in
  match match_caseE "integer binop" exp with
  | [["ADD"]], [] -> IntOp.Add
  | [["SUB"]], [] -> IntOp.Sub
  | [["MUL"]], [] -> IntOp.Mul
  | [["DIV"];[]], [sx] -> IntOp.Div (il_to_sx sx)
  | [["REM"];[]], [sx] -> IntOp.Rem (il_to_sx sx)
  | [["AND"]], [] -> IntOp.And
  | [["OR" ]], [] -> IntOp.Or
  | [["XOR"]], [] -> IntOp.Xor
  | [["SHL"]], [] -> IntOp.Shl
  | [["SHR"];[]], [sx] -> IntOp.Shr (il_to_sx sx)
  | [["ROTL"]], [] -> IntOp.Rotl
  | [["ROTR"]], [] -> IntOp.Rotr
  | _ -> error_value "integer binop" exp
let il_to_float_binop exp : RI.Ast.FloatOp.binop =
  let open RI in
  let open Ast in
  match match_caseE "float binop" exp with
  | [["ADD"]], [] -> FloatOp.Add
  | [["SUB"]], [] -> FloatOp.Sub
  | [["MUL"]], [] -> FloatOp.Mul
  | [["DIV"]], [] -> FloatOp.Div
  | [["MIN"]], [] -> FloatOp.Min
  | [["MAX"]], [] -> FloatOp.Max
  | [["COPYSIGN"]], [] -> FloatOp.CopySign
  | _ -> error_value "float binop" exp
let il_to_binop : exp list -> RI.Ast.binop = il_to_op il_to_int_binop il_to_float_binop

let il_to_int_testop exp : RI.Ast.IntOp.testop =
  match match_caseE "testop" exp with
  | [["EQZ"]], [] -> RI.Ast.IntOp.Eqz
  | _ -> error_value "integer testop" exp
let il_to_testop exps : RI.Ast.testop =
  match exps with
  | [numtype; op] ->
    (match match_caseE "testop numtype" numtype with
    | [["I32"]], [] -> RI.Value.I32 (il_to_int_testop op)
    | [["I64"]], [] -> RI.Value.I64 (il_to_int_testop op)
    | _ -> error_value "testop numtype" numtype
    )
  | _ -> error_values "testop" exps

let il_to_int_relop exp : RI.Ast.IntOp.relop =
  let open RI.Ast in
  match match_caseE "integer relop" exp with
  | [["EQ"]], [] -> IntOp.Eq
  | [["NE"]], [] -> IntOp.Ne
  | [["LT"];[]], [sx] -> IntOp.Lt (il_to_sx sx)
  | [["GT"];[]], [sx] -> IntOp.Gt (il_to_sx sx)
  | [["LE"];[]], [sx] -> IntOp.Le (il_to_sx sx)
  | [["GE"];[]], [sx] -> IntOp.Ge (il_to_sx sx)
  | _ -> error_value "integer relop" exp
let il_to_float_relop exp : RI.Ast.FloatOp.relop =
  let open RI.Ast in
  match match_caseE "float relop" exp with
  | [["EQ"]], [] -> FloatOp.Eq
  | [["NE"]], [] -> FloatOp.Ne
  | [["LT"]], [] -> FloatOp.Lt
  | [["GT"]], [] -> FloatOp.Gt
  | [["LE"]], [] -> FloatOp.Le
  | [["GE"]], [] -> FloatOp.Ge
  | _ -> error_value "float relop" exp
let il_to_relop : exp list -> RI.Ast.relop = il_to_op il_to_int_relop il_to_float_relop

let il_to_int_cvtop exps : RI.Ast.IntOp.cvtop =
  let open RI.Ast in
  match exps with
  | [_; numtype2; op] ->
    (match match_caseE "integer cvtop numtype2" numtype2, match_caseE "integer cvtop op" op with
    | ([["I32"]], []), ([["EXTEND"];[]], [sx]) -> IntOp.ExtendI32 (il_to_sx sx)
    | ([["I64"]], []), ([["WRAP"]], []) -> IntOp.WrapI64
    | ([["F32"]], []), ([["TRUNC"];[]], [sx]) -> IntOp.TruncF32 (il_to_sx sx)
    | ([["F64"]], []), ([["TRUNC"];[]], [sx]) -> IntOp.TruncF64 (il_to_sx sx)
    | ([["F32"]], []), ([["TRUNC_SAT"];[]], [sx]) -> IntOp.TruncSatF32 (il_to_sx sx)
    | ([["F64"]], []), ([["TRUNC_SAT"];[]], [sx]) -> IntOp.TruncSatF64 (il_to_sx sx)
    | _, ([["REINTERPRET"]], []) -> IntOp.ReinterpretFloat
    | _ -> error_values "integer cvtop [numtype2; op]" [numtype2; op]
    )
  | _ -> error_values "integer cvtop" exps
let il_to_float_cvtop exps : RI.Ast.FloatOp.cvtop =
  let open RI.Ast in
  match exps with
  | [_; numtype2; op] ->
    (match match_caseE "float cvtop numtype2" numtype2, match_caseE "float cvtop op" op with
    | ([["I32"]], []), ([["CONVERT"];[]], [sx]) -> FloatOp.ConvertI32 (il_to_sx sx)
    | ([["I64"]], []), ([["CONVERT"];[]], [sx]) -> FloatOp.ConvertI64 (il_to_sx sx)
    | ([["F32"]], []), ([["PROMOTE"]], []) -> FloatOp.PromoteF32
    | ([["F64"]], []), ([["DEMOTE"]], []) -> FloatOp.DemoteF64
    | _, ([["REINTERPRET"]], []) -> FloatOp.ReinterpretInt
    | l -> error_values "float cvtop [numtype2; op]" [numtype2; op]
    )
  | _ -> error_values "float cvtop" exps
let il_to_cvtop exps : RI.Ast.cvtop =
  match exps with
  | numtype :: _ ->
    (match match_caseE "cvtop" numtype with
    | [["I32"]], [] -> I32 (il_to_int_cvtop exps)
    | [["I64"]], [] -> I64 (il_to_int_cvtop exps)
    | [["F32"]], [] -> F32 (il_to_float_cvtop exps)
    | [["F64"]], [] -> F64 (il_to_float_cvtop exps)
    | _ -> error_value "cvtop" numtype
    )
  | _ ->  error_values "cvtop" exps


(*
(* Vector operator *)

let al_to_vop f1 f2 = function
  | [ CaseV ("X", [ CaseV ("I8", []); NumV z ]); vop ] when z = sixteen -> V128 (V128.I8x16 (f1 vop))
  | [ CaseV ("X", [ CaseV ("I16", []); NumV z ]); vop ] when z = eight -> V128 (V128.I16x8 (f1 vop))
  | [ CaseV ("X", [ CaseV ("I32", []); NumV z ]); vop ] when z = four -> V128 (V128.I32x4 (f1 vop))
  | [ CaseV ("X", [ CaseV ("I64", []); NumV z ]); vop ] when z = two -> V128 (V128.I64x2 (f1 vop))
  | [ CaseV ("X", [ CaseV ("F32", []); NumV z ]); vop ] when z = four -> V128 (V128.F32x4 (f2 vop))
  | [ CaseV ("X", [ CaseV ("F64", []); NumV z ]); vop ] when z = two -> V128 (V128.F64x2 (f2 vop))
  | l -> error_values "vop" l

let al_to_vvop f = function
  | [ CaseV ("V128", []); vop ] -> V128 (f vop)
  | l -> error_values "vvop" l

let al_to_int_vtestop : value -> V128Op.itestop = function
  | CaseV ("ALL_TRUE", []) -> V128Op.AllTrue
  | v -> error_value "integer vtestop" v

let al_to_float_vtestop : value -> Ast.void = function
  | v -> error_value "float vtestop" v

let al_to_vtestop : value list -> vtestop =
  al_to_vop al_to_int_vtestop al_to_float_vtestop

let al_to_vbitmaskop : value list -> vbitmaskop = function
  | [ CaseV ("X", [ CaseV ("I8", []); NumV z ]) ] when z = sixteen -> V128 (V128.I8x16 (V128Op.Bitmask))
  | [ CaseV ("X", [ CaseV ("I16", []); NumV z ]) ] when z = eight -> V128 (V128.I16x8 (V128Op.Bitmask))
  | [ CaseV ("X", [ CaseV ("I32", []); NumV z ]) ] when z = four -> V128 (V128.I32x4 (V128Op.Bitmask))
  | [ CaseV ("X", [ CaseV ("I64", []); NumV z ]) ] when z = two -> V128 (V128.I64x2 (V128Op.Bitmask))
  | l -> error_values "vbitmaskop" l

let al_to_int_vrelop : value -> V128Op.irelop = function
  | CaseV ("EQ", []) -> V128Op.Eq
  | CaseV ("NE", []) -> V128Op.Ne
  | CaseV ("LT", [sx]) -> V128Op.Lt (al_to_sx sx)
  | CaseV ("LE", [sx]) -> V128Op.Le (al_to_sx sx)
  | CaseV ("GT", [sx]) -> V128Op.Gt (al_to_sx sx)
  | CaseV ("GE", [sx]) -> V128Op.Ge (al_to_sx sx)
  | v -> error_value "integer vrelop" v

let al_to_float_vrelop : value -> V128Op.frelop = function
  | CaseV ("EQ", []) -> V128Op.Eq
  | CaseV ("NE", []) -> V128Op.Ne
  | CaseV ("LT", []) -> V128Op.Lt
  | CaseV ("LE", []) -> V128Op.Le
  | CaseV ("GT", []) -> V128Op.Gt
  | CaseV ("GE", []) -> V128Op.Ge
  | v -> error_value "float vrelop" v

let al_to_vrelop : value list -> vrelop =
  al_to_vop al_to_int_vrelop al_to_float_vrelop

let al_to_int_vunop : value -> V128Op.iunop = function
  | CaseV ("ABS", []) -> V128Op.Abs
  | CaseV ("NEG", []) -> V128Op.Neg
  | CaseV ("POPCNT", []) -> V128Op.Popcnt
  | v -> error_value "integer vunop" v

let al_to_float_vunop : value -> V128Op.funop = function
  | CaseV ("ABS", []) -> V128Op.Abs
  | CaseV ("NEG", []) -> V128Op.Neg
  | CaseV ("SQRT", []) -> V128Op.Sqrt
  | CaseV ("CEIL", []) -> V128Op.Ceil
  | CaseV ("FLOOR", []) -> V128Op.Floor
  | CaseV ("TRUNC", []) -> V128Op.Trunc
  | CaseV ("NEAREST", []) -> V128Op.Nearest
  | v -> error_value "float vunop" v

let al_to_vunop : value list -> vunop =
  al_to_vop al_to_int_vunop al_to_float_vunop

let al_to_int_vbinop : value -> V128Op.ibinop = function
  | CaseV ("ADD", []) -> V128Op.Add
  | CaseV ("SUB", []) -> V128Op.Sub
  | CaseV ("MUL", []) -> V128Op.Mul
  | CaseV ("MIN", [sx]) -> V128Op.Min (al_to_sx sx)
  | CaseV ("MAX", [sx]) -> V128Op.Max (al_to_sx sx)
  | CaseV ("AVGR", []) -> V128Op.AvgrU
  | CaseV ("ADD_SAT", [sx]) -> V128Op.AddSat (al_to_sx sx)
  | CaseV ("SUB_SAT", [sx]) -> V128Op.SubSat (al_to_sx sx)
  | CaseV ("Q15MULR_SAT", [(*CaseV ("S", [])*)]) -> V128Op.Q15MulRSatS
  | CaseV ("RELAXED_Q15MULR", [(*CaseV ("S", [])*)]) -> V128Op.RelaxedQ15MulRS
  | v -> error_value "integer vbinop" v

let al_to_float_vbinop : value -> V128Op.fbinop = function
  | CaseV ("ADD", []) -> V128Op.Add
  | CaseV ("SUB", []) -> V128Op.Sub
  | CaseV ("MUL", []) -> V128Op.Mul
  | CaseV ("DIV", []) -> V128Op.Div
  | CaseV ("MIN", []) -> V128Op.Min
  | CaseV ("MAX", []) -> V128Op.Max
  | CaseV ("PMIN", []) -> V128Op.Pmin
  | CaseV ("PMAX", []) -> V128Op.Pmax
  | CaseV ("RELAXED_MIN", []) -> V128Op.RelaxedMin
  | CaseV ("RELAXED_MAX", []) -> V128Op.RelaxedMax
  | v -> error_value "float vbinop" v

let al_to_vbinop : value list -> vbinop = al_to_vop al_to_int_vbinop al_to_float_vbinop

let al_to_int_vternop : value -> V128Op.iternop = function
  | CaseV ("RELAXED_LANESELECT", []) -> V128Op.RelaxedLaneselect
  | v -> error_value "integer vternop" v

let al_to_float_vternop : value -> V128Op.fternop = function
  | CaseV ("RELAXED_MADD", []) -> V128Op.RelaxedMadd
  | CaseV ("RELAXED_NMADD", []) -> V128Op.RelaxedNmadd
  | v -> error_value "float vternop" v

let al_to_vternop : value list -> vternop = al_to_vop al_to_int_vternop al_to_float_vternop

let al_to_half : value -> V128Op.half = function
  | CaseV ("HIGH", []) -> V128Op.High
  | CaseV ("LOW", []) -> V128Op.Low
  | v -> error_value "half" v

let al_to_special_vbinop = function
  | CaseV ("VSWIZZLOP", [ CaseV ("X", [ CaseV ("I8", []); NumV z ]); op ]) as v when z = sixteen ->
    (match op with
    | CaseV ("SWIZZLE", []) -> V128 (V128.I8x16 (V128Op.Swizzle))
    | CaseV ("RELAXED_SWIZZLE", []) -> V128 (V128.I8x16 (V128Op.RelaxedSwizzle))
    | _ ->  error_value "special vbinop" v)
  | CaseV ("VSWIZZLE", [ CaseV ("X", [ CaseV ("I8", []); NumV z ]) ]) when z = sixteen && !version <= 2 -> V128 (V128.I8x16 (V128Op.Swizzle))
  | CaseV ("VSHUFFLE", [ CaseV ("X", [ CaseV ("I8", []); NumV z ]); l ]) when z = sixteen -> V128 (V128.I8x16 (V128Op.Shuffle (al_to_list al_to_nat8 l)))
  | CaseV ("VNARROW", [ CaseV ("X", [ CaseV ("I8", []); NumV z1 ]); CaseV ("X", [ CaseV ("I16", []); NumV z2 ]); CaseV ("S", []) ]) when z1 = sixteen && z2 = eight -> V128 (V128.I8x16 V128Op.(Narrow S))
  | CaseV ("VNARROW", [ CaseV ("X", [ CaseV ("I16", []); NumV z1 ]); CaseV ("X", [ CaseV ("I32", []); NumV z2 ]); CaseV ("S", []) ]) when z1 = eight && z2 = four -> V128 (V128.I16x8 V128Op.(Narrow S))
  | CaseV ("VNARROW", [ CaseV ("X", [ CaseV ("I8", []); NumV z1 ]); CaseV ("X", [ CaseV ("I16", []); NumV z2 ]); CaseV ("U", []) ]) when z1 = sixteen && z2 = eight -> V128 (V128.I8x16 V128Op.(Narrow U))
  | CaseV ("VNARROW", [ CaseV ("X", [ CaseV ("I16", []); NumV z1 ]); CaseV ("X", [ CaseV ("I32", []); NumV z2 ]); CaseV ("U", []) ]) when z1 = eight && z2 = four -> V128 (V128.I16x8 V128Op.(Narrow U))
  | CaseV ("VEXTBINOP", [ c1; c2; ext ]) as v ->
    let ext' =
      match ext with
      | CaseV ("EXTMUL", [half; sx]) -> V128Op.(ExtMul (al_to_half half, al_to_sx sx))
      | CaseV ("DOT", [(*CaseV ("S", [])*)]) -> V128Op.DotS
      | CaseV ("RELAXED_DOT", [(*CaseV ("S", [])*)]) -> V128Op.RelaxedDot
      | _ -> error_value "special vextbinop operator" ext
    in
    (match c1, c2 with
    | CaseV ("X", [ CaseV ("I16", []); NumV z1 ]), CaseV ("X", [ CaseV ("I8", []); NumV z2 ]) when z1 = eight && z2 = sixteen -> V128 (V128.I16x8 ext')
    | CaseV ("X", [ CaseV ("I32", []); NumV z1 ]), CaseV ("X", [ CaseV ("I16", []); NumV z2 ]) when z1 = four && z2 = eight -> V128 (V128.I32x4 ext')
    | CaseV ("X", [ CaseV ("I64", []); NumV z1 ]), CaseV ("X", [ CaseV ("I32", []); NumV z2 ]) when z1 = two && z2 = four -> V128 (V128.I64x2 ext')
    | _   -> error_value "special vextbinop shapes" v)
  | v -> error_value "special vbinop" v

let al_to_special_vternop = function
  | CaseV ("VEXTTERNOP", [ c1; c2; ext ]) as v ->
    let ext' =
      match ext with
      | CaseV ("RELAXED_DOT_ADD", [(*CaseV ("S", [])*)]) -> V128Op.RelaxedDotAddS
      | _ -> error_value "special vextternop operator" ext
    in
    (match c1, c2 with
    | CaseV ("X", [ CaseV ("I32", []); NumV z1 ]), CaseV ("X", [ CaseV ("I8", []); NumV z2 ]) when z1 = four && z2 = sixteen -> V128 (V128.I32x4 ext')
    | _   -> error_value "special vextternop shapes" v)
  | v -> error_value "special vternop" v

let al_to_int_vcvtop : value list -> V128Op.icvtop = function
  | [ _sh; CaseV ("EXTEND", [ half; sx ] ) ] -> V128Op.Extend (al_to_half half, al_to_sx sx)
  | [ sh; CaseV ("TRUNC_SAT", [ sx; _zero ] ) ] as l -> (
      match sh with
      | CaseV ("X", [ CaseV ("F32", []); NumV z ]) when z = four -> V128Op.TruncSatF32x4 (al_to_sx sx)
      | CaseV ("X", [ CaseV ("F64", []); NumV z ]) when z = two -> V128Op.TruncSatZeroF64x2 (al_to_sx sx)
      | _ -> error_values "integer vcvtop" l
    )
  | [ sh; CaseV ("RELAXED_TRUNC", [ sx; _zero ] ) ] as l -> (
      match sh with
      | CaseV ("X", [ CaseV ("F32", []); NumV z ]) when z = four -> V128Op.RelaxedTruncF32x4 (al_to_sx sx)
      | CaseV ("X", [ CaseV ("F64", []); NumV z ]) when z = two -> V128Op.RelaxedTruncZeroF64x2 (al_to_sx sx)
      | _ -> error_values "integer vcvtop" l
    )
  | l -> error_values "integer vcvtop" l

let al_to_float_vcvtop : value list -> V128Op.fcvtop = function
  | [ _sh; CaseV ("DEMOTE", [ _zero ]) ] -> V128Op.DemoteZeroF64x2
  | [ _sh; CaseV ("CONVERT", [ _half; sx ]) ] -> V128Op.ConvertI32x4 (al_to_sx sx)
  | [ _sh; CaseV ("PROMOTE", [ ]) ] -> V128Op.PromoteLowF32x4
  | l -> error_values "float vcvtop" l

let al_to_vcvtop : value list -> vcvtop = function
  | CaseV ("X", [ CaseV ("I8", []); NumV z ]) :: op when z = sixteen -> V128 (V128.I8x16 (al_to_int_vcvtop op))
  | CaseV ("X", [ CaseV ("I16", []); NumV z ]) :: op when z = eight -> V128 (V128.I16x8 (al_to_int_vcvtop op))
  | CaseV ("X", [ CaseV ("I32", []); NumV z ]) :: op when z = four -> V128 (V128.I32x4 (al_to_int_vcvtop op))
  | CaseV ("X", [ CaseV ("I64", []); NumV z ]) :: op when z = two -> V128 (V128.I64x2 (al_to_int_vcvtop op))
  | CaseV ("X", [ CaseV ("F32", []); NumV z ]) :: op when z = four -> V128 (V128.F32x4 (al_to_float_vcvtop op))
  | CaseV ("X", [ CaseV ("F64", []); NumV z ]) :: op when z = two -> V128 (V128.F64x2 (al_to_float_vcvtop op))
  | l -> error_values "vcvtop" l

let al_to_special_vcvtop = function
  | [ CaseV ("X", [ CaseV ("I16", []); NumV z1 ]); CaseV ("X", [ CaseV ("I8", []); NumV z2 ]); CaseV ("EXTADD_PAIRWISE", [ sx ]) ] when z1 = eight && z2 = sixteen ->
    V128 (V128.I16x8 (V128Op.ExtAddPairwise (al_to_sx sx)))
  | [ CaseV ("X", [ CaseV ("I32", []); NumV z1 ]); CaseV ("X", [ CaseV ("I16", []); NumV z2 ]); CaseV ("EXTADD_PAIRWISE", [ sx ]) ] when z1 = four && z2 = eight ->
    V128 (V128.I32x4 (V128Op.ExtAddPairwise (al_to_sx sx)))
  | l -> error_values "special vcvtop" l

let al_to_int_vshiftop : value -> V128Op.ishiftop = function
  | CaseV ("SHL", []) -> V128Op.Shl
  | CaseV ("SHR", [sx]) -> V128Op.Shr (al_to_sx sx)
  | v -> error_value "integer vshiftop" v
let al_to_float_vshiftop : value -> void = error_value "float vshiftop"
let al_to_vshiftop : value list -> vshiftop = al_to_vop al_to_int_vshiftop al_to_float_vshiftop

let al_to_vvtestop' : value -> V128Op.vtestop = function
  | CaseV ("ANY_TRUE", []) -> V128Op.AnyTrue
  | v -> error_value "vvtestop" v
let al_to_vvtestop : value list -> vvtestop = al_to_vvop al_to_vvtestop'

let al_to_vvunop' : value -> V128Op.vunop = function
  | CaseV ("NOT", []) -> V128Op.Not
  | v -> error_value "vvunop" v
let al_to_vvunop : value list -> vvunop = al_to_vvop al_to_vvunop'

let al_to_vvbinop' = function
  | CaseV ("AND", []) -> V128Op.And
  | CaseV ("OR", []) -> V128Op.Or
  | CaseV ("XOR", []) -> V128Op.Xor
  | CaseV ("ANDNOT", []) -> V128Op.AndNot
  | v -> error_value "vvbinop" v
let al_to_vvbinop : value list -> vvbinop = al_to_vvop al_to_vvbinop'

let al_to_vvternop' : value -> V128Op.vternop = function
  | CaseV ("BITSELECT", []) -> V128Op.Bitselect
  | v -> error_value "vvternop" v
let al_to_vvternop : value list -> vvternop = al_to_vvop al_to_vvternop'

let al_to_vsplatop : value list -> vsplatop = function
  | [ CaseV ("X", [ CaseV ("I8", []); NumV z ]) ] when z = sixteen -> V128 (V128.I8x16 Splat)
  | [ CaseV ("X", [ CaseV ("I16", []); NumV z ]) ] when z = eight -> V128 (V128.I16x8 Splat)
  | [ CaseV ("X", [ CaseV ("I32", []); NumV z ]) ] when z = four -> V128 (V128.I32x4 Splat)
  | [ CaseV ("X", [ CaseV ("I64", []); NumV z ]) ] when z = two -> V128 (V128.I64x2 Splat)
  | [ CaseV ("X", [ CaseV ("F32", []); NumV z ]) ] when z = four -> V128 (V128.F32x4 Splat)
  | [ CaseV ("X", [ CaseV ("F64", []); NumV z ]) ] when z = two -> V128 (V128.F64x2 Splat)
  | vs -> error_values "vsplatop" vs

let al_to_vextractop : value list -> vextractop = function
  | [ CaseV ("X", [ CaseV ("I8", []); NumV z ]); OptV (Some sx); n ] when z = sixteen ->
    V128 (V128.I8x16 (Extract (al_to_nat8 n, al_to_sx sx)))
  | [ CaseV ("X", [ CaseV ("I16", []); NumV z ]); OptV (Some sx); n ] when z = eight ->
    V128 (V128.I16x8 (Extract (al_to_nat8 n, al_to_sx sx)))
  | [ CaseV ("X", [ CaseV ("I32", []); NumV z ]); OptV None; n ] when z = four ->
    V128 (V128.I32x4 (Extract (al_to_nat8 n, ())))
  | [ CaseV ("X", [ CaseV ("I64", []); NumV z ]); OptV None; n ] when z = two ->
    V128 (V128.I64x2 (Extract (al_to_nat8 n, ())))
  | [ CaseV ("X", [ CaseV ("F32", []); NumV z ]); OptV None; n ] when z = four ->
    V128 (V128.F32x4 (Extract (al_to_nat8 n, ())))
  | [ CaseV ("X", [ CaseV ("F64", []); NumV z ]); OptV None; n ] when z = two ->
    V128 (V128.F64x2 (Extract (al_to_nat8 n, ())))
  | vs -> error_values "vextractop" vs

let al_to_vreplaceop : value list -> vreplaceop = function
  | [ CaseV ("X", [ CaseV ("I8", []); NumV z ]); n ] when z = sixteen -> V128 (V128.I8x16 (Replace (al_to_nat8 n)))
  | [ CaseV ("X", [ CaseV ("I16", []); NumV z ]); n ] when z = eight -> V128 (V128.I16x8 (Replace (al_to_nat8 n)))
  | [ CaseV ("X", [ CaseV ("I32", []); NumV z ]); n ] when z = four -> V128 (V128.I32x4 (Replace (al_to_nat8 n)))
  | [ CaseV ("X", [ CaseV ("I64", []); NumV z ]); n ] when z = two -> V128 (V128.I64x2 (Replace (al_to_nat8 n)))
  | [ CaseV ("X", [ CaseV ("F32", []); NumV z ]); n ] when z = four -> V128 (V128.F32x4 (Replace (al_to_nat8 n)))
  | [ CaseV ("X", [ CaseV ("F64", []); NumV z ]); n ] when z = two -> V128 (V128.F64x2 (Replace (al_to_nat8 n)))
  | vs -> error_values "vreplaceop" vs
*)

let il_to_packsize exp : RI.Pack.packsize =
  match exp.it with
  | NumE z when z = eight     -> RI.Pack.Pack8
  | NumE z when z = sixteen   -> RI.Pack.Pack16
  | NumE z when z = thirtytwo -> RI.Pack.Pack32
  | NumE z when z = sixtyfour -> RI.Pack.Pack64
  | _ -> error_value "packsize" exp

let il_to_memop (f: exp -> 'p) exps : RI.Ast.idx * (RI.Types.numtype, 'p) RI.Ast.memop =
  match exps with
  | [nt; p; idx; str] ->
    il_to_idx idx,
    {
      ty = il_to_numtype nt;
      align  = find_str_field "ALIGN"  str |> unwrap_case |> il_to_nat |> Z.to_int;
      offset = find_str_field "OFFSET" str |> il_to_uN_64;
      pack = f p;
    }
  | _ -> error_values "memop" exps


let il_to_packsize_sx exp : RI.Pack.packsize * RI.Pack.sx =
  match match_caseE "packsize sx" exp with
  | [[];["_"];[]], [sz; sx] -> il_to_packsize sz, il_to_sx sx
  | _ -> error_value "packsize sx" exp

let il_to_loadop  : exp list -> RI.Ast.idx * RI.Ast.loadop  = il_to_opt il_to_packsize_sx |> il_to_memop

let il_to_storeop : exp list -> RI.Ast.idx * RI.Ast.storeop = il_to_opt il_to_packsize    |> il_to_memop


(*
let al_to_vmemop' (f: value -> 'p): value list -> (vectype, 'p) memop = function
  | [ StrV str ] ->
    {
      ty = V128T;
      align = Record.find "ALIGN" str |> al_to_nat;
      offset = Record.find "OFFSET" str |> al_to_nat64;
      pack = f (natV Z.zero);
    }
  | [ p; StrV str ] ->
    {
      ty = V128T;
      align = Record.find "ALIGN" str |> al_to_nat;
      offset = Record.find "OFFSET" str |> al_to_nat64;
      pack = f p;
    }
  | v -> error_values "vmemop" v

let al_to_vmemop (f: value -> 'p) (g: value list -> value * (value list)): value list -> idx * (vectype, 'p) memop = function
  | vl when !version <= 2 ->
    0l @@ no_region, al_to_vmemop' f vl
  | vl ->
    let idx, vl' = g vl in
    al_to_idx idx, al_to_vmemop' f vl'

let al_to_packshape = function
  | [NumV z1; NumV z2] when z1 = eight && z2 = eight -> Pack.Pack8x8
  | [NumV z1; NumV z2] when z1 = sixteen && z2 = four -> Pack.Pack16x4
  | [NumV z1; NumV z2] when z1 = thirtytwo && z2 = two -> Pack.Pack32x2
  | vs -> error_value "packshape" (TupV vs)

let al_to_vloadop': value -> Pack.packsize * Pack.vext = function
  | CaseV ("SHAPE", [ v1; v2; ext ] ) ->
    let packshape = al_to_packshape [v1; v2] in
    (
      Pack.Pack64,
      Pack.ExtLane (packshape, al_to_sx ext)
    )
  | CaseV ("SPLAT", [ packsize ]) -> al_to_packsize packsize, Pack.ExtSplat
  | CaseV ("ZERO", [ packsize ]) -> al_to_packsize packsize, Pack.ExtZero
  | v -> error_value "vloadop'" v

let al_to_vloadop: value list -> idx * vloadop = function
  | CaseV ("V128", []) :: vl ->
    let split vl =
      match vl with
      | memop :: idx :: vl' -> idx, memop :: vl'
      | _ -> error_values "vloadop" vl
    in
    al_to_vmemop (al_to_opt al_to_vloadop') split vl
  | vs -> error_value "vloadop" (TupV vs)

let al_to_vstoreop = function
  | CaseV ("V128", []) :: vl ->
    let split = Util.Lib.List.split_hd in
    al_to_vmemop (fun _ -> ()) split vl
  | vs -> error_value "vstoreop" (TupV vs)

let al_to_vlaneop: value list -> idx * vlaneop * I8.t = function
  | CaseV ("V128", []) :: vl ->
    let h, t = Util.Lib.List.split_last vl in
    let split vl =
      match vl with
      | ps :: idx :: vl' -> idx, ps :: vl'
      | _ -> error_values "vlaneop" vl
    in
    let idx, op = al_to_vmemop al_to_packsize split h in
    idx, op, al_to_nat8 t
  | vs -> error_value "vlaneop" (TupV vs)
*)

(* Destruct expressions *)

let il_to_catch' exp : RI.Ast.catch' =
  match match_caseE "catch" exp with
  | [["CATCH"];[];[]]     , [idx1; idx2] -> Catch       (il_to_idx idx1, il_to_idx idx2)
  | [["CATCH_REF"];[];[]] , [idx1; idx2] -> CatchRef    (il_to_idx idx1, il_to_idx idx2)
  | [["CATCH_ALL"];[]]    , [idx]        -> CatchAll    (il_to_idx idx)
  | [["CATCH_ALL_REF"];[]], [idx]        -> CatchAllRef (il_to_idx idx)
  | _ -> error_value "catch" exp
let il_to_catch exp : RI.Ast.catch = il_to_phrase il_to_catch' exp

let il_to_num exp : RI.Value.num =
  match match_caseE "num" exp with
  | [["CONST"];[];[]], [numtype; num_] ->
    (match match_caseE "numtype" numtype with
    | [["I32"]], [] -> I32 (il_to_uN_32   num_)
    | [["I64"]], [] -> I64 (il_to_uN_64   num_)
    | [["F32"]], [] -> F32 (il_to_float32 num_)
    | [["F64"]], [] -> F64 (il_to_float64 num_)
    | v -> error_value "numtype" numtype
    )
  | _ -> error_value "num" exp

let il_to_vec exp : RI.Value.vec =
  let _, [vectype; vec_] = match_caseE "vec" exp in
  match match_caseE "vectype" vectype with
  | [["V128"]], [] -> V128 (il_to_vec128 (unwrap_case vec_))
  | _ -> error_value "vectype" vectype


let rec il_to_instr exp : RI.Ast.instr = il_to_phrase il_to_instr' exp
and il_to_instr' exp : RI.Ast.instr' =
  match match_caseE "instr" exp with
  (* wasm values *)
  | [["CONST"];[];[]], _ -> Const (il_to_phrase il_to_num exp)
  | [["VCONST"];[];[]], _ -> VecConst (il_to_phrase il_to_vec exp)
  | [["REF.NULL"];[]], [ht] -> RefNull (il_to_heaptype ht)
  (* wasm instructions *)
  | [["UNREACHABLE"]], [] -> Unreachable
  | [["NOP"]], [] -> Nop
  | [["DROP"]], [] -> Drop
  | [["UNOP"];[];[]], op -> Unary (il_to_unop op)
  | [["BINOP"];[];[]], op -> Binary (il_to_binop op)
  | [["TESTOP"];[];[]], op -> Test (il_to_testop op)
  | [["RELOP"];[];[]], op -> Compare (il_to_relop op)
  | [["CVTOP"];[];[];[]], op -> Convert (il_to_cvtop op)
  (*
  | [["VTESTOP"];[];[]], vop -> VecTest (il_to_vtestop vop)
  | [["VRELOP"];[];[]], vop -> VecCompare (il_to_vrelop vop)
  | [["VUNOP"];[];[]], vop -> VecUnary (il_to_vunop vop)
  | [["VBINOP"];[];[]], vop -> VecBinary (il_to_vbinop vop)
  | [["VTERNOP"];[];[]], vop -> VecTernary (il_to_vternop vop)
  | [[("VSWIZZLOP" | "VSHUFFLE")];[];[]], _ -> VecBinary (il_to_special_vbinop exp)
  | [[("VNARROW" | "VEXTBINOP")];[];[];[]], _ -> VecBinary (il_to_special_vbinop exp)
  | [["VEXTTERNOP"];[];[];[]], _ -> VecTernary (il_to_special_vternop exp)
  | [["VCVTOP"];[];[];[]], vop -> VecConvert (il_to_vcvtop vop)
  | [["VEXTUNOP"];[];[];[]], vop -> VecConvert (il_to_special_vcvtop vop)
  | [["VSHIFTOP"];[];[]], vop -> VecShift (il_to_vshiftop vop)
  | [["VBITMASK"];[]], vop -> VecBitmask (il_to_vbitmaskop vop)
  | [["VVTESTOP"];[];[]], vop -> VecTestBits (il_to_vvtestop vop)
  | [["VVUNOP"];[];[]], vop -> VecUnaryBits (il_to_vvunop vop)
  | [["VVBINOP"];[];[]], vop -> VecBinaryBits (il_to_vvbinop vop)
  | [["VVTERNOP"];[];[]], vop -> VecTernaryBits (il_to_vvternop vop)
  | [["VSPLAT"];[]], vop -> VecSplat (il_to_vsplatop vop)
  | [["VEXTRACT_LANE"];[];[];[]], vop -> VecExtract (il_to_vextractop vop)
  | [["VREPLACE_LANE"];[];[]], vop -> VecReplace (il_to_vreplaceop vop)
  *)
  | [["REF.IS_NULL"]], [] -> RefIsNull
  | [["REF.FUNC"];[]], [idx] -> RefFunc (il_to_idx idx)
  | [["SELECT"];[]], [vtl_opt] -> Select (il_to_opt (il_to_list il_to_valtype) vtl_opt)
  | [["LOCAL.GET"];[]], [idx] -> LocalGet (il_to_idx idx)
  | [["LOCAL.SET"];[]], [idx] -> LocalSet (il_to_idx idx)
  | [["LOCAL.TEE"];[]], [idx] -> LocalTee (il_to_idx idx)
  | [["GLOBAL.GET"];[]], [idx] -> GlobalGet (il_to_idx idx)
  | [["GLOBAL.SET"];[]], [idx] -> GlobalSet (il_to_idx idx)
  | [["TABLE.GET"];[]], [idx] -> TableGet (il_to_idx idx)
  | [["TABLE.SET"];[]], [idx] -> TableSet (il_to_idx idx)
  | [["TABLE.SIZE"];[]], [idx] -> TableSize (il_to_idx idx)
  | [["TABLE.GROW"];[]], [idx] -> TableGrow (il_to_idx idx)
  | [["TABLE.FILL"];[]], [idx] -> TableFill (il_to_idx idx)
  | [["TABLE.COPY"];[];[]], [idx1; idx2] -> TableCopy (il_to_idx idx1, il_to_idx idx2)
  | [["TABLE.INIT"];[];[]], [idx1; idx2] -> TableInit (il_to_idx idx1, il_to_idx idx2)
  | [["ELEM.DROP"];[]], [idx] -> ElemDrop (il_to_idx idx)
  | [["BLOCK"];[];[]], [bt; instrs] ->
    Block (il_to_blocktype bt, il_to_list il_to_instr instrs)
  | [["LOOP"];[];[]], [bt; instrs] ->
    Loop (il_to_blocktype bt, il_to_list il_to_instr instrs)
  | [["IF"];[];["ELSE"];[]], [bt; instrs1; instrs2] ->
    If (il_to_blocktype bt, il_to_list il_to_instr instrs1, il_to_list il_to_instr instrs2)
  | [["BR"];[]], [idx] -> Br (il_to_idx idx)
  | [["BR_IF"];[]], [idx] -> BrIf (il_to_idx idx)
  | [["BR_TABLE"];[];[]], [idxs; idx] -> BrTable (il_to_list il_to_idx idxs, il_to_idx idx)
  | [["BR_ON_NULL"];[]], [idx] -> BrOnNull (il_to_idx idx)
  | [["BR_ON_NON_NULL"];[]], [idx] -> BrOnNonNull (il_to_idx idx)
  | [["BR_ON_CAST"];[];[];[]], [idx; rt1; rt2] -> BrOnCast (il_to_idx idx, il_to_reftype rt1, il_to_reftype rt2)
  | [["BR_ON_CAST_FAIL"];[];[];[]], [idx; rt1; rt2] -> BrOnCastFail (il_to_idx idx, il_to_reftype rt1, il_to_reftype rt2)
  | [["RETURN"]], [] -> Return
  | [["CALL"];[]], [idx] -> Call (il_to_idx idx)
  | [["CALL_REF"];[]], [typeuse] -> CallRef (il_to_idx_of_typeuse typeuse)
  | [["CALL_INDIRECT"];[];[]], [idx1; typeuse2] -> CallIndirect (il_to_idx idx1, il_to_idx_of_typeuse typeuse2)
  | [["RETURN_CALL"];[]], [idx] -> ReturnCall (il_to_idx idx)
  | [["RETURN_CALL_REF"];[]], [typeuse] -> ReturnCallRef (il_to_idx_of_typeuse typeuse)
  | [["RETURN_CALL_INDIRECT"];[];[]], [idx1; typeuse2] -> ReturnCallIndirect (il_to_idx idx1, il_to_idx_of_typeuse typeuse2)
  | [["THROW"];[]], [idx] -> Throw (il_to_idx idx)
  | [["THROW_REF"]], [] -> ThrowRef
  | [["TRY_TABLE"];[];[];[]], [bt; catches; instrs] ->
    TryTable (il_to_blocktype bt, il_to_list' il_to_catch catches, il_to_list il_to_instr instrs)
  | [["LOAD"];[];[];[];[]], loadop -> let idx, op = il_to_loadop loadop in Load (idx, op)
  | [["STORE"];[];[];[];[]], storeop -> let idx, op = il_to_storeop storeop in Store (idx, op)
  (*
  | [["VLOAD"];[];[];[];[]], vloadop -> let idx, op = il_to_vloadop vloadop in VecLoad (idx, op)
  | [["VLOAD_LANE"];[];[];[];[];[]], vlaneop ->
    let idx, op, i = il_to_vlaneop vlaneop in VecLoadLane (idx, op, i)
  | [["VSTORE"];[];[];[]], vstoreop -> let idx, op = il_to_vstoreop vstoreop in VecStore (idx, op)
  | [["VSTORE_LANE"];[];[];[];[];[]], vlaneop ->
    let idx, op, i = il_to_vlaneop vlaneop in VecStoreLane (idx, op, i)
  *)
  | [["MEMORY.SIZE"];[]], [idx] -> MemorySize (il_to_idx idx)
  | [["MEMORY.GROW"];[]], [idx] -> MemoryGrow (il_to_idx idx)
  | [["MEMORY.FILL"];[]], [idx] -> MemoryFill (il_to_idx idx)
  | [["MEMORY.COPY"];[];[]], [idx1; idx2] -> MemoryCopy (il_to_idx idx1, il_to_idx idx2)
  | [["MEMORY.INIT"];[];[]], [idx1; idx2] -> MemoryInit (il_to_idx idx1, il_to_idx idx2)
  | [["DATA.DROP"];[]], [idx] -> DataDrop (il_to_idx idx)
  | [["REF.AS_NON_NULL"]], [] -> RefAsNonNull
  | [["REF.TEST"];[]], [rt] -> RefTest (il_to_reftype rt)
  | [["REF.CAST"];[]], [rt] -> RefCast (il_to_reftype rt)
  | [["REF.EQ"]], [] -> RefEq
  | [["REF.I31"]], [] -> RefI31
  | [["I31.GET"];[]], [sx] -> I31Get (il_to_sx sx)
  | [["STRUCT.NEW"];[]], [idx] -> StructNew (il_to_idx idx, Explicit)
  | [["STRUCT.NEW_DEFAULT"];[]], [idx] -> StructNew (il_to_idx idx, Implicit)
  | [["STRUCT.GET"];[];[];[]], [sx_opt; idx1; idx2] ->
    StructGet (il_to_idx idx1, il_to_uN_32 idx2, il_to_opt il_to_sx sx_opt)
  | [["STRUCT.SET"];[];[]], [idx1; idx2] -> StructSet (il_to_idx idx1, il_to_uN_32 idx2)
  | [["ARRAY.NEW"];[]], [idx] -> ArrayNew (il_to_idx idx, Explicit)
  | [["ARRAY.NEW_DEFAULT"];[]], [idx] -> ArrayNew (il_to_idx idx, Implicit)
  | [["ARRAY.NEW_FIXED"];[];[]], [idx; i32] -> ArrayNewFixed (il_to_idx idx, il_to_uN_32 i32)
  | [["ARRAY.NEW_ELEM"];[];[]], [idx1; idx2] -> ArrayNewElem (il_to_idx idx1, il_to_idx idx2)
  | [["ARRAY.NEW_DATA"];[];[]], [idx1; idx2] -> ArrayNewData (il_to_idx idx1, il_to_idx idx2)
  | [["ARRAY.GET"];[];[]], [sx_opt; idx] -> ArrayGet (il_to_idx idx, il_to_opt il_to_sx sx_opt)
  | [["ARRAY.SET"];[]], [idx] -> ArraySet (il_to_idx idx)
  | [["ARRAY.LEN"]], [] -> ArrayLen
  | [["ARRAY.COPY"];[];[]], [idx1; idx2] -> ArrayCopy (il_to_idx idx1, il_to_idx idx2)
  | [["ARRAY.FILL"];[]], [idx] -> ArrayFill (il_to_idx idx)
  | [["ARRAY.INIT_DATA"];[];[]], [idx1; idx2] -> ArrayInitData (il_to_idx idx1, il_to_idx idx2)
  | [["ARRAY.INIT_ELEM"];[];[]], [idx1; idx2] -> ArrayInitElem (il_to_idx idx1, il_to_idx idx2)
  | [["ANY.CONVERT_EXTERN"]], [] -> ExternConvert Internalize
  | [["EXTERN.CONVERT_ANY"]], [] -> ExternConvert Externalize
  | _ -> error_value "instruction" exp

let il_to_const : exp -> RI.Ast.const = il_to_list il_to_instr |> il_to_phrase


(* Deconstruct module *)

let il_to_type exp : RI.Ast.type_ =
  match match_caseE "type" exp with
  | [["TYPE"];[]], [rt] -> il_to_phrase il_to_rectype rt
  | _ -> error_value "type" exp

let il_to_local' exp : RI.Ast.local' =
  match match_caseE "local" exp with
  | [["LOCAL"];[]], [vt] -> Local (il_to_valtype vt)
  | _ -> error_value "local" exp
let il_to_local exp : RI.Ast.local = il_to_phrase il_to_local' exp

let il_to_func' exp : RI.Ast.func' =
  match match_caseE "func" exp with
  | [["FUNC"];[];[];[]], [idx; locals; instrs] ->
    Func (il_to_idx idx, il_to_list il_to_local locals, il_to_list il_to_instr instrs)
  | _ -> error_value "func" exp
let il_to_func exp : RI.Ast.func = il_to_phrase il_to_func' exp

let il_to_global' exp : RI.Ast.global' =
  match match_caseE "global" exp with
  | [["GLOBAL"];[];[]], [gt; const] ->
    Global (il_to_globaltype gt, il_to_const const)
  | _ -> error_value "global" exp
let il_to_global : exp -> RI.Ast.global = il_to_phrase il_to_global'

let il_to_table' exp : RI.Ast.table' =
  match match_caseE "table" exp with
  | [["TABLE"];[];[]], [tt; const] ->
    Table (il_to_tabletype tt, il_to_const const)
  | _ -> error_value "table" exp
let il_to_table : exp -> RI.Ast.table = il_to_phrase il_to_table'

let il_to_memory' exp : RI.Ast.memory' =
  match match_caseE "memory" exp with
  | [["MEMORY"];[]], [mt] -> Memory (il_to_memorytype mt)
  | _ -> error_value "memory" exp
let il_to_memory : exp -> RI.Ast.memory = il_to_phrase il_to_memory'

let il_to_tag' exp : RI.Ast.tag' =
  match match_caseE "tag" exp with
  | [["TAG"];[]], [tt] -> Tag (il_to_tagtype tt)
  | _ -> error_value "tag" exp
let il_to_tag : exp -> RI.Ast.tag = il_to_phrase il_to_tag'

let il_to_segmentmode' exp : RI.Ast.segmentmode' =
  match match_caseE "segmentmode" exp with
  | [["PASSIVE"]], [] -> Passive
  | [["ACTIVE"];[];[]], [idx; const] -> Active (il_to_idx idx, il_to_const const)
  | [["DECLARE"]], [] -> Declarative
  | _ -> error_value "segmentmode" exp
let il_to_segmentmode : exp -> RI.Ast.segmentmode = il_to_phrase il_to_segmentmode'

let il_to_elem' exp : RI.Ast.elem' =
  match match_caseE "elem" exp with
  | [["ELEM"];[];[];[]], [rt; consts; mode] ->
    Elem (il_to_reftype rt, il_to_list il_to_const consts, il_to_segmentmode mode)
  | _ -> error_value "elem" exp
let il_to_elem : exp -> RI.Ast.elem = il_to_phrase il_to_elem'

let il_to_data' exp : RI.Ast.data' =
  match match_caseE "data" exp with
  | [["DATA"];[];[]], [bytes; mode] ->
    Data (il_to_bytes bytes, il_to_segmentmode mode)
  | _ -> error_value "data" exp
let il_to_data : exp -> RI.Ast.data = il_to_phrase il_to_data'

let il_to_externtype exp : RI.Types.externtype =
  match match_caseE "externtype" exp with
  | [["FUNC"]  ;[]], [typeuse]    -> ExternFuncT   (il_to_typeuse    typeuse   )
  | [["GLOBAL"];[]], [globaltype] -> ExternGlobalT (il_to_globaltype globaltype)
  | [["TABLE"] ;[]], [tabletype]  -> ExternTableT  (il_to_tabletype  tabletype )
  | [["MEM"]   ;[]], [memtype]    -> ExternMemoryT (il_to_memorytype memtype   )
  | [["TAG"]   ;[]], [tagtype]    -> ExternTagT    (il_to_tagtype    tagtype   )
  | _ -> error_value "externtype" exp

let il_to_import' exp : RI.Ast.import' =
  match match_caseE "import" exp with
  | [["IMPORT"];[];[];[]], [module_name; item_name; xt] ->
    RI.Ast.Import (il_to_name module_name, il_to_name item_name, il_to_externtype xt)
  | _ -> error_value "import" exp
let il_to_import : exp -> RI.Ast.import = il_to_phrase il_to_import'

let il_to_externidx' exp : RI.Ast.externidx' =
  match match_caseE "externidx" exp with
  | [["FUNC"]  ;[]], [idx] -> FuncX   (il_to_idx idx)
  | [["TABLE"] ;[]], [idx] -> TableX  (il_to_idx idx)
  | [["MEM"]   ;[]], [idx] -> MemoryX (il_to_idx idx)
  | [["GLOBAL"];[]], [idx] -> GlobalX (il_to_idx idx)
  | [["TAG"]   ;[]], [idx] -> TagX    (il_to_idx idx)
  | _ -> error_value "externidx" exp
let il_to_externidx : exp -> RI.Ast.externidx = il_to_phrase il_to_externidx'

let il_to_start' exp : RI.Ast.start' =
  match match_caseE "start" exp with
  | [["START"];[]], [idx] -> Start (il_to_idx idx)
  | _ -> error_value "start" exp
let il_to_start : exp -> RI.Ast.start = il_to_phrase il_to_start'

let il_to_export' exp : RI.Ast.export' =
  match match_caseE "export" exp with
  | [["EXPORT"];[];[]], [name; xx] -> Export (il_to_name name, il_to_externidx xx)
  | _ -> error_value "export" exp
let il_to_export : exp -> RI.Ast.export = il_to_phrase il_to_export'

let il_to_module' exp : RI.Ast.module_' =
  match match_caseE "module" exp with
  | [["MODULE"];[];[];[];[];[];[];[];[];[];[];[]], [
      types; imports; tags; globals; memories; tables; funcs; datas; elems; start; exports
    ] ->
    {
      types    = il_to_list il_to_type   types   ;
      imports  = il_to_list il_to_import imports ;
      tags     = il_to_list il_to_tag    tags    ;
      globals  = il_to_list il_to_global globals ;
      memories = il_to_list il_to_memory memories;
      tables   = il_to_list il_to_table  tables  ;
      funcs    = il_to_list il_to_func   funcs   ;
      datas    = il_to_list il_to_data   datas   ;
      elems    = il_to_list il_to_elem   elems   ;
      start    = il_to_opt  il_to_start  start   ;
      exports  = il_to_list il_to_export exports ;
    }
  | _ -> error_value "module" exp
let il_to_module : exp -> RI.Ast.module_ = il_to_phrase il_to_module'


(* Destruct value *)

let rec il_to_field exp : RI.Aggr.field =
  match match_caseE "field" exp with
  | [["PACK"];[];[]], [pt; c] -> RI.Aggr.PackField (il_to_packtype pt, ref (il_to_nat c |> Z.to_int))
  | _ -> RI.Aggr.ValField (ref (il_to_value exp))

and il_to_array exp : RI.Aggr.array =
  if has_str_field "TYPE" exp && has_str_field "FIELDS" exp then
    RI.Aggr.Array (
      il_to_deftype (find_str_field "TYPE" exp),
      il_to_list il_to_field (find_str_field "FIELDS" exp)
    )
  else
    error_value "array" exp

and il_to_struct exp : RI.Aggr.struct_ =
  if has_str_field "TYPE" exp && has_str_field "FIELDS" exp then
    RI.Aggr.Struct (
      il_to_deftype (find_str_field "TYPE" exp),
      il_to_list il_to_field (find_str_field "FIELDS" exp)
    )
  else
    error_value "struct" exp

(*
and al_to_tag: value -> Tag.t = function
  | StrV r when Record.mem "TYPE" r ->
    Tag.alloc (al_to_tagtype (Record.find "TYPE" r))
  | v -> error_value "tag" v

and al_to_exn: value -> Exn.exn_ = function
  | StrV r when Record.mem "TAG" r && Record.mem "FIELDS" r ->
    let tag_insts = Ds.Store.access "TAGS" in
    let tag = Record.find "TAG" r |> al_to_nat |> listv_nth tag_insts |> al_to_tag in
    Exn.Exn (
      tag,
      al_to_list al_to_value (Record.find "FIELDS" r)
    )
  | v -> error_value "exn" v
*)

and il_to_funcinst exp : RI.Instance.funcinst =
  if has_str_field "TYPE" exp && has_str_field "MODULE" exp && has_str_field "CODE" exp then
    RI.Func.AstFunc (
      il_to_deftype (find_str_field "TYPE" exp),
      Reference_interpreter.Lib.Promise.make (), (* TODO: Fulfill the promise with module instance *)
      il_to_func (find_str_field "CODE" exp)
    )
  else
    error_value "funcinst" exp

and il_to_ref exp : RI.Value.ref_ =
  let open RI in
  let open Value in
  match match_caseE "ref" exp with
  | [["REF.NULL"];[]], [ht] -> NullRef (il_to_heaptype ht)
  | [["REF.I31_NUM"];[]], [i] -> RI.I31.I31Ref (il_to_nat i |> Z.to_int)
  | [["REF.STRUCT_ADDR"];[]], [addr] ->
    let struct_insts = State.Store.access "STRUCTS" in
    let struct_ = addr |> il_to_nat |> nth_of_list struct_insts |> il_to_struct in
    Aggr.StructRef struct_
  | [["REF.ARRAY_ADDR"];[]], [addr] ->
    let arr_insts = State.Store.access "ARRAYS" in
    let arr = addr |> il_to_nat |> nth_of_list arr_insts |> il_to_array in
    Aggr.ArrayRef arr
  | [["REF.FUNC_ADDR"];[]], [addr] ->
    let func_insts = State.Store.access "FUNCS" in
    let func = addr |> il_to_nat |> nth_of_list func_insts |> il_to_funcinst in
    Instance.FuncRef func
  | [["REF.HOST_ADDR"];[]], [i32] -> RI.Script.HostRef (il_to_nat32 i32)
  | [["REF.EXTERN"];[]], [r] -> Extern.ExternRef (il_to_ref r)
  | _ ->  error_value "ref" exp

and il_to_value exp : RI.Value.value =
  match match_caseE "val" exp with
  | [["CONST" ];[];[]], _ -> RI.Value.Num (il_to_num exp)
  | [["VCONST"];[];[]], _ -> RI.Value.Vec (il_to_vec exp)
  | [[ref_con];[]], _ when String.starts_with ~prefix:"REF." ref_con ->
    RI.Value.Ref (il_to_ref exp)
  | _ -> error_value "val" exp
