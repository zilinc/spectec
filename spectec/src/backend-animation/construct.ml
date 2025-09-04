open Il.Ast
open Util
open Error
open Source
open Il_util
module RI = Reference_interpreter
module RT = RI.Types
module BI = Backend_interpreter


let error at msg = Util.Error.error at "ani.../int.../construct" msg


(* Constant *)

let default_table_max = 4294967295L
let default_memory_max = 65536L

(* Currently support only version 3. *)
let version = ref 3



(* Construct minor *)

let il_of_z_nat z : exp = natE z
let il_of_z_int z : exp = intE z


let il_of_fmagN layout i : exp =
  let n = Z.logand i (BI.Construct.mask_exp layout) in
  let m = Z.logand i (BI.Construct.mask_mant layout) in
  let t = VarT ("fNmag" $ no, [ExpA (varE ~note:(t_var "N") "N") $ no]) $ no in
  if n = Z.zero then
    mk_case t [["SUBNORM"];[]] [ il_of_z_nat m ]
  else if n <> BI.Construct.mask_exp layout then
    mk_case t [["NORM"];[]] [ il_of_z_nat m; il_of_z_int Z.(shift_right n layout.mantissa - BI.Construct.bias layout) ]
  else if m = Z.zero then
    mk_case t [["INF"];[]] []
  else
    mk_case t [["NAN"];[]] [ il_of_z_nat m ]

let il_of_floatN layout i =
  let t = VarT ("fN" $ no, [ExpA (varE ~note:(t_var "N") "N") $ no]) $ no in
  let i' = Z.logand i (BI.Construct.mask_mag layout) in
  let mag = il_of_fmagN layout i in
  mk_case t [[if i' = i then "POS" else "NEG"];[]] [ mag ]


let il_of_nat i = Z.of_int i |> il_of_z_nat
let il_of_nat8  i8  = Z.of_int (RI.I8.to_int_u  i8 ) |> il_of_z_nat
let il_of_nat16 i16 = Z.of_int (RI.I16.to_int_u i16) |> il_of_z_nat
let il_of_nat32 i32 = Z.of_int32_unsigned i32 |> il_of_z_nat
let il_of_nat64 i64 = Z.of_int64_unsigned i64 |> il_of_z_nat

let il_of_idx (idx: RI.Ast.idx) = il_of_nat32 idx.it

let il_of_name name = textE (Utf8.encode name)
let il_of_byte byte = Char.code byte |> il_of_nat
let il_of_bytes bytes = String.to_seq bytes |> il_of_seq il_of_byte (t_star "byte")
let il_of_float32 f32 = RI.F32.to_bits f32 |> Z.of_int32_unsigned |> il_of_floatN BI.Construct.layout32
let il_of_float64 f64 = RI.F64.to_bits f64 |> Z.of_int64_unsigned |> il_of_floatN BI.Construct.layout64
let il_of_vec128 vec = BI.Construct.vec128_to_z vec |> il_of_z_nat
let il_of_memidx idx = il_of_idx idx

(*
let al_of_bool b = Stdlib.Bool.to_int b |> al_of_nat
*)






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
  | RT.FieldT (mut, st) -> mk_case' "fieldtype" [[];[];[]] [ il_of_mut mut; il_of_storagetype st ]

and il_of_resulttype rt = il_of_list (t_star "valtype") il_of_valtype rt

and il_of_comptype = function
  | RT.StructT ftl      -> mk_case' "comptype" [["STRUCT"];[]]      [ il_of_list (t_list "fieldtype") il_of_fieldtype ftl ]
  | RT.ArrayT  ft       -> mk_case' "comptype" [["ARRAY"];[]]       [ il_of_fieldtype ft ]
  | RT.FuncT (rt1, rt2) -> mk_case' "comptype" [["FUNC"];["->"];[]] [ il_of_resulttype rt1; il_of_resulttype rt2 ]

and il_of_subtype = function
  | RT.SubT (fin, tul, st) ->
    mk_case' "subtype" [["SUB"];[];[];[]] [ il_of_final fin; il_of_list (t_star "typeuse") il_of_typeuse tul; il_of_comptype st ]

and il_of_rectype = function
  | RT.RecT stl -> mk_case' "rectype" [["REC"];[]] [ il_of_list (t_list "subtype") il_of_subtype stl ]

and il_of_deftype = function
  | RT.DefT (rt, i) -> mk_case' "deftype" [["_DEF"];[];[]] [il_of_rectype rt; il_of_nat32 i]

and il_of_typeuse = function
  | RT.Idx idx -> mk_case' "typeuse" [["_IDX"];[]] [ il_of_nat32 idx ]
  | RT.Rec n   -> mk_case' "typeuse" [["REC" ];[]] [ il_of_nat32 n ]
  | RT.Def dt  -> il_of_deftype dt

and il_of_typeuse_of_idx idx = mk_case' "typeuse" [["_IDX"];[]] [ il_of_idx idx ]

and il_of_heaptype = function
  | RT.UseHT tu -> il_of_typeuse tu
  | RT.BotHT    -> mk_nullary' "absheaptype" "BOT"
  | ht -> RT.string_of_heaptype ht |> mk_nullary' "absheaptype"

and il_of_reftype (null, ht) =
  mk_case' "reftype" [["REF"];[];[]] [ il_of_null null; il_of_heaptype ht ]

and il_of_addrtype at = RT.string_of_addrtype at |> mk_nullary' "addrtype"

and il_of_numtype nt = RT.string_of_numtype nt |> mk_nullary' "numtype"

and il_of_vectype vt = RT.string_of_vectype vt |> mk_nullary' "vectype"

and il_of_valtype = function
  | RT.RefT rt -> il_of_reftype rt
  | RT.NumT nt -> il_of_numtype nt
  | RT.VecT vt -> il_of_vectype vt
  | RT.BotT    -> mk_nullary' "valtype" "BOT"

let il_of_blocktype = function
  | RI.Ast.VarBlockType idx    -> mk_case' "blocktype" [["_IDX"   ];[]] [ il_of_idx idx ]
  | RI.Ast.ValBlockType vt_opt -> mk_case' "blocktype" [["_RESULT"];[]] [ il_of_opt (t_opt "valtype") il_of_valtype vt_opt ]

let il_of_limits default (limits: RT.limits) =
  let max =
    match limits.max with
    | Some v -> il_of_nat64 v
    | None   -> il_of_nat64 default
  in
  mk_case' "limits" [["["];[".."];["]"]] [ il_of_nat64 limits.min; max ]

let il_of_tagtype = function
  | RT.TagT tu -> il_of_typeuse tu

let il_of_globaltype = function
  | RT.GlobalT (mut, vt) -> mk_case' "globaltype" [[];[];[]] [ il_of_mut mut; il_of_valtype vt ]

let il_of_tabletype = function
  | RT.TableT (at, limits, rt) ->
    mk_case' "tabletype" [[];[];[];[]] [ il_of_addrtype at; il_of_limits default_table_max limits; il_of_reftype rt ]

let il_of_memorytype = function
  | RT.MemoryT (at, limits) ->
    mk_case' "memtype" [[];[];["PAGE"]] [ il_of_addrtype at; il_of_limits default_memory_max limits ]




(* Construct value *)

let il_of_num value =
  let const_info = Xl.Atom.{def = "instr"; case = "CONST"} in
  match value with
  | RI.Value.I32 i32 -> mk_case' "instr" [["CONST"];[];[]] [ mk_nullary' "numtype" "I32"; il_of_nat32 i32 ]
  | RI.Value.I64 i64 -> mk_case' "instr" [["CONST"];[];[]] [ mk_nullary' "numtype" "I64"; il_of_nat64 i64 ]
  | RI.Value.F32 f32 -> mk_case' "instr" [["CONST"];[];[]] [ mk_nullary' "numtype" "F32"; il_of_float32 f32 ]
  | RI.Value.F64 f64 -> mk_case' "instr" [["CONST"];[];[]] [ mk_nullary' "numtype" "F64"; il_of_float64 f64 ]

let il_of_vec = function
  | RI.Value.V128 v128 -> mk_case' "instr" [["VCONST"];[];[]] [ mk_nullary' "vectype" "V128"; il_of_vec128 v128 ]

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
  | RI.Value.NullRef ht   -> mk_case' "instr" [["REF.NULL"];[]] [ il_of_heaptype ht ]
  | RI.Script.HostRef i32 -> mk_case' "instr" [["REF.HOST_ADDR"];[]] [ il_of_nat32 i32 ]
  | RI.Extern.ExternRef r -> mk_case' "instr" [["REF.EXTERN"];[]] [ il_of_ref r ]
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
  | RI.Value.I32 op -> [ mk_nullary' "numtype" "I32"; f1 op ]
  | RI.Value.I64 op -> [ mk_nullary' "numtype" "I64"; f1 op ]
  | RI.Value.F32 op -> [ mk_nullary' "numtype" "F32"; f2 op ]
  | RI.Value.F64 op -> [ mk_nullary' "numtype" "F64"; f2 op ]



let il_of_unop =
  let open RI in
  let open Ast in
  let il_of_int_unop op =
    let t = t_app "unop_" [expA (subE (varE ~note:(t_var "Inn") "Inn") (t_var "Inn") (t_var "numtype"))] in
    match op with
    | IntOp.Clz    -> mk_nullary t "CLZ"
    | IntOp.Ctz    -> mk_nullary t "CTZ"
    | IntOp.Popcnt -> mk_nullary t "POPCNT"
    | IntOp.ExtendS Pack.Pack8  -> mk_case t [["EXTEND"];[]] [il_of_nat 8 ]
    | IntOp.ExtendS Pack.Pack16 -> mk_case t [["EXTEND"];[]] [il_of_nat 16]
    | IntOp.ExtendS Pack.Pack32 -> mk_case t [["EXTEND"];[]] [il_of_nat 32]
    | IntOp.ExtendS Pack.Pack64 -> mk_case t [["EXTEND"];[]] [il_of_nat 64]
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
    | IntOp.ExtendI32 sx     -> mk_nullary' "numtype" "I32", mk_case tII [["EXTEND"   ];[]] [ il_of_sx sx ]
    | IntOp.WrapI64          -> mk_nullary' "numtype" "I64", mk_nullary tII "WRAP"
    | IntOp.TruncF32 sx      -> mk_nullary' "numtype" "F32", mk_case tIF [["TRUNC"    ];[]] [ il_of_sx sx ]
    | IntOp.TruncF64 sx      -> mk_nullary' "numtype" "F64", mk_case tIF [["TRUNC"    ];[]] [ il_of_sx sx ]
    | IntOp.TruncSatF32 sx   -> mk_nullary' "numtype" "F32", mk_case tIF [["TRUNC_SAT"];[]] [ il_of_sx sx ]
    | IntOp.TruncSatF64 sx   -> mk_nullary' "numtype" "F64", mk_case tIF [["TRUNC_SAT"];[]] [ il_of_sx sx ]
    | IntOp.ReinterpretFloat -> mk_nullary' "numtype" ("F" ^ num_bits), mk_nullary tIF "REINTERPRET"
  in
  let il_of_float_cvtop num_bits cop =
    match cop with
    | FloatOp.ConvertI32 sx  -> mk_nullary' "numtype" "I32", mk_case tFI [["CONVERT"];[]] [ il_of_sx sx ]
    | FloatOp.ConvertI64 sx  -> mk_nullary' "numtype" "I64", mk_case tFI [["CONVERT"];[]] [ il_of_sx sx ]
    | FloatOp.PromoteF32     -> mk_nullary' "numtype" "F32", mk_case tFF [["PROMOTE"]] []
    | FloatOp.DemoteF64      -> mk_nullary' "numtype" "F64", mk_case tFF [["DEMOTE" ]] []
    | FloatOp.ReinterpretInt -> mk_nullary' "numtype" ("I" ^ num_bits), mk_nullary tFI "REINTERPRET"
  in
  match cop with
  | I32 op -> let to_, op' = il_of_int_cvtop "32" op in
              [ mk_nullary t_Inn "I32"; to_; op' ]
  | I64 op -> let to_, op' = il_of_int_cvtop "64" op in
              [ mk_nullary t_Inn "I64"; to_; op' ]
  | F32 op -> let to_, op' = il_of_float_cvtop "32" op in
              [ mk_nullary t_Fnn "F32"; to_; op' ]
  | F64 op -> let to_, op' = il_of_float_cvtop "64" op in
              [ mk_nullary t_Fnn "F64"; to_; op' ]


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
  let str = [("ALIGN" , il_of_nat   memop.align );
             ("OFFSET", il_of_nat64 memop.offset)]
  in
  [ il_of_numtype memop.ty; f memop.pack; il_of_memidx idx; mk_str "memarg" str ]

let il_of_packsize_sx (ps, sx) =
  let t = t_app "loadop_" [expA (subE (varE ~note:(t_var "Inn") "Inn") (t_var "Inn") (t_var "numtype"))] in
  mk_case t [[];["_"];[]] [ il_of_packsize ps; il_of_sx sx ]

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
  | Catch    (idx1, idx2) -> mk_catch "CATCH"         2 [ il_of_idx idx1; il_of_idx idx2 ]
  | CatchRef (idx1, idx2) -> mk_catch "CATCH_REF"     2 [ il_of_idx idx1; il_of_idx idx2 ]
  | CatchAll    idx       -> mk_catch "CATCH_ALL"     1 [ il_of_idx idx ]
  | CatchAllRef idx       -> mk_catch "CATCH_ALL_REF" 1 [ il_of_idx idx ]

let rec il_of_instr (instr: RI.Ast.instr) =
  let mk_instr0 = mk_nullary' "instr'" in
  let mk_instr c n = mk_case' "instr'" ([c] :: List.init 2 (Fun.const [])) in
  match instr.it with
  (* wasm values *)
  | Const num -> il_of_num num.it
  | VecConst vec -> il_of_vec vec.it
  | RefNull ht -> mk_instr "REF.NULL" 1 [ il_of_heaptype ht ]
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
  | RefFunc idx     -> mk_instr "REF.FUNC" 1 [ il_of_idx idx ]
  | Select  vtl_opt -> mk_instr "SELECT"   1 [ il_of_opt (optT (t_star "valtype")) (il_of_list (t_star "valtype") il_of_valtype) vtl_opt ]
  | LocalGet  idx   -> mk_instr "LOCAL.GET"  1 [ il_of_idx idx ]
  | LocalSet  idx   -> mk_instr "LOCAL.SET"  1 [ il_of_idx idx ]
  | LocalTee  idx   -> mk_instr "LOCAL.TEE"  1 [ il_of_idx idx ]
  | GlobalGet idx   -> mk_instr "GLOBAL.GET" 1 [ il_of_idx idx ]
  | GlobalSet idx   -> mk_instr "GLOBAL.SET" 1 [ il_of_idx idx ]
  | TableGet  idx   -> mk_instr "TABLE.GET"  1 [ il_of_idx idx ]
  | TableSet  idx   -> mk_instr "TABLE.SET"  1 [ il_of_idx idx ]
  | TableSize idx   -> mk_instr "TABLE.SIZE" 1 [ il_of_idx idx ]
  | TableGrow idx   -> mk_instr "TABLE.GROW" 1 [ il_of_idx idx ]
  | TableFill idx   -> mk_instr "TABLE.FILL" 1 [ il_of_idx idx ]
  | TableCopy (idx1, idx2) -> mk_instr "TABLE.COPY" 2 [ il_of_idx idx1; il_of_idx idx2 ]
  | TableInit (idx1, idx2) -> mk_instr "TABLE.INIT" 2 [ il_of_idx idx1; il_of_idx idx2 ]
  | ElemDrop idx -> mk_instr "ELEM.DROP" 1 [ il_of_idx idx ]
  | Block (bt, instrs) -> mk_instr "BLOCK" 2 [ il_of_blocktype bt; il_of_list (t_star "instr") il_of_instr instrs ]
  | Loop  (bt, instrs) -> mk_instr "LOOP"  2 [ il_of_blocktype bt; il_of_list (t_star "instr") il_of_instr instrs ]
  | If (bt, instrs1, instrs2) ->
    mk_case (t_var "instr") [["IF"];[];[];["ELSE"];[]] [
      il_of_blocktype bt;
      il_of_list (t_star "instr") il_of_instr instrs1;
      il_of_list (t_star "instr") il_of_instr instrs2;
    ]
  | Br   idx -> mk_instr "BR"    1 [ il_of_idx idx ]
  | BrIf idx -> mk_instr "BR_IF" 1 [ il_of_idx idx ]
  | BrTable (idxs, idx) -> mk_instr "BR_TABLE" 2 [ il_of_list (t_star "labelidx") il_of_idx idxs; il_of_idx idx ]
  | BrOnNull    idx -> mk_instr "BR_ON_NULL"     1 [ il_of_idx idx ]
  | BrOnNonNull idx -> mk_instr "BR_ON_NON_NULL" 1 [ il_of_idx idx ]
  | BrOnCast     (idx, rt1, rt2) -> mk_instr "BR_ON_CAST"      3 [ il_of_idx idx; il_of_reftype rt1; il_of_reftype rt2 ]
  | BrOnCastFail (idx, rt1, rt2) -> mk_instr "BR_ON_CAST_FAIL" 3 [ il_of_idx idx; il_of_reftype rt1; il_of_reftype rt2 ]
  | Return -> mk_instr0 "RETURN"
  | Call    idx -> mk_instr "CALL"     1 [ il_of_idx idx ]
  | CallRef idx -> mk_instr "CALL_REF" 1 [ il_of_typeuse_of_idx idx ]
  | CallIndirect (idx1, idx2) -> mk_instr "CALL_INDIRECT" 2 [ il_of_idx idx1; il_of_typeuse_of_idx idx2 ]
  | ReturnCall    idx -> mk_instr "RETURN_CALL"     1 [ il_of_idx idx ]
  | ReturnCallRef idx -> mk_instr "RETURN_CALL_REF" 1 [ il_of_typeuse_of_idx idx ]
  | ReturnCallIndirect (idx1, idx2) -> mk_instr "RETURN_CALL_INDIRECT" 2 [ il_of_idx idx1; il_of_typeuse_of_idx idx2 ]
  | Throw idx -> mk_instr "THROW" 1 [ il_of_idx idx ]
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
  | MemorySize idx -> mk_instr "MEMORY.SIZE" 1 [ il_of_memidx idx ]
  | MemoryGrow idx -> mk_instr "MEMORY.GROW" 1 [ il_of_memidx idx ]
  | MemoryFill idx -> mk_instr "MEMORY.FILL" 1 [ il_of_memidx idx ]
  | MemoryCopy (idx1, idx2) -> mk_instr "MEMORY.COPY" 2 [ il_of_memidx idx1; il_of_memidx idx2 ]
  | MemoryInit (idx1, idx2) -> mk_instr "MEMORY.INIT" 2 [ il_of_memidx idx1; il_of_idx    idx2 ]
  | DataDrop idx -> mk_instr "DATA.DROP" 1 [ il_of_idx idx ]
  | RefAsNonNull -> mk_instr0 "REF.AS_NON_NULL"
  | RefTest rt -> mk_instr "REF.TEST" 1 [ il_of_reftype rt ]
  | RefCast rt -> mk_instr "REF.CAST" 1 [ il_of_reftype rt ]
  | RefEq  -> mk_instr0 "REF.EQ"
  | RefI31 -> mk_instr0 "REF.I31"
  | I31Get sx -> mk_instr "I31.GET" 1 [ il_of_sx sx ]
  | StructNew (idx, Explicit) -> mk_instr "STRUCT.NEW"         1 [ il_of_idx idx ]
  | StructNew (idx, Implicit) -> mk_instr "STRUCT.NEW_DEFAULT" 1 [ il_of_idx idx ]
  | StructGet (idx1, idx2, sx_opt) ->
    mk_instr "STRUCT.GET" 3 [
      il_of_opt (t_opt "sx") il_of_sx sx_opt;
      il_of_idx idx1;
      il_of_nat32 idx2;
    ]
  | StructSet (idx1, idx2)     -> mk_instr "STRUCT.SET"        2 [ il_of_idx idx1; il_of_nat32 idx2 ]
  | ArrayNew (idx, Explicit)   -> mk_instr "ARRAY.NEW"         1 [ il_of_idx idx ]
  | ArrayNew (idx, Implicit)   -> mk_instr "ARRAY.NEW_DEFAULT" 1 [ il_of_idx idx ]
  | ArrayNewFixed (idx, i32)   -> mk_instr "ARRAY.NEW_FIXED"   2 [ il_of_idx idx ; il_of_nat32 i32 ]
  | ArrayNewElem (idx1, idx2)  -> mk_instr "ARRAY.NEW_ELEM"    2 [ il_of_idx idx1; il_of_idx idx2 ]
  | ArrayNewData (idx1, idx2)  -> mk_instr "ARRAY.NEW_DATA"    2 [ il_of_idx idx1; il_of_idx idx2 ]
  | ArrayGet (idx, sx_opt)     -> mk_instr "ARRAY.GET"         2 [ il_of_opt (t_opt "sx") il_of_sx sx_opt; il_of_idx idx ]
  | ArraySet idx               -> mk_instr "ARRAY.SET"         1 [ il_of_idx idx ]
  | ArrayLen                   -> mk_instr0 "ARRAY.LEN"
  | ArrayCopy (idx1, idx2)     -> mk_instr "ARRAY.COPY"        2 [ il_of_idx idx1; il_of_idx idx2 ]
  | ArrayFill idx              -> mk_instr "ARRAY.FILL"        1 [ il_of_idx idx ]
  | ArrayInitData (idx1, idx2) -> mk_instr "ARRAY.INIT_DATA"   2 [ il_of_idx idx1; il_of_idx idx2 ]
  | ArrayInitElem (idx1, idx2) -> mk_instr "ARRAY.INIT_ELEM"   2 [ il_of_idx idx1; il_of_idx idx2 ]
  | ExternConvert Internalize  -> mk_instr0 "ANY.CONVERT_EXTERN"
  | ExternConvert Externalize  -> mk_instr0 "EXTERN.CONVERT_ANY"
  | _ -> mk_instr0 "TODO: Unconstructed Wasm instruction (il_of_instr)"

let il_of_const (const: RI.Ast.const) = il_of_list (t_star "instr") il_of_instr const.it


(* Construct module *)

let il_of_type (ty: RI.Ast.type_) =
  mk_case' "type" [["TYPE"];[]] [ il_of_rectype ty.it ]

let il_of_local (local: RI.Ast.local) =
  let Local t = local.it in
  mk_case' "local" [["LOCAL"];[]] [ il_of_valtype t ]

let il_of_func (func: RI.Ast.func) =
  let Func (idx, locals, body) = func.it in
  mk_case' "func" [["FUNC"];[];[];[]] [
    il_of_idx idx;
    il_of_list (t_star "local") il_of_local locals;
    il_of_list (t_var "expr") il_of_instr body;
  ]

let il_of_global (global: RI.Ast.global) =
  let Global (gt, expr) = global.it in
  mk_case' "global" [["GLOBAL"];[];[]] [ il_of_globaltype gt; il_of_const expr ]

let il_of_table (table: RI.Ast.table) =
  let Table (tt, expr) = table.it in
  mk_case' "table" [["TABLE"];[];[]] [ il_of_tabletype tt; il_of_const expr ]

let il_of_memory (memory: RI.Ast.memory) =
  let Memory mt = memory.it in
  mk_case' "mem" [["MEMORY"];[]] [ il_of_memorytype mt ]

let il_of_tag (tag: RI.Ast.tag) =
  let Tag tt = tag.it in
  mk_case' "tag" [["TAG"];[]] [ il_of_tagtype tt ]

let il_of_segmentmode (segmentmode: RI.Ast.segmentmode) =
  match segmentmode.it with
  | Passive -> mk_nullary' "datamode" "PASSIVE"
  | Active (index, offset) ->
    mk_case' "datamode" [["ACTIVE"];[];[]] [ il_of_idx index; il_of_const offset ]
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
  mk_case' "import" [["IMPORT"];[];[];[]] [ il_of_name module_name; il_of_name item_name; il_of_externtype xt ]

let il_of_externidx (xt: RI.Ast.externidx) = match xt.it with
  | FuncX   idx -> mk_case' "externidx" [["FUNC"  ];[]] [ il_of_idx idx ]
  | TableX  idx -> mk_case' "externidx" [["TABLE" ];[]] [ il_of_idx idx ]
  | MemoryX idx -> mk_case' "externidx" [["MEM"   ];[]] [ il_of_idx idx ]
  | GlobalX idx -> mk_case' "externidx" [["GLOBAL"];[]] [ il_of_idx idx ]
  | TagX    idx -> mk_case' "externidx" [["TAG"   ];[]] [ il_of_idx idx ]

let il_of_start (start: RI.Ast.start) =
  let Start idx = start.it in
  mk_case' "start" [["START"];[]] [ il_of_idx idx ]

let il_of_export (export: RI.Ast.export) =
  let Export (name, exix) = export.it in
  mk_case' "export" [["EXPORT"];[];[]] [ il_of_name name; il_of_externidx exix ]


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

