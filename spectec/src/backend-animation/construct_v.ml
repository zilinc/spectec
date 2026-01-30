open Value
open Util
open Source
module RI = Reference_interpreter
module RT = RI.Types
module BI = Backend_interpreter
open Xl.Atom


let error at msg = Util.Error.error at "animation/construct_v" msg
let error_value ?(at = no) name val_ = error at ("Invalid " ^ name ^ ": " ^ string_of_value val_)
let error_values ?(at = no) name vals =
  error at ("Invalid " ^ name ^ ": " ^ string_of_values ", " vals)


(* Constant *)

let default_table_max = 4294967295L
let default_memory_max = 65536L

(* Currently support only version 3. *)
let version = ref 3



(* Construct minor *)

let vl_of_z_nat z : value = natV z
let vl_of_z_int z : value = intV z

let vl_of_uN z : value = caseV1 (natV z)
let vl_of_iN z : value = caseV1 (natV z)


let vl_of_fmagN layout i : value =
  let n = Z.logand i (BI.Construct.mask_exp layout) in
  let m = Z.logand i (BI.Construct.mask_mant layout) in
  if n = Z.zero then
    caseV [["SUBNORM"];[]] [vl_of_z_nat m]
  else if n <> BI.Construct.mask_exp layout then
    caseV [["NORM"];[];[]] [vl_of_z_nat m; vl_of_z_int Z.(shift_right n layout.mantissa - BI.Construct.bias layout)]
  else if m = Z.zero then
    caseV [["INF"]] []
  else
    caseV [["NAN"];[]] [vl_of_z_nat m]

let vl_of_floatN layout i =
  let i' = Z.logand i (BI.Construct.mask_mag layout) in
  let mag = vl_of_fmagN layout i in
  caseV [[if i' = i then "POS" else "NEG"];[]] [mag]


let vl_of_nat i = Z.of_int i |> vl_of_z_nat
let vl_of_nat8  i8  = Z.of_int (RI.I8.to_int_u  i8 ) |> vl_of_z_nat
let vl_of_nat16 i16 = Z.of_int (RI.I16.to_int_u i16) |> vl_of_z_nat
let vl_of_nat32 i32 = Z.of_int32_unsigned i32 |> vl_of_z_nat
let vl_of_nat64 i64 = Z.of_int64_unsigned i64 |> vl_of_z_nat

let vl_of_name name = textV (Utf8.encode name) |> caseV1
let vl_of_byte byte = Char.code byte |> vl_of_nat |> caseV1
let vl_of_bytes bytes = String.to_seq bytes |> vl_of_seq vl_of_byte
let vl_of_float32 f32 = RI.F32.to_bits f32 |> Z.of_int32_unsigned |> vl_of_floatN BI.Construct.layout32
let vl_of_float64 f64 = RI.F64.to_bits f64 |> Z.of_int64_unsigned |> vl_of_floatN BI.Construct.layout64
let vl_of_vec128 vec = BI.Construct.vec128_to_z vec |> vl_of_z_nat |> caseV1


let vl_of_uN_32 (n: RI.I32.t) = vl_of_nat32 n |> caseV1
let vl_of_uN_64 (n: RI.I64.t) = vl_of_nat64 n |> caseV1
let vl_of_idx (idx: RI.Ast.idx) = vl_of_uN_32 idx.it
let vl_of_memidx idx = vl_of_idx idx


(* syntax list(syntax X) = X*  -- if ... *)
let vl_of_list' f l = vl_of_list f l |> caseV1


let rec vl_of_null = function
  | RT.NoNull -> none
  | RT.Null   -> some (nullary "NULL")

and vl_of_final = function
  | RT.NoFinal -> none
  | RT.Final   -> some (nullary "FINAL")

and vl_of_mut = function
  | RT.Cons -> none
  | RT.Var  -> some (nullary "MUT")

and vl_of_packtype = function
  | RT.I8T  -> nullary "I8"
  | RT.I16T -> nullary "I16"

and vl_of_storagetype = function
  | RT.ValStorageT  vt -> vl_of_valtype  vt
  | RT.PackStorageT pt -> vl_of_packtype pt

and vl_of_fieldtype = function
  | RT.FieldT (mut, st) -> caseV [[];[];[]] [vl_of_mut mut; vl_of_storagetype st]

and vl_of_resulttype rt = vl_of_list' vl_of_valtype rt

and vl_of_comptype = function
  | RT.StructT ftl      -> caseV [["STRUCT"];[]]      [vl_of_list' vl_of_fieldtype ftl]
  | RT.ArrayT  ft       -> caseV [["ARRAY"];[]]       [vl_of_fieldtype ft]
  | RT.FuncT (rt1, rt2) -> caseV [["FUNC"];["->"];[]] [vl_of_resulttype rt1; vl_of_resulttype rt2]

and vl_of_subtype = function
  | RT.SubT (fin, tul, st) ->
    caseV [["SUB"];[];[];[]] [vl_of_final fin; vl_of_list vl_of_typeuse tul; vl_of_comptype st]

and vl_of_rectype = function
  | RT.RecT stl -> caseV [["REC"];[]] [vl_of_list' vl_of_subtype stl]

and vl_of_deftype = function
  | RT.DefT (rt, i) -> caseV [["_DEF"];[];[]] [vl_of_rectype rt; vl_of_nat32 i]

and vl_of_typeuse = function
  | RT.Idx idx -> caseV [["_IDX"];[]] [vl_of_uN_32 idx]
  | RT.Rec n   -> caseV [["REC" ];[]] [vl_of_nat32 n]
  | RT.Def dt  -> vl_of_deftype dt

and vl_of_typeuse_of_idx idx = caseV [["_IDX"];[]] [vl_of_idx idx]

and vl_of_heaptype = function
  | RT.UseHT tu -> vl_of_typeuse tu
  | RT.BotHT    -> nullary "BOT"
  | ht -> RT.string_of_heaptype ht |> nullary

and vl_of_reftype (null, ht) =
  caseV [["REF"];[];[]] [vl_of_null null; vl_of_heaptype ht]

and vl_of_addrtype at = RT.string_of_addrtype at |> nullary

and vl_of_numtype nt = RT.string_of_numtype nt |> nullary

and vl_of_vectype vt = RT.string_of_vectype vt |> nullary

and vl_of_valtype = function
  | RT.RefT rt -> vl_of_reftype rt
  | RT.NumT nt -> vl_of_numtype nt
  | RT.VecT vt -> vl_of_vectype vt
  | RT.BotT    -> nullary "BOT"

let vl_of_blocktype = function
  | RI.Ast.VarBlockType idx    -> caseV [["_IDX"   ];[]] [vl_of_idx idx]
  | RI.Ast.ValBlockType vt_opt -> caseV [["_RESULT"];[]] [vl_of_opt vl_of_valtype vt_opt]

let vl_of_limits default (limits: RT.limits) =
  let omax =
    match limits.max with
    | Some v -> some (vl_of_uN_64 v)
    | None   -> none
  in
  caseV [["["];[".."];["]"]] [vl_of_uN_64 limits.min; omax]

let vl_of_tagtype = function
  | RT.TagT tu -> vl_of_typeuse tu

let vl_of_globaltype = function
  | RT.GlobalT (mut, vt) -> caseV [[];[];[]] [vl_of_mut mut; vl_of_valtype vt]

let vl_of_tabletype = function
  | RT.TableT (at, limits, rt) ->
    caseV [[];[];[];[]] [vl_of_addrtype at; vl_of_limits default_table_max limits; vl_of_reftype rt]

let vl_of_memorytype = function
  | RT.MemoryT (at, limits) ->
    caseV [[];[];["PAGE"]] [vl_of_addrtype at; vl_of_limits default_memory_max limits]


(* Construct value *)

let vl_of_num value = match value with
  | RI.Value.I32 i32 -> caseV [["CONST"];[];[]] [nullary "I32"; vl_of_uN_32 i32]
  | RI.Value.I64 i64 -> caseV [["CONST"];[];[]] [nullary "I64"; vl_of_uN_64 i64]
  | RI.Value.F32 f32 -> caseV [["CONST"];[];[]] [nullary "F32"; vl_of_float32 f32]
  | RI.Value.F64 f64 -> caseV [["CONST"];[];[]] [nullary "F64"; vl_of_float64 f64]

let vl_of_vec = function
  | RI.Value.V128 v128 -> caseV [["VCONST"];[];[]] [nullary "V128"; vl_of_vec128 v128]

let vl_of_vec_shape shape (lanes: int64 list) =
  vl_of_vec (V128 (
    match shape with
    | RI.V128.I8x16() -> RI.V128.I8x16.of_lanes (List.map RI.I8.of_int_s (List.map Int64.to_int lanes))
    | RI.V128.I16x8() -> RI.V128.I16x8.of_lanes (List.map RI.I16.of_int_s (List.map Int64.to_int lanes))
    | RI.V128.I32x4() -> RI.V128.I32x4.of_lanes (List.map Int64.to_int32 lanes)
    | RI.V128.I64x2() -> RI.V128.I64x2.of_lanes lanes
    | RI.V128.F32x4() -> RI.V128.F32x4.of_lanes (List.map (fun i -> i |> Int64.to_int32 |> RI.F32.of_bits) lanes)
    | RI.V128.F64x2() -> RI.V128.F64x2.of_lanes (List.map RI.F64.of_bits lanes)
  ))

let rec vl_of_ref = function
  | RI.Value.NullRef ht   -> caseV [["REF.NULL"];[]] [vl_of_heaptype ht]
  | RI.Script.HostRef i32 -> caseV [["REF.HOST_ADDR"];[]] [vl_of_nat32 i32]
  | RI.Extern.ExternRef r -> caseV [["REF.EXTERN"];[]] [vl_of_ref r]
  | r -> error no ("vl_of_ref: " ^ RI.Value.string_of_ref r)


let vl_of_value (v: RI.Value.value) = match v with
  | Num n -> vl_of_num n
  | Vec v -> vl_of_vec v
  | Ref r -> vl_of_ref r


(* Construct operation *)

let vl_of_sx = function
  | RI.Pack.S -> nullary "S"
  | RI.Pack.U -> nullary "U"

let vl_of_op f1 f2 = function
  | RI.Value.I32 op -> [nullary "I32"; f1 op]
  | RI.Value.I64 op -> [nullary "I64"; f1 op]
  | RI.Value.F32 op -> [nullary "F32"; f2 op]
  | RI.Value.F64 op -> [nullary "F64"; f2 op]



let vl_of_unop =
  let open RI in
  let open Ast in
  let vl_of_int_unop op =
    match op with
    | IntOp.Clz    -> nullary "CLZ"
    | IntOp.Ctz    -> nullary "CTZ"
    | IntOp.Popcnt -> nullary "POPCNT"
    | IntOp.ExtendS Pack.Pack8  -> caseV [["EXTEND"];[]] [vl_of_nat 8  |> caseV1]
    | IntOp.ExtendS Pack.Pack16 -> caseV [["EXTEND"];[]] [vl_of_nat 16 |> caseV1]
    | IntOp.ExtendS Pack.Pack32 -> caseV [["EXTEND"];[]] [vl_of_nat 32 |> caseV1]
    | IntOp.ExtendS Pack.Pack64 -> caseV [["EXTEND"];[]] [vl_of_nat 64 |> caseV1]
  in
  let vl_of_float_unop op =
    match op with
    | FloatOp.Neg     -> nullary "NEG"
    | FloatOp.Abs     -> nullary "ABS"
    | FloatOp.Ceil    -> nullary "CEIL"
    | FloatOp.Floor   -> nullary "FLOOR"
    | FloatOp.Trunc   -> nullary "TRUNC"
    | FloatOp.Nearest -> nullary "NEAREST"
    | FloatOp.Sqrt    -> nullary "SQRT"
  in
  vl_of_op vl_of_int_unop vl_of_float_unop

let vl_of_binop =
  let open RI.Ast in
  let vl_of_int_binop bop =
    match bop with
    | IntOp.Add    -> nullary "ADD"
    | IntOp.Sub    -> nullary "SUB"
    | IntOp.Mul    -> nullary "MUL"
    | IntOp.Div sx -> caseV [["DIV"];[]] [vl_of_sx sx]
    | IntOp.Rem sx -> caseV [["REM"];[]] [vl_of_sx sx]
    | IntOp.And    -> nullary "AND"
    | IntOp.Or     -> nullary "OR"
    | IntOp.Xor    -> nullary "XOR"
    | IntOp.Shl    -> nullary "SHL"
    | IntOp.Shr sx -> caseV [["SHR"];[]] [vl_of_sx sx]
    | IntOp.Rotl   -> nullary "ROTL"
    | IntOp.Rotr   -> nullary "ROTR"
  in
  let vl_of_float_binop bop =
    match bop with
    | FloatOp.Add      -> nullary "ADD"
    | FloatOp.Sub      -> nullary "SUB"
    | FloatOp.Mul      -> nullary "MUL"
    | FloatOp.Div      -> nullary "DIV"
    | FloatOp.Min      -> nullary "MIN"
    | FloatOp.Max      -> nullary "MAX"
    | FloatOp.CopySign -> nullary "COPYSIGN"
  in
  vl_of_op vl_of_int_binop vl_of_float_binop

let vl_of_testop: RI.Ast.testop -> value list =
  let vl_of_int_testop : RI.Ast.IntOp.testop -> value = function
    | Eqz -> nullary "EQZ"
  in
  let vl_of_float_testop: RI.Ast.FloatOp.testop -> value = function
    | _ -> .
  in
  vl_of_op vl_of_int_testop vl_of_float_testop

let vl_of_relop =
  let open RI.Ast in
  let vl_of_int_relop rop =
    match rop with
    | IntOp.Eq    -> nullary "EQ"
    | IntOp.Ne    -> nullary "NE"
    | IntOp.Lt sx -> caseV [["LT"];[]] [vl_of_sx sx]
    | IntOp.Gt sx -> caseV [["GT"];[]] [vl_of_sx sx]
    | IntOp.Le sx -> caseV [["LE"];[]] [vl_of_sx sx]
    | IntOp.Ge sx -> caseV [["GE"];[]] [vl_of_sx sx]
  in
  let vl_of_float_relop rop =
    match rop with
    | FloatOp.Eq -> nullary "EQ"
    | FloatOp.Ne -> nullary "NE"
    | FloatOp.Lt -> nullary "LT"
    | FloatOp.Gt -> nullary "GT"
    | FloatOp.Le -> nullary "LE"
    | FloatOp.Ge -> nullary "GE"
  in
  vl_of_op vl_of_int_relop vl_of_float_relop

let vl_of_cvtop cop =
  let open RI.Value in
  let open RI.Ast in
  let vl_of_int_cvtop num_bits cop =
    match cop with
    | IntOp.ExtendI32 sx     -> nullary "I32", caseV [["EXTEND"   ];[]] [vl_of_sx sx]
    | IntOp.WrapI64          -> nullary "I64", nullary "WRAP"
    | IntOp.TruncF32 sx      -> nullary "F32", caseV [["TRUNC"    ];[]] [vl_of_sx sx]
    | IntOp.TruncF64 sx      -> nullary "F64", caseV [["TRUNC"    ];[]] [vl_of_sx sx]
    | IntOp.TruncSatF32 sx   -> nullary "F32", caseV [["TRUNC_SAT"];[]] [vl_of_sx sx]
    | IntOp.TruncSatF64 sx   -> nullary "F64", caseV [["TRUNC_SAT"];[]] [vl_of_sx sx]
    | IntOp.ReinterpretFloat -> nullary ("F" ^ num_bits), nullary "REINTERPRET"
  in
  let vl_of_float_cvtop num_bits cop =
    match cop with
    | FloatOp.ConvertI32 sx  -> nullary "I32", caseV [["CONVERT"];[]] [vl_of_sx sx]
    | FloatOp.ConvertI64 sx  -> nullary "I64", caseV [["CONVERT"];[]] [vl_of_sx sx]
    | FloatOp.PromoteF32     -> nullary "F32", caseV [["PROMOTE"]] []
    | FloatOp.DemoteF64      -> nullary "F64", caseV [["DEMOTE" ]] []
    | FloatOp.ReinterpretInt -> nullary ("I" ^ num_bits), nullary "REINTERPRET"
  in
  match cop with
  | I32 op -> let to_, op' = vl_of_int_cvtop "32" op in
              [nullary "I32"; to_; op']
  | I64 op -> let to_, op' = vl_of_int_cvtop "64" op in
              [nullary "I64"; to_; op']
  | F32 op -> let to_, op' = vl_of_float_cvtop "32" op in
              [nullary "F32"; to_; op']
  | F64 op -> let to_, op' = vl_of_float_cvtop "64" op in
              [nullary "F64"; to_; op']


(* Vector operator *)

let vl_of_shape d1 d2 = caseV [[];["X"];[]] [d1; d2]

let vl_of_half = function
  | RI.Ast.V128Op.Low  -> nullary "LOW"
  | RI.Ast.V128Op.High -> nullary "HIGH"

let vl_of_vop f1 f2 = function
  | RI.Value.V128 vop -> (
    match vop with
    | RI.V128.I8x16 op -> [ vl_of_shape (nullary "I8" ) sixteen; f1 op ]
    | RI.V128.I16x8 op -> [ vl_of_shape (nullary "I16") eight  ; f1 op ]
    | RI.V128.I32x4 op -> [ vl_of_shape (nullary "I32") four   ; f1 op ]
    | RI.V128.I64x2 op -> [ vl_of_shape (nullary "I64") two    ; f1 op ]
    | RI.V128.F32x4 op -> [ vl_of_shape (nullary "F32") four   ; f2 op ]
    | RI.V128.F64x2 op -> [ vl_of_shape (nullary "F64") two    ; f2 op ]
  )

let vl_of_vop_opt f1 f2 = function
  | RI.Value.V128 vop -> (
    match vop with
    | RI.V128.I8x16 op -> Option.map (fun v -> [ vl_of_shape (nullary "I8" ) sixteen; v ]) (f1 op)
    | RI.V128.I16x8 op -> Option.map (fun v -> [ vl_of_shape (nullary "I16") eight  ; v ]) (f1 op)
    | RI.V128.I32x4 op -> Option.map (fun v -> [ vl_of_shape (nullary "I32") four   ; v ]) (f1 op)
    | RI.V128.I64x2 op -> Option.map (fun v -> [ vl_of_shape (nullary "I64") two    ; v ]) (f1 op)
    | RI.V128.F32x4 op -> Option.map (fun v -> [ vl_of_shape (nullary "F32") four   ; v ]) (f2 op)
    | RI.V128.F64x2 op -> Option.map (fun v -> [ vl_of_shape (nullary "F64") two    ; v ]) (f2 op)
  )

let vl_of_viop f1 :
    ('a, 'a, 'a, 'a, RI.Ast.void, RI.Ast.void) RI.V128.laneop RI.Value.vecop -> value list = function
  | RI.Value.V128 vop -> (
    match vop with
    | RI.V128.I8x16 op -> [ vl_of_shape (nullary "I8" ) sixteen; f1 op ]
    | RI.V128.I16x8 op -> [ vl_of_shape (nullary "I16") eight  ; f1 op ]
    | RI.V128.I32x4 op -> [ vl_of_shape (nullary "I32") four   ; f1 op ]
    | RI.V128.I64x2 op -> [ vl_of_shape (nullary "I64") two    ; f1 op ]
    | _ -> .
  )

let vl_of_vbitmaskop = function
  | RI.Value.V128 (vop : RI.Ast.V128Op.bitmaskop) -> (
    match vop with
    | RI.V128.I8x16 _ -> [ vl_of_shape (nullary "I8" ) sixteen ]
    | RI.V128.I16x8 _ -> [ vl_of_shape (nullary "I16") eight   ]
    | RI.V128.I32x4 _ -> [ vl_of_shape (nullary "I32") four    ]
    | RI.V128.I64x2 _ -> [ vl_of_shape (nullary "I64") two     ]
    | _ -> .
  )

let vl_of_int_vtestop : RI.Ast.V128Op.itestop -> value = function
  | RI.Ast.V128Op.AllTrue -> nullary "ALL_TRUE"

let vl_of_float_vtestop : RI.Ast.void -> value = function
  | _ -> .

let vl_of_vtestop = vl_of_vop vl_of_int_vtestop vl_of_float_vtestop

let vl_of_int_vrelop : RI.Ast.V128Op.irelop -> value = function
  | RI.Ast.V128Op.Eq -> nullary "EQ"
  | RI.Ast.V128Op.Ne -> nullary "NE"
  | RI.Ast.V128Op.Lt sx -> caseV [["LT"];[]] [vl_of_sx sx]
  | RI.Ast.V128Op.Le sx -> caseV [["LE"];[]] [vl_of_sx sx]
  | RI.Ast.V128Op.Gt sx -> caseV [["GT"];[]] [vl_of_sx sx]
  | RI.Ast.V128Op.Ge sx -> caseV [["GE"];[]] [vl_of_sx sx]

let vl_of_float_vrelop : RI.Ast.V128Op.frelop -> value = function
  | RI.Ast.V128Op.Eq -> nullary "EQ"
  | RI.Ast.V128Op.Ne -> nullary "NE"
  | RI.Ast.V128Op.Lt -> nullary "LT"
  | RI.Ast.V128Op.Le -> nullary "LE"
  | RI.Ast.V128Op.Gt -> nullary "GT"
  | RI.Ast.V128Op.Ge -> nullary "GE"

let vl_of_vrelop = vl_of_vop vl_of_int_vrelop vl_of_float_vrelop

let vl_of_int_vunop : RI.Ast.V128Op.iunop -> value = function
  | RI.Ast.V128Op.Abs    -> nullary "ABS"
  | RI.Ast.V128Op.Neg    -> nullary "NEG"
  | RI.Ast.V128Op.Popcnt -> nullary "POPCNT"

let vl_of_float_vunop : RI.Ast.V128Op.funop -> value = function
  | RI.Ast.V128Op.Abs     -> nullary "ABS"
  | RI.Ast.V128Op.Neg     -> nullary "NEG"
  | RI.Ast.V128Op.Sqrt    -> nullary "SQRT"
  | RI.Ast.V128Op.Ceil    -> nullary "CEIL"
  | RI.Ast.V128Op.Floor   -> nullary "FLOOR"
  | RI.Ast.V128Op.Trunc   -> nullary "TRUNC"
  | RI.Ast.V128Op.Nearest -> nullary "NEAREST"

let vl_of_vunop = vl_of_vop vl_of_int_vunop vl_of_float_vunop

let vl_of_int_vbinop_opt : RI.Ast.V128Op.ibinop -> value option = function
  | RI.Ast.V128Op.Add             -> Some (nullary "ADD")
  | RI.Ast.V128Op.Sub             -> Some (nullary "SUB")
  | RI.Ast.V128Op.Mul             -> Some (nullary "MUL")
  | RI.Ast.V128Op.Min sx          -> Some (caseV [["MIN"];[]] [vl_of_sx sx])
  | RI.Ast.V128Op.Max sx          -> Some (caseV [["MAX"];[]] [vl_of_sx sx])
  | RI.Ast.V128Op.AvgrU           -> Some (nullary "AVGRU")  (* U *)
  | RI.Ast.V128Op.AddSat sx       -> Some (caseV [["ADD_SAT"];[]] [vl_of_sx sx])
  | RI.Ast.V128Op.SubSat sx       -> Some (caseV [["SUB_SAT"];[]] [vl_of_sx sx])
  | RI.Ast.V128Op.Q15MulRSatS     -> Some (nullary "Q15MULR_SATS")     (* S *)
  | RI.Ast.V128Op.RelaxedQ15MulRS -> Some (nullary "RELAXED_Q15MULRS") (* S *)
  | _ -> None

let vl_of_float_vbinop_opt : RI.Ast.V128Op.fbinop -> value option = function
  | RI.Ast.V128Op.Add        -> Some (nullary "ADD")
  | RI.Ast.V128Op.Sub        -> Some (nullary "SUB")
  | RI.Ast.V128Op.Mul        -> Some (nullary "MUL")
  | RI.Ast.V128Op.Div        -> Some (nullary "DIV")
  | RI.Ast.V128Op.Min        -> Some (nullary "MIN")
  | RI.Ast.V128Op.Max        -> Some (nullary "MAX")
  | RI.Ast.V128Op.Pmin       -> Some (nullary "PMIN")
  | RI.Ast.V128Op.Pmax       -> Some (nullary "PMAX")
  | RI.Ast.V128Op.RelaxedMin -> Some (nullary "RELAXED_MIN")
  | RI.Ast.V128Op.RelaxedMax -> Some (nullary "RELAXED_MAX")

let vl_of_vbinop_opt = vl_of_vop_opt vl_of_int_vbinop_opt vl_of_float_vbinop_opt

let vl_of_int_vternop_opt : RI.Ast.V128Op.iternop -> value option = function
  | RI.Ast.V128Op.RelaxedLaneselect -> Some (nullary "RELAXED_LANESELECT")
  | _ -> None

let vl_of_float_vternop_opt : RI.Ast.V128Op.fternop -> value option = function
  | RI.Ast.V128Op.RelaxedMadd  -> Some (nullary "RELAXED_MADD")
  | RI.Ast.V128Op.RelaxedNmadd -> Some (nullary "RELAXED_NMADD")

let vl_of_vternop_opt = vl_of_vop_opt vl_of_int_vternop_opt vl_of_float_vternop_opt

let vl_of_special_vbinop =
  let open RI in
  let open Ast in
  let open Value in
  let mk_instr c n = caseV ([c] :: List.init n (Fun.const [])) in
  function
  | V128 (V128.I8x16 (V128Op.Swizzle))           -> mk_instr "VSWIZZLOP" 2 [ vl_of_shape (nullary "I8" ) sixteen; nullary "SWIZZLE" ]
  | V128 (V128.I8x16 (V128Op.RelaxedSwizzle))    -> mk_instr "VSWIZZLOP" 2 [ vl_of_shape (nullary "I8" ) sixteen; nullary "RELAXED_SWIZZLE" ]
  | V128 (V128.I8x16 (V128Op.Shuffle l))         -> mk_instr "VSHUFFLE"  2 [ vl_of_shape (nullary "I8" ) sixteen; vl_of_list vl_of_nat8 l ]
  | V128 (V128.I8x16 (V128Op.Narrow sx))         -> mk_instr "VNARROW"   3 [ vl_of_shape (nullary "I8" ) sixteen; vl_of_shape (nullary "I16") eight  ; vl_of_sx sx ]
  | V128 (V128.I16x8 (V128Op.Narrow sx))         -> mk_instr "VNARROW"   3 [ vl_of_shape (nullary "I16") eight  ; vl_of_shape (nullary "I32") four   ; vl_of_sx sx ]
  | V128 (V128.I16x8 (V128Op.ExtMul (half, sx))) -> mk_instr "VEXTBINOP" 3 [ vl_of_shape (nullary "I16") eight  ; vl_of_shape (nullary "I8" ) sixteen; caseV [["EXTMUL"];[];[]] [vl_of_half half; vl_of_sx sx] ]
  | V128 (V128.I32x4 (V128Op.ExtMul (half, sx))) -> mk_instr "VEXTBINOP" 3 [ vl_of_shape (nullary "I32") four   ; vl_of_shape (nullary "I16") eight  ; caseV [["EXTMUL"];[];[]] [vl_of_half half; vl_of_sx sx] ]
  | V128 (V128.I64x2 (V128Op.ExtMul (half, sx))) -> mk_instr "VEXTBINOP" 3 [ vl_of_shape (nullary "I64") two    ; vl_of_shape (nullary "I32") four   ; caseV [["EXTMUL"];[];[]] [vl_of_half half; vl_of_sx sx] ]
  | V128 (V128.I32x4 (V128Op.DotS))              -> mk_instr "VEXTBINOP" 3 [ vl_of_shape (nullary "I32") four   ; vl_of_shape (nullary "I16") eight  ; nullary "DOTS"         (* S *) ]
  | V128 (V128.I16x8 (V128Op.RelaxedDot))        -> mk_instr "VEXTBINOP" 3 [ vl_of_shape (nullary "I16") eight  ; vl_of_shape (nullary "I8" ) sixteen; nullary "RELAXED_DOTS" (* S *) ]
  | vop -> BI.Construct.error_instr "vl_of_specivl_vbinop" (VecBinary vop)

let vl_of_special_vternop = function
  | RI.Value.V128 (RI.V128.I32x4 RI.Ast.V128Op.RelaxedDotAddS) ->
      caseV [["VEXTTERNOP"];[];[];[]] [ vl_of_shape (nullary "I32") four   ;
                                        vl_of_shape (nullary "I8" ) sixteen;
                                        nullary "RELAXED_DOT_ADDS" (* S *) ]
  | vop -> BI.Construct.error_instr "vl_of_specivl_vternop" (VecTernary vop)

let vl_of_int_vcvtop_opt = function
  | RI.Ast.V128Op.Extend (half, sx)        -> Some (None, caseV [["EXTEND"];[];[]] [vl_of_half half; vl_of_sx sx])
  | RI.Ast.V128Op.TruncSatF32x4 sx         -> Some (Some (vl_of_shape (nullary "F32") four), caseV [["TRUNC_SAT"];[];[]] [vl_of_sx sx; none])
  | RI.Ast.V128Op.TruncSatZeroF64x2 sx     -> Some (Some (vl_of_shape (nullary "F64") two ), caseV [["TRUNC_SAT"];[];[]] [vl_of_sx sx; some (nullary "ZERO")])
  | RI.Ast.V128Op.RelaxedTruncF32x4 sx     -> Some (Some (vl_of_shape (nullary "F32") four), caseV [["RELAXED_TRUNC"];[];[]] [vl_of_sx sx; none])
  | RI.Ast.V128Op.RelaxedTruncZeroF64x2 sx -> Some (Some (vl_of_shape (nullary "F64") two ), caseV [["RELAXED_TRUNC"];[];[]] [vl_of_sx sx; some (nullary "ZERO")])
  | _ -> None

let vl_of_float32_vcvtop_opt = function
  | RI.Ast.V128Op.DemoteZeroF64x2 -> Some (Some (vl_of_shape (nullary "F64") two ), caseV [["DEMOTE"];[]] [nullary "ZERO"])
  | RI.Ast.V128Op.ConvertI32x4 sx -> Some (Some (vl_of_shape (nullary "I32") four), caseV [["CONVERT"];[];[]] [none; vl_of_sx sx])
  | _ -> None

let vl_of_float64_vcvtop_opt = function
  | RI.Ast.V128Op.PromoteLowF32x4 -> Some (Some (vl_of_shape (nullary "F32") four), nullary "PROMOTE")
  | RI.Ast.V128Op.ConvertI32x4 sx -> Some (Some (vl_of_shape (nullary "I32") four), caseV [["CONVERT"];[];[]] [some (nullary "LOW"); vl_of_sx sx])
  | _ -> None

let vl_of_vcvtop_opt =
  let open RI in
  let open Value in
  function
  | V128 vop -> (
    match vop with
    | V128.I8x16 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> BI.Construct.error_instr "vl_of_vcvtop" (VecConvert (V128 vop)) in
        [ vl_of_shape (nullary "I8") sixteen; sh; op' ]
      ) (vl_of_int_vcvtop_opt op)
    )
    | V128.I16x8 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> vl_of_shape (nullary "I8") sixteen in
        [ vl_of_shape (nullary "I16") eight; sh; op' ]
      ) (vl_of_int_vcvtop_opt op)
    )
    | V128.I32x4 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> vl_of_shape (nullary "I16") eight in
        [ vl_of_shape (nullary "I32") four; sh; op' ]
      ) (vl_of_int_vcvtop_opt op)
    )
    | V128.I64x2 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> vl_of_shape (nullary "I32") four in
        [ vl_of_shape (nullary "I64") two; sh; op' ]
      ) (vl_of_int_vcvtop_opt op)
    )
    | V128.F32x4 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> BI.Construct.error_instr "vl_of_vcvtop" (VecConvert (V128 vop)) in
        [ vl_of_shape (nullary "F32") four; sh; op' ]
      ) (vl_of_float32_vcvtop_opt op)
    )
    | V128.F64x2 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> BI.Construct.error_instr "vl_of_vcvtop" (VecConvert (V128 vop)) in
        [ vl_of_shape (nullary "F64") two; sh; op' ]
      ) (vl_of_float64_vcvtop_opt op)
    )
  )


let vl_of_special_vcvtop =
  let open RI in
  let open Ast in
  let open Value in
  function
  | V128 (V128.I16x8 (V128Op.ExtAddPairwise sx)) ->
    caseV [["VEXTUNOP"];[];[];[]] [ vl_of_shape (nullary "I16") eight; vl_of_shape (nullary "I8" ) sixteen; caseV [["EXTADD_PAIRWISE"];[]] [vl_of_sx sx] ]
  | V128 (V128.I32x4 (V128Op.ExtAddPairwise sx)) ->
    caseV [["VEXTUNOP"];[];[];[]] [ vl_of_shape (nullary "I32") four ; vl_of_shape (nullary "I16") eight  ; caseV [["EXTADD_PAIRWISE"];[]] [vl_of_sx sx] ]
  | vop -> BI.Construct.error_instr "vl_of_special_vcvtop" (VecConvert vop)

let vl_of_int_vshiftop : RI.Ast.V128Op.ishiftop -> value = function
  | RI.Ast.V128Op.Shl    -> nullary "SHL"
  | RI.Ast.V128Op.Shr sx -> caseV [["SHR"];[]] [vl_of_sx sx]

let vl_of_vshiftop = vl_of_viop vl_of_int_vshiftop

let vl_of_vvtestop : RI.Ast.vvtestop -> value list = function
  | V128 vop -> (
    match vop with
    | RI.Ast.V128Op.AnyTrue -> [ nullary "V128"; nullary "ANY_TRUE" ]
  )

let vl_of_vvunop :RI.Ast.vvunop -> value list = function
  | V128 vop ->
    (match vop with
    | RI.Ast.V128Op.Not -> [ nullary "V128"; nullary "NOT" ]
    )

let vl_of_vvbinop : RI.Ast.vvbinop -> value list = function
  | V128 vop ->
    RI.Ast.(match vop with
    | V128Op.And    -> [ nullary "V128"; nullary "AND"    ]
    | V128Op.Or     -> [ nullary "V128"; nullary "OR"     ]
    | V128Op.Xor    -> [ nullary "V128"; nullary "XOR"    ]
    | V128Op.AndNot -> [ nullary "V128"; nullary "ANDNOT" ]
    )

let vl_of_vvternop : RI.Ast.vvternop -> value list = function
  | V128 vop ->
    (match vop with
    | RI.Ast.V128Op.Bitselect -> [ nullary "V128"; nullary "BITSELECT" ]
    )

let vl_of_vsplatop : RI.Ast.vsplatop -> value list = function
  | V128 vop ->
    RI.(match vop with
    | V128.I8x16 _ -> [ vl_of_shape (nullary "I8" ) sixteen ]
    | V128.I16x8 _ -> [ vl_of_shape (nullary "I16") eight   ]
    | V128.I32x4 _ -> [ vl_of_shape (nullary "I32") four    ]
    | V128.I64x2 _ -> [ vl_of_shape (nullary "I64") two     ]
    | V128.F32x4 _ -> [ vl_of_shape (nullary "F32") four    ]
    | V128.F64x2 _ -> [ vl_of_shape (nullary "F64") two     ]
    )

let vl_of_vextractop : RI.Ast.vextractop -> value list = function
  | V128 vop ->
    RI.(match vop with
    | V128.I8x16(Extract (n, sx)) -> [ vl_of_shape (nullary "I8" ) sixteen; some (vl_of_sx sx); vl_of_nat8 n; ]
    | V128.I16x8(Extract (n, sx)) -> [ vl_of_shape (nullary "I16") eight  ; some (vl_of_sx sx); vl_of_nat8 n; ]
    | V128.I32x4(Extract (n, _ )) -> [ vl_of_shape (nullary "I32") four   ; none; vl_of_nat8 n ]
    | V128.I64x2(Extract (n, _ )) -> [ vl_of_shape (nullary "I64") two    ; none; vl_of_nat8 n ]
    | V128.F32x4(Extract (n, _ )) -> [ vl_of_shape (nullary "F32") four   ; none; vl_of_nat8 n ]
    | V128.F64x2(Extract (n, _ )) -> [ vl_of_shape (nullary "F64") two    ; none; vl_of_nat8 n ]
    )

let vl_of_vreplaceop : RI.Ast.vreplaceop -> value list = function
  | V128 vop ->
    RI.(match vop with
    | V128.I8x16 (Replace n) -> [ vl_of_shape (nullary "I8" ) sixteen; vl_of_nat8 n ]
    | V128.I16x8 (Replace n) -> [ vl_of_shape (nullary "I16") eight  ; vl_of_nat8 n ]
    | V128.I32x4 (Replace n) -> [ vl_of_shape (nullary "I32") four   ; vl_of_nat8 n ]
    | V128.I64x2 (Replace n) -> [ vl_of_shape (nullary "I64") two    ; vl_of_nat8 n ]
    | V128.F32x4 (Replace n) -> [ vl_of_shape (nullary "F32") four   ; vl_of_nat8 n ]
    | V128.F64x2 (Replace n) -> [ vl_of_shape (nullary "F64") two    ; vl_of_nat8 n ]
    )


let vl_of_packsize = function
  | RI.Pack.Pack8  -> vl_of_nat 8  |> caseV1
  | RI.Pack.Pack16 -> vl_of_nat 16 |> caseV1
  | RI.Pack.Pack32 -> vl_of_nat 32 |> caseV1
  | RI.Pack.Pack64 -> vl_of_nat 64 |> caseV1

let vl_of_packshape = function
  | RI.Pack.Pack8x8  -> [vl_of_nat 8  |> caseV1; vl_of_nat 8]
  | RI.Pack.Pack16x4 -> [vl_of_nat 16 |> caseV1; vl_of_nat 4]
  | RI.Pack.Pack32x2 -> [vl_of_nat 32 |> caseV1; vl_of_nat 2]

let vl_of_memop f idx (memop: (RI.Types.numtype, 'p) RI.Ast.memop) =
  let str = [("ALIGN" , vl_of_uN (Z.of_int memop.align)  |> ref);
             ("OFFSET", vl_of_uN_64 memop.offset         |> ref)]
  in
  [vl_of_numtype memop.ty; f memop.pack; vl_of_memidx idx; strV str]

let vl_of_packsize_sx (ps, sx) = caseV [[];["_"];[]] [vl_of_packsize ps; vl_of_sx sx]

let vl_of_loadop = vl_of_opt vl_of_packsize_sx |> vl_of_memop

let vl_of_storeop = vl_of_opt (fun sz -> vl_of_packsize sz |> caseV1) |> vl_of_memop

let vl_of_vloadop idx (vloadop: RI.Ast.vloadop) =
  let str =
    Record.empty
    |> Record.add "ALIGN"  (vl_of_nat   vloadop.align  |> caseV1)
    |> Record.add "OFFSET" (vl_of_nat64 vloadop.offset |> caseV1)
  in
  let vmemop = match vloadop.pack with
  | Option.Some (packsize, vext) ->
    (match vext with
    | RI.Pack.ExtLane (packshape, sx) -> caseV [["SHAPE"];["X"];["_"];[]] (vl_of_packshape packshape @ [vl_of_sx sx])
    | RI.Pack.ExtSplat -> caseV [["SPLAT"];[]] [ vl_of_packsize packsize ]
    | RI.Pack.ExtZero  -> caseV [["ZERO" ];[]] [ vl_of_packsize packsize ]
    ) |> some
  | None -> none in
  [ vl_of_vectype V128T; vmemop; vl_of_memidx idx; StrV str ]

let vl_of_vstoreop idx (vstoreop: RI.Ast.vstoreop) =
  let str =
    Record.empty
    |> Record.add "ALIGN"  (vl_of_nat   vstoreop.align  |> caseV1)
    |> Record.add "OFFSET" (vl_of_nat64 vstoreop.offset |> caseV1)
  in
  [ vl_of_vectype V128T; vl_of_memidx idx; StrV str ]

let vl_of_vlaneop idx (vlaneop: RI.Ast.vlaneop) laneidx =
  let packsize = vlaneop.pack in
  let str =
    Record.empty
    |> Record.add "ALIGN"  (vl_of_nat   vlaneop.align  |> caseV1)
    |> Record.add "OFFSET" (vl_of_nat64 vlaneop.offset |> caseV1)
  in
  [ vl_of_vectype V128T; vl_of_packsize packsize; vl_of_memidx idx; StrV str; vl_of_nat8 laneidx ]



(* Construct instruction *)

let vl_of_catch (catch: RI.Ast.catch) =
  let mk_catch c n = caseV ([c] :: List.init n (Fun.const [])) in
  match catch.it with
  | Catch    (idx1, idx2) -> mk_catch "CATCH"         2 [vl_of_idx idx1; vl_of_idx idx2]
  | CatchRef (idx1, idx2) -> mk_catch "CATCH_REF"     2 [vl_of_idx idx1; vl_of_idx idx2]
  | CatchAll    idx       -> mk_catch "CATCH_ALL"     1 [vl_of_idx idx]
  | CatchAllRef idx       -> mk_catch "CATCH_ALL_REF" 1 [vl_of_idx idx]

let rec vl_of_instr (instr: RI.Ast.instr) =
  let mk_instr0 = nullary in
  let mk_instr c n = caseV ([c] :: List.init n (Fun.const [])) in
  match instr.it with
  (* wasm values *)
  | Const num -> vl_of_num num.it
  | VecConst vec -> vl_of_vec vec.it
  | RefNull ht -> mk_instr "REF.NULL" 1 [vl_of_heaptype ht]
  (* wasm instructions *)
  | Unreachable -> mk_instr0 "UNREACHABLE"
  | Nop  -> mk_instr0 "NOP"
  | Drop -> mk_instr0 "DROP"
  | Unary   op -> mk_instr "UNOP"   2 (vl_of_unop     op)
  | Binary  op -> mk_instr "BINOP"  2 (vl_of_binop    op)
  | Test    op -> mk_instr "TESTOP" 2 (vl_of_testop   op)
  | Compare op -> mk_instr "RELOP"  2 (vl_of_relop    op)
  | Convert op -> mk_instr "CVTOP"  3 (vl_of_cvtop    op)
  | VecTest        vop -> mk_instr "VTESTOP" 2 (vl_of_vtestop vop)
  | VecCompare     vop -> mk_instr "VRELOP"  2 (vl_of_vrelop  vop)
  | VecUnary       vop -> mk_instr "VUNOP"   2 (vl_of_vunop   vop)
  | VecBinary      vop -> (match vl_of_vbinop_opt  vop with Some l -> mk_instr "VBINOP"  2 l | None -> vl_of_special_vbinop  vop)
  | VecTernary     vop -> (match vl_of_vternop_opt vop with Some l -> mk_instr "VTERNOP" 2 l | None -> vl_of_special_vternop vop)
  | VecConvert     vop -> (match vl_of_vcvtop_opt  vop with Some l -> mk_instr "VCVTOP"  3 l | None -> vl_of_special_vcvtop  vop)
  | VecShift       vop -> mk_instr "VSHIFTOP"      2 (vl_of_vshiftop   vop)
  | VecBitmask     vop -> mk_instr "VBITMASK"      1 (vl_of_vbitmaskop vop)
  | VecTestBits    vop -> mk_instr "VVTESTOP"      2 (vl_of_vvtestop   vop)
  | VecUnaryBits   vop -> mk_instr "VVUNOP"        2 (vl_of_vvunop     vop)
  | VecBinaryBits  vop -> mk_instr "VVBINOP"       2 (vl_of_vvbinop    vop)
  | VecTernaryBits vop -> mk_instr "VVTERNOP"      2 (vl_of_vvternop   vop)
  | VecSplat       vop -> mk_instr "VSPLAT"        1 (vl_of_vsplatop   vop)
  | VecExtract     vop -> mk_instr "VEXTRACT_LANE" 3 (vl_of_vextractop vop)
  | VecReplace     vop -> mk_instr "VREPLACE_LANE" 2 (vl_of_vreplaceop vop)
  | RefIsNull -> mk_instr0 "REF.IS_NULL"
  | RefFunc idx     -> mk_instr "REF.FUNC"   1 [vl_of_idx idx]
  | Select  vtl_opt -> mk_instr "SELECT"     1 [vl_of_opt (vl_of_list vl_of_valtype) vtl_opt]
  | LocalGet  idx   -> mk_instr "LOCAL.GET"  1 [vl_of_idx idx]
  | LocalSet  idx   -> mk_instr "LOCAL.SET"  1 [vl_of_idx idx]
  | LocalTee  idx   -> mk_instr "LOCAL.TEE"  1 [vl_of_idx idx]
  | GlobalGet idx   -> mk_instr "GLOBAL.GET" 1 [vl_of_idx idx]
  | GlobalSet idx   -> mk_instr "GLOBAL.SET" 1 [vl_of_idx idx]
  | TableGet  idx   -> mk_instr "TABLE.GET"  1 [vl_of_idx idx]
  | TableSet  idx   -> mk_instr "TABLE.SET"  1 [vl_of_idx idx]
  | TableSize idx   -> mk_instr "TABLE.SIZE" 1 [vl_of_idx idx]
  | TableGrow idx   -> mk_instr "TABLE.GROW" 1 [vl_of_idx idx]
  | TableFill idx   -> mk_instr "TABLE.FILL" 1 [vl_of_idx idx]
  | TableCopy (idx1, idx2) -> mk_instr "TABLE.COPY" 2 [vl_of_idx idx1; vl_of_idx idx2]
  | TableInit (idx1, idx2) -> mk_instr "TABLE.INIT" 2 [vl_of_idx idx1; vl_of_idx idx2]
  | ElemDrop idx -> mk_instr "ELEM.DROP" 1 [vl_of_idx idx]
  | Block (bt, instrs) -> mk_instr "BLOCK" 2 [vl_of_blocktype bt; vl_of_list vl_of_instr instrs]
  | Loop  (bt, instrs) -> mk_instr "LOOP"  2 [vl_of_blocktype bt; vl_of_list vl_of_instr instrs]
  | If (bt, instrs1, instrs2) ->
    caseV [["IF"];[];["ELSE"];[]] [
      vl_of_blocktype bt;
      vl_of_list vl_of_instr instrs1;
      vl_of_list vl_of_instr instrs2;
    ]
  | Br   idx -> mk_instr "BR"    1 [vl_of_idx idx]
  | BrIf idx -> mk_instr "BR_IF" 1 [vl_of_idx idx]
  | BrTable (idxs, idx) -> mk_instr "BR_TABLE" 2 [vl_of_list vl_of_idx idxs; vl_of_idx idx]
  | BrOnNull    idx -> mk_instr "BR_ON_NULL"     1 [vl_of_idx idx]
  | BrOnNonNull idx -> mk_instr "BR_ON_NON_NULL" 1 [vl_of_idx idx]
  | BrOnCast     (idx, rt1, rt2) -> mk_instr "BR_ON_CAST"      3 [vl_of_idx idx; vl_of_reftype rt1; vl_of_reftype rt2]
  | BrOnCastFail (idx, rt1, rt2) -> mk_instr "BR_ON_CAST_FAIL" 3 [vl_of_idx idx; vl_of_reftype rt1; vl_of_reftype rt2]
  | Return -> mk_instr0 "RETURN"
  | Call    idx -> mk_instr "CALL"     1 [vl_of_idx idx]
  | CallRef idx -> mk_instr "CALL_REF" 1 [vl_of_typeuse_of_idx idx]
  | CallIndirect (idx1, idx2) -> mk_instr "CALL_INDIRECT" 2 [vl_of_idx idx1; vl_of_typeuse_of_idx idx2]
  | ReturnCall    idx -> mk_instr "RETURN_CALL"     1 [vl_of_idx idx]
  | ReturnCallRef idx -> mk_instr "RETURN_CALL_REF" 1 [vl_of_typeuse_of_idx idx]
  | ReturnCallIndirect (idx1, idx2) -> mk_instr "RETURN_CALL_INDIRECT" 2 [vl_of_idx idx1; vl_of_typeuse_of_idx idx2]
  | Throw idx -> mk_instr "THROW" 1 [vl_of_idx idx]
  | ThrowRef  -> mk_instr0 "THROW_REF"
  | TryTable (bt, catches, instrs) ->
    mk_instr "TRY_TABLE" 3 [
      vl_of_blocktype bt;
      vl_of_list' vl_of_catch catches;
      vl_of_list vl_of_instr instrs
    ]
  | Load    (idx, loadop )         -> mk_instr "LOAD"        4 (vl_of_loadop   idx loadop)
  | Store   (idx, storeop)         -> mk_instr "STORE"       4 (vl_of_storeop  idx storeop)
  | VecLoad (idx, vloadop)         -> mk_instr "VLOAD"       4 (vl_of_vloadop  idx vloadop)
  | VecLoadLane  (idx, vlaneop, i) -> mk_instr "VLOAD_LANE"  5 (vl_of_vlaneop  idx vlaneop i)
  | VecStore     (idx, vstoreop  ) -> mk_instr "VSTORE"      3 (vl_of_vstoreop idx vstoreop)
  | VecStoreLane (idx, vlaneop, i) -> mk_instr "VSTORE_LANE" 5 (vl_of_vlaneop  idx vlaneop i)
  | MemorySize idx -> mk_instr "MEMORY.SIZE" 1 [vl_of_memidx idx]
  | MemoryGrow idx -> mk_instr "MEMORY.GROW" 1 [vl_of_memidx idx]
  | MemoryFill idx -> mk_instr "MEMORY.FILL" 1 [vl_of_memidx idx]
  | MemoryCopy (idx1, idx2) -> mk_instr "MEMORY.COPY" 2 [vl_of_memidx idx1; vl_of_memidx idx2]
  | MemoryInit (idx1, idx2) -> mk_instr "MEMORY.INIT" 2 [vl_of_memidx idx1; vl_of_idx    idx2]
  | DataDrop idx -> mk_instr "DATA.DROP" 1 [vl_of_idx idx]
  | RefAsNonNull -> mk_instr0 "REF.AS_NON_NULL"
  | RefTest rt -> mk_instr "REF.TEST" 1 [vl_of_reftype rt]
  | RefCast rt -> mk_instr "REF.CAST" 1 [vl_of_reftype rt]
  | RefEq  -> mk_instr0 "REF.EQ"
  | RefI31 -> mk_instr0 "REF.I31"
  | I31Get sx -> mk_instr "I31.GET" 1 [vl_of_sx sx]
  | StructNew (idx, Explicit) -> mk_instr "STRUCT.NEW"         1 [vl_of_idx idx]
  | StructNew (idx, Implicit) -> mk_instr "STRUCT.NEW_DEFAULT" 1 [vl_of_idx idx]
  | StructGet (idx1, idx2, sx_opt) ->
    mk_instr "STRUCT.GET" 3 [
      vl_of_opt vl_of_sx sx_opt;
      vl_of_idx idx1;
      vl_of_nat32 idx2;
    ]
  | StructSet (idx1, idx2)     -> mk_instr "STRUCT.SET"        2 [vl_of_idx idx1; vl_of_nat32 idx2]
  | ArrayNew (idx, Explicit)   -> mk_instr "ARRAY.NEW"         1 [vl_of_idx idx]
  | ArrayNew (idx, Implicit)   -> mk_instr "ARRAY.NEW_DEFAULT" 1 [vl_of_idx idx]
  | ArrayNewFixed (idx, i32)   -> mk_instr "ARRAY.NEW_FIXED"   2 [vl_of_idx idx ; vl_of_nat32 i32]
  | ArrayNewElem (idx1, idx2)  -> mk_instr "ARRAY.NEW_ELEM"    2 [vl_of_idx idx1; vl_of_idx idx2]
  | ArrayNewData (idx1, idx2)  -> mk_instr "ARRAY.NEW_DATA"    2 [vl_of_idx idx1; vl_of_idx idx2]
  | ArrayGet (idx, sx_opt)     -> mk_instr "ARRAY.GET"         2 [vl_of_opt vl_of_sx sx_opt; vl_of_idx idx]
  | ArraySet idx               -> mk_instr "ARRAY.SET"         1 [vl_of_idx idx]
  | ArrayLen                   -> mk_instr0 "ARRAY.LEN"
  | ArrayCopy (idx1, idx2)     -> mk_instr "ARRAY.COPY"        2 [vl_of_idx idx1; vl_of_idx idx2]
  | ArrayFill idx              -> mk_instr "ARRAY.FILL"        1 [vl_of_idx idx]
  | ArrayInitData (idx1, idx2) -> mk_instr "ARRAY.INIT_DATA"   2 [vl_of_idx idx1; vl_of_idx idx2]
  | ArrayInitElem (idx1, idx2) -> mk_instr "ARRAY.INIT_ELEM"   2 [vl_of_idx idx1; vl_of_idx idx2]
  | ExternConvert Internalize  -> mk_instr0 "ANY.CONVERT_EXTERN"
  | ExternConvert Externalize  -> mk_instr0 "EXTERN.CONVERT_ANY"


let vl_of_const (const: RI.Ast.const) = vl_of_list vl_of_instr const.it


(* Construct module *)

let vl_of_type (ty: RI.Ast.type_) =
  caseV [["TYPE"];[]] [vl_of_rectype ty.it]

let vl_of_local (local: RI.Ast.local) =
  let Local t = local.it in
  caseV [["LOCAL"];[]] [vl_of_valtype t]

let vl_of_func (func: RI.Ast.func) =
  let Func (idx, locals, body) = func.it in
  caseV [["FUNC"];[];[];[]] [
    vl_of_idx idx;
    vl_of_list vl_of_local locals;
    vl_of_list vl_of_instr body;
  ]

let vl_of_global (global: RI.Ast.global) =
  let Global (gt, expr) = global.it in
  caseV [["GLOBAL"];[];[]] [vl_of_globaltype gt; vl_of_const expr]

let vl_of_table (table: RI.Ast.table) =
  let Table (tt, expr) = table.it in
  caseV [["TABLE"];[];[]] [vl_of_tabletype tt; vl_of_const expr]

let vl_of_memory (memory: RI.Ast.memory) =
  let Memory mt = memory.it in
  caseV [["MEMORY"];[]] [vl_of_memorytype mt]

let vl_of_tag (tag: RI.Ast.tag) =
  let Tag tt = tag.it in
  caseV [["TAG"];[]] [vl_of_tagtype tt]

let vl_of_segmentmode (segmentmode: RI.Ast.segmentmode) (mode: [`Datamode | `Elemmode]) =
  match segmentmode.it with
  | Passive -> nullary "PASSIVE"
  | Active (index, offset) ->
    caseV [["ACTIVE"];[];[]] [vl_of_idx index; vl_of_const offset]
  | Declarative -> (match mode with
                    | `Datamode -> error no "datamode: invalid Declarative constructor"
                    | `Elemmode -> nullary "DECLARE"
                    )

let vl_of_elem (elem: RI.Ast.elem) =
  let Elem (rt, consts, mode) = elem.it in
  caseV [["ELEM"];[];[];[]] [
    vl_of_reftype rt;
    vl_of_list vl_of_const consts;
    vl_of_segmentmode mode `Elemmode;
  ]

let vl_of_data (data: RI.Ast.data) =
  let Data (bytes, mode) = data.it in
  caseV [["DATA"];[];[]] [ vl_of_bytes bytes; vl_of_segmentmode mode `Datamode ]

let vl_of_externtype = function
  | RT.ExternFuncT   (typeuse   ) -> caseV [["FUNC"  ];[]] [vl_of_typeuse    typeuse   ]
  | RT.ExternGlobalT (globaltype) -> caseV [["GLOBAL"];[]] [vl_of_globaltype globaltype]
  | RT.ExternTableT  (tabletype ) -> caseV [["TABLE" ];[]] [vl_of_tabletype  tabletype ]
  | RT.ExternMemoryT (memtype   ) -> caseV [["MEM"   ];[]] [vl_of_memorytype memtype   ]
  | RT.ExternTagT    (tagtype   ) -> caseV [["TAG"   ];[]] [vl_of_tagtype    tagtype   ]

let vl_of_import (import: RI.Ast.import)=
  let Import (module_name, item_name, xt) = import.it in
  caseV [["IMPORT"];[];[];[]] [vl_of_name module_name; vl_of_name item_name; vl_of_externtype xt]

let vl_of_externidx (xt: RI.Ast.externidx) = match xt.it with
  | FuncX   idx -> caseV [["FUNC"  ];[]] [vl_of_idx idx]
  | TableX  idx -> caseV [["TABLE" ];[]] [vl_of_idx idx]
  | MemoryX idx -> caseV [["MEM"   ];[]] [vl_of_idx idx]
  | GlobalX idx -> caseV [["GLOBAL"];[]] [vl_of_idx idx]
  | TagX    idx -> caseV [["TAG"   ];[]] [vl_of_idx idx]

let vl_of_start (start: RI.Ast.start) =
  let Start idx = start.it in
  caseV [["START"];[]] [vl_of_idx idx]

let vl_of_export (export: RI.Ast.export) =
  let Export (name, exix) = export.it in
  caseV [["EXPORT"];[];[]] [vl_of_name name; vl_of_externidx exix]


(* Wasm-3: MODULE type* import* tag* global* mem* table* func* data* elem* start? export* *)
let vl_of_module (module_: RI.Ast.module_) =
  let es = [
            vl_of_list vl_of_type module_.it.types;
            vl_of_list vl_of_import module_.it.imports;
            vl_of_list vl_of_tag module_.it.tags;
            vl_of_list vl_of_global module_.it.globals;
            vl_of_list vl_of_memory module_.it.memories;
            vl_of_list vl_of_table module_.it.tables;
            vl_of_list vl_of_func module_.it.funcs;
            vl_of_list vl_of_data module_.it.datas;
            vl_of_list vl_of_elem module_.it.elems;
            vl_of_opt  vl_of_start module_.it.start;
            vl_of_list vl_of_export module_.it.exports;
          ]
  in
  caseV [["MODULE"];[];[];[];[];[];[];[];[];[];[];[]] es



(* Destruct *)


(* Destruct data structure *)

let vl_to_opt (f: value -> 'a) : value -> 'a option = function
  | OptV ov -> Option.map f ov
  | v -> error_value "opt" v

let vl_to_list (f: value -> 'a) : value -> 'a list = function
  | ListV vs ->  List.map f (Array.to_list !vs)
  | v -> error_value "list" v

(* For `syntax list(x)`. *)
let vl_to_list' (f: value -> 'a) v : 'a list =
  match match_caseV "list" v with
  | [[];[]], [l] -> vl_to_list f l
  | _ -> error_value "list(X)" v

let vl_to_seq f s = vl_to_list f s |> List.to_seq

let vl_to_phrase (f: value -> 'a) v : 'a RI.Source.phrase = RI.Source.(f v @@ no_region)


(* Destruct minor *)

type layout = { width : int; exponent : int; mantissa : int }
let layout32 = { width = 32; exponent = 8; mantissa = 23 }
let layout64 = { width = 64; exponent = 11; mantissa = 52 }

let mask_sign layout = Z.shift_left Z.one (layout.width - 1)
let mask_mag layout = Z.pred (mask_sign layout)
let mask_mant layout = Z.(pred (shift_left one layout.mantissa))
let mask_exp layout = Z.(mask_mag layout - mask_mant layout)
let bias layout = let em1 = layout.exponent - 1 in Z.((one + one)**em1 - one)

let vl_to_z_nat num : Z.t =
  match num with
  | `Nat n -> n
  | _ -> error no ("Invalid nat: " ^ Xl.Num.to_string num)
let vl_to_z_int num : Z.t =
  match num with
  | `Int i -> i
  | _ -> error no ("Invalid int: " ^ Xl.Num.to_string num)
let z_to_intN signed unsigned z = if z < Z.zero then signed z else unsigned z

let vl_to_fmagN layout v : Z.t =
  match match_caseV "fmagN" v with
  | [["NORM"];[];[]], [m; n] ->
    Z.(shift_left (vl_to_z_int (as_num_value n) + bias layout) layout.mantissa + vl_to_z_nat (as_num_value m))
  | [["SUBNORM"];[]], [m] -> vl_to_z_nat (as_num_value m)
  | [["INF"]], [] -> mask_exp layout
  | [["NAN"];[]], [m] -> Z.(mask_exp layout + vl_to_z_nat (as_num_value m))
  | _ -> error_value "fmagN" v

let vl_to_floatN layout v : Z.t =
  match match_caseV "floatN" v with
  | [["POS"];[]], [mag] -> vl_to_fmagN layout mag
  | [["NEG"];[]], [mag] -> Z.(mask_sign layout + vl_to_fmagN layout mag)
  | _ -> error_value "floatN" v

let e64 = Z.(shift_left one 64)
let z_to_vec128 i =
  let hi, lo = Z.div_rem i e64 in
  RI.V128.I64x2.of_lanes [Z.to_int64_unsigned lo; Z.to_int64_unsigned hi]

let vl_to_int = function
  | NumV n -> vl_to_z_nat n |> Z.to_int
  | v -> error_value "int" v

let vl_to_nat8    exp : RI.I8.t   = as_num_value exp |> vl_to_z_nat |> Z.to_int |> RI.I8.of_int_u
let vl_to_int8    exp : RI.I8.t   = as_num_value exp |> vl_to_z_nat |> Z.to_int |> RI.I8.of_int_s
let vl_to_int16   exp : RI.I16.t  = as_num_value exp |> vl_to_z_nat |> Z.to_int |> RI.I16.of_int_s
let vl_to_nat32   exp : RI.I32.t  = as_num_value exp |> vl_to_z_nat |> z_to_intN Z.to_int32 Z.to_int32_unsigned
let vl_to_nat64   exp : RI.I64.t  = as_num_value exp |> vl_to_z_nat |> z_to_intN Z.to_int64 Z.to_int64_unsigned
let vl_to_vec128  exp : RI.V128.t = as_num_value exp |> vl_to_z_nat |> z_to_vec128
let vl_to_float32 exp : RI.F32.t  = vl_to_floatN layout32 exp |> Z.to_int32_unsigned |> RI.F32.of_bits
let vl_to_float64 exp : RI.F64.t  = vl_to_floatN layout64 exp |> Z.to_int64_unsigned |> RI.F64.of_bits

let vl_to_uN_32 exp : RI.I32.t = vl_to_nat32 (as_singleton_case exp)
let vl_to_uN_64 exp : RI.I64.t = vl_to_nat64 (as_singleton_case exp)

let vl_to_idx v : RI.Ast.idx = vl_to_phrase vl_to_uN_32 v
let vl_to_byte v : Char.t = as_nat_value (as_singleton_case v) |> Z.to_int |> Char.chr
let vl_to_bytes v : string = vl_to_seq vl_to_byte v |> String.of_seq
let vl_to_string = function
  | TextV str -> str
  | v -> error_value "text" v
let vl_to_name name = name |> as_singleton_case |> vl_to_string |> Utf8.decode
let vl_to_bool = function
  | BoolV b -> b
  | v -> error_value "bool" v


(* Destruct type *)


let vl_to_null : value -> RI.Types.null = function
  | OptV None -> NoNull
  | OptV _ -> Null
  | v -> error_value "null" v

let vl_to_final : value -> RI.Types.final = function
  | OptV None -> NoFinal
  | OptV _ -> Final
  | v -> error_value "final" v

let vl_to_mut : value -> RI.Types.mut = function
  | OptV None -> Cons
  | OptV _ -> Var
  | v -> error_value "mut" v

let rec vl_to_storagetype v : RI.Types.storagetype =
  match match_caseV "storagetype" v with
  | [["I8"]] , [] -> PackStorageT I8T
  | [["I16"]], [] -> PackStorageT I16T
  | _ -> ValStorageT (vl_to_valtype v)

and vl_to_fieldtype v : RI.Types.fieldtype =
  match match_caseV "fieldtype" v with
  | [[];[];[]], [mut; st] -> FieldT (vl_to_mut mut, vl_to_storagetype st)
  | _ -> error_value "fieldtype" v

and vl_to_resulttype v : RI.Types.resulttype =
  vl_to_list' vl_to_valtype v

and vl_to_comptype v : RI.Types.comptype =
  match match_caseV "comptype" v with
  | [["STRUCT"];[]], [ftl] -> StructT (vl_to_list' vl_to_fieldtype ftl)
  | [["ARRAY"];[]], [ft] -> ArrayT (vl_to_fieldtype ft)
  | [["FUNC"];["->"];[]], [rt1; rt2] -> FuncT (vl_to_resulttype rt1, vl_to_resulttype rt2)
  | _ -> error_value "comptype" v

and vl_to_subtype v : RI.Types.subtype =
  match match_caseV "subtype" v with
  | [["SUB"];[];[];[]], [fin; tul; st] ->
    SubT (vl_to_final fin, vl_to_list vl_to_typeuse tul, vl_to_comptype st)
  | _ -> error_value "subtype" v

and vl_to_rectype v : RI.Types.rectype =
  match match_caseV "rectype" v with
  | [["REC"];[]], [stl] -> RecT (vl_to_list' vl_to_subtype stl)
  | _ -> error_value "rectype" v

and vl_to_deftype v : RI.Types.deftype =
  match match_caseV "deftype" v with
  | [["_DEF"];[];[]], [rt; i32] -> DefT (vl_to_rectype rt, vl_to_nat32 i32)
  | _ -> error_value "deftype" v

and vl_to_typeuse exp : RI.Types.typeuse =
  match match_caseV "typeuse" exp with
  | [["_IDX"];[]]   , [ idx ] -> Idx (vl_to_idx idx).it
  | [["REC"];[]]    , [ n ]   -> Rec (vl_to_nat32 n)
  | [["_DEF"];[];[]], _       -> Def (vl_to_deftype exp)
  | v -> error_value "typeuse" exp

and vl_to_idx_of_typeuse exp : RI.Ast.idx =
  match match_caseV "idx_of_typeuse" exp with
  | [["_IDX"];[]], [idx] -> vl_to_idx idx
  | _ -> error_value "idx_of_typeuse" exp

and vl_to_heaptype : value -> RI.Types.heaptype = function
  | CaseV (tag, _) as v ->
    (match tag with
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
    | ([["_IDX"];[]] | [["REC"];[]] | [["_DEF"];[];[]]) -> UseHT (vl_to_typeuse v)
    | _ -> error no ("Invalid heaptype: " ^ string_of_value v)
    )
  | v -> error no ("Invalid heaptype: " ^ string_of_value v)

and vl_to_reftype v : RI.Types.reftype =
  match match_caseV "reftype" v with
  | [["REF"];[];[]], [n; ht] -> vl_to_null n, vl_to_heaptype ht
  | _ -> error_value "reftype" v

and vl_to_addrtype v : RI.Types.addrtype =
  match match_caseV "addrtype" v with
  | [["I32"]], [] -> I32AT
  | [["I64"]], [] -> I64AT
  | _ -> error_value "addrtype" v

and vl_to_numtype v : RI.Types.numtype =
  match match_caseV "numtype" v with
  | [["I32"]], [] -> I32T
  | [["I64"]], [] -> I64T
  | [["F32"]], [] -> F32T
  | [["F64"]], [] -> F64T
  | _ -> error_value "numtype" v

and vl_to_packtype v : RI.Types.packtype =
  match match_caseV "packtype" v with
  | [["I8" ]], [] -> I8T
  | [["I16"]], [] -> I16T
  | _ -> error_value "packtype" v

and vl_to_valtype v : RI.Types.valtype =
  match match_caseV "valtype" v with
  | [["I32"]], _ | [["I64"]], _ | [["F32"]], _ | [["F64"]], _ -> NumT (vl_to_numtype v)
  | [["V128"]], [] -> VecT V128T
  | [["REF"];[];[]], _ -> RefT (vl_to_reftype v)
  | [["BOT"]], [] -> BotT
  | _ -> error_value "valtype" v

let vl_to_blocktype v : RI.Ast.blocktype =
  match match_caseV "blocktype" v with
  | [["_IDX"];[]], [idx] -> VarBlockType (vl_to_idx idx)
  | [["_RESULT"];[]], [vt_opt] -> ValBlockType (vl_to_opt vl_to_valtype vt_opt)
  | _ -> error_value "blocktype" v

let vl_to_limits (default: int64) v : RI.Types.limits =
  match match_caseV "limits" v with
  | [["["];[".."];["]"]], [min; omax] ->
    { min = vl_to_uN_64 min; max = vl_to_opt vl_to_uN_64 omax }
  | _ -> error_value "limits" v

let vl_to_globaltype v : RI.Types.globaltype =
  match match_caseV "globaltype" v with
  | [[];[];[]], [mut; vt] -> GlobalT (vl_to_mut mut, vl_to_valtype vt)
  | _ -> error_value "globaltype" v

let vl_to_tabletype v : RI.Types.tabletype =
  match match_caseV "tabletype" v with
  | [[];[];[];[]], [at; limits; rt] ->
    TableT (vl_to_addrtype at, vl_to_limits default_table_max limits, vl_to_reftype rt)
  | _ -> error_value "tabletype" v

let vl_to_memorytype v : RI.Types.memorytype =
  match match_caseV "memorytype" v with
  | [[];[];["PAGE"]], [at; limits] -> MemoryT (vl_to_addrtype at, vl_to_limits default_memory_max limits)
  | _ -> error_value "memorytype" v

let vl_to_tagtype v : RI.Types.tagtype = TagT (vl_to_typeuse v)


(* Destruct operator *)

let vl_to_sx v : RI.Pack.sx =
  match match_caseV "sx" v with
  | [["S"]], [] -> RI.Pack.S
  | [["U"]], [] -> RI.Pack.U
  | _ -> error_value "sx" v

let vl_to_op f1 f2 vs : ('i32, 'i64, 'f32, 'f64) RI.Value.op =
  match vs with
  | [numtype; op] ->
    (match match_caseV "op numtype" numtype with
    | [["I32"]], [] -> RI.Value.I32 (f1 op)
    | [["I64"]], [] -> RI.Value.I64 (f1 op)
    | [["F32"]], [] -> RI.Value.F32 (f2 op)
    | [["F64"]], [] -> RI.Value.F64 (f2 op)
    | _ -> error_value "op numtype" numtype
    )
  | _ -> error_values "op" vs

let vl_to_int_unop v : RI.Ast.IntOp.unop =
  let open RI in
  let open Ast in
  match match_caseV "interger unop" v with
  | [["CLZ"]], []    -> IntOp.Clz
  | [["CTZ"]], []    -> IntOp.Ctz
  | [["POPCNT"]], [] -> IntOp.Popcnt
  | [["EXTEND"];[]], [z] when z = eight     -> IntOp.ExtendS Pack.Pack8
  | [["EXTEND"];[]], [z] when z = sixteen   -> IntOp.ExtendS Pack.Pack16
  | [["EXTEND"];[]], [z] when z = thirtytwo -> IntOp.ExtendS Pack.Pack32
  | [["EXTEND"];[]], [z] when z = sixtyfour -> IntOp.ExtendS Pack.Pack64
  | _ -> error_value "integer unop" v
let vl_to_float_unop v : RI.Ast.FloatOp.unop =
  let open RI in
  let open Ast in
  match match_caseV "float unop" v with
  | [["NEG"]]    , [] -> FloatOp.Neg
  | [["ABS"]]    , [] -> FloatOp.Abs
  | [["CEIL"]]   , [] -> FloatOp.Ceil
  | [["FLOOR"]]  , [] -> FloatOp.Floor
  | [["TRUNC"]]  , [] -> FloatOp.Trunc
  | [["NEAREST"]], [] -> FloatOp.Nearest
  | [["SQRT"]]   , [] -> FloatOp.Sqrt
  | _ -> error_value "float unop" v
let vl_to_unop : value list -> RI.Ast.unop = vl_to_op vl_to_int_unop vl_to_float_unop


let vl_to_int_binop v : RI.Ast.IntOp.binop =
  let open RI in
  let open Ast in
  match match_caseV "integer binop" v with
  | [["ADD"]], [] -> IntOp.Add
  | [["SUB"]], [] -> IntOp.Sub
  | [["MUL"]], [] -> IntOp.Mul
  | [["DIV"];[]], [sx] -> IntOp.Div (vl_to_sx sx)
  | [["REM"];[]], [sx] -> IntOp.Rem (vl_to_sx sx)
  | [["AND"]], [] -> IntOp.And
  | [["OR" ]], [] -> IntOp.Or
  | [["XOR"]], [] -> IntOp.Xor
  | [["SHL"]], [] -> IntOp.Shl
  | [["SHR"];[]], [sx] -> IntOp.Shr (vl_to_sx sx)
  | [["ROTL"]], [] -> IntOp.Rotl
  | [["ROTR"]], [] -> IntOp.Rotr
  | _ -> error_value "integer binop" v
let vl_to_float_binop v : RI.Ast.FloatOp.binop =
  let open RI in
  let open Ast in
  match match_caseV "float binop" v with
  | [["ADD"]], [] -> FloatOp.Add
  | [["SUB"]], [] -> FloatOp.Sub
  | [["MUL"]], [] -> FloatOp.Mul
  | [["DIV"]], [] -> FloatOp.Div
  | [["MIN"]], [] -> FloatOp.Min
  | [["MAX"]], [] -> FloatOp.Max
  | [["COPYSIGN"]], [] -> FloatOp.CopySign
  | _ -> error_value "float binop" v
let vl_to_binop : value list -> RI.Ast.binop = vl_to_op vl_to_int_binop vl_to_float_binop

let vl_to_int_testop v : RI.Ast.IntOp.testop =
  match match_caseV "testop" v with
  | [["EQZ"]], [] -> RI.Ast.IntOp.Eqz
  | _ -> error_value "integer testop" v
let vl_to_testop vs : RI.Ast.testop =
  match vs with
  | [numtype; op] ->
    (match match_caseV "testop numtype" numtype with
    | [["I32"]], [] -> RI.Value.I32 (vl_to_int_testop op)
    | [["I64"]], [] -> RI.Value.I64 (vl_to_int_testop op)
    | _ -> error_value "testop numtype" numtype
    )
  | _ -> error_values "testop" vs

let vl_to_int_relop v : RI.Ast.IntOp.relop =
  let open RI.Ast in
  match match_caseV "integer relop" v with
  | [["EQ"]], [] -> IntOp.Eq
  | [["NE"]], [] -> IntOp.Ne
  | [["LT"];[]], [sx] -> IntOp.Lt (vl_to_sx sx)
  | [["GT"];[]], [sx] -> IntOp.Gt (vl_to_sx sx)
  | [["LE"];[]], [sx] -> IntOp.Le (vl_to_sx sx)
  | [["GE"];[]], [sx] -> IntOp.Ge (vl_to_sx sx)
  | _ -> error_value "integer relop" v
let vl_to_float_relop v : RI.Ast.FloatOp.relop =
  let open RI.Ast in
  match match_caseV "float relop" v with
  | [["EQ"]], [] -> FloatOp.Eq
  | [["NE"]], [] -> FloatOp.Ne
  | [["LT"]], [] -> FloatOp.Lt
  | [["GT"]], [] -> FloatOp.Gt
  | [["LE"]], [] -> FloatOp.Le
  | [["GE"]], [] -> FloatOp.Ge
  | _ -> error_value "float relop" v
let vl_to_relop : value list -> RI.Ast.relop = vl_to_op vl_to_int_relop vl_to_float_relop

let vl_to_int_cvtop vs : RI.Ast.IntOp.cvtop =
  let open RI.Ast in
  match vs with
  | [_; numtype2; op] ->
    (match match_caseV "integer cvtop numtype2" numtype2, match_caseV "integer cvtop op" op with
    | ([["I32"]], []), ([["EXTEND"];[]], [sx]) -> IntOp.ExtendI32 (vl_to_sx sx)
    | ([["I64"]], []), ([["WRAP"]], []) -> IntOp.WrapI64
    | ([["F32"]], []), ([["TRUNC"];[]], [sx]) -> IntOp.TruncF32 (vl_to_sx sx)
    | ([["F64"]], []), ([["TRUNC"];[]], [sx]) -> IntOp.TruncF64 (vl_to_sx sx)
    | ([["F32"]], []), ([["TRUNC_SAT"];[]], [sx]) -> IntOp.TruncSatF32 (vl_to_sx sx)
    | ([["F64"]], []), ([["TRUNC_SAT"];[]], [sx]) -> IntOp.TruncSatF64 (vl_to_sx sx)
    | _, ([["REINTERPRET"]], []) -> IntOp.ReinterpretFloat
    | _ -> error_values "integer cvtop [numtype2; op]" [numtype2; op]
    )
  | _ -> error_values "integer cvtop" vs
let vl_to_float_cvtop vs : RI.Ast.FloatOp.cvtop =
  let open RI.Ast in
  match vs with
  | [_; numtype2; op] ->
    (match match_caseV "float cvtop numtype2" numtype2, match_caseV "float cvtop op" op with
    | ([["I32"]], []), ([["CONVERT"];[]], [sx]) -> FloatOp.ConvertI32 (vl_to_sx sx)
    | ([["I64"]], []), ([["CONVERT"];[]], [sx]) -> FloatOp.ConvertI64 (vl_to_sx sx)
    | ([["F32"]], []), ([["PROMOTE"]], []) -> FloatOp.PromoteF32
    | ([["F64"]], []), ([["DEMOTE"]], []) -> FloatOp.DemoteF64
    | _, ([["REINTERPRET"]], []) -> FloatOp.ReinterpretInt
    | l -> error_values "float cvtop [numtype2; op]" [numtype2; op]
    )
  | _ -> error_values "float cvtop" vs
let vl_to_cvtop vs : RI.Ast.cvtop =
  match vs with
  | numtype :: _ ->
    (match match_caseV "cvtop" numtype with
    | [["I32"]], [] -> I32 (vl_to_int_cvtop vs)
    | [["I64"]], [] -> I64 (vl_to_int_cvtop vs)
    | [["F32"]], [] -> F32 (vl_to_float_cvtop vs)
    | [["F64"]], [] -> F64 (vl_to_float_cvtop vs)
    | _ -> error_value "cvtop" numtype
    )
  | _ ->  error_values "cvtop" vs


(* Vector operator *)

let vl_to_vop f1 f2 = function
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I8" ]], []); z ]); vop ] when z = sixteen -> RI.Value.V128 (RI.V128.I8x16 (f1 vop))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); z ]); vop ] when z = eight   -> RI.Value.V128 (RI.V128.I16x8 (f1 vop))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I32"]], []); z ]); vop ] when z = four    -> RI.Value.V128 (RI.V128.I32x4 (f1 vop))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I64"]], []); z ]); vop ] when z = two     -> RI.Value.V128 (RI.V128.I64x2 (f1 vop))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["F32"]], []); z ]); vop ] when z = four    -> RI.Value.V128 (RI.V128.F32x4 (f2 vop))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["F64"]], []); z ]); vop ] when z = two     -> RI.Value.V128 (RI.V128.F64x2 (f2 vop))
  | l -> error_values "vop" l

let vl_to_vvop f = function
  | [ CaseV ([["V128"]], []); vop ] -> RI.Value.V128 (f vop)
  | l -> error_values "vvop" l

let vl_to_int_vtestop : value -> RI.Ast.V128Op.itestop = function
  | CaseV ([["ALL_TRUE"]], []) -> RI.Ast.V128Op.AllTrue
  | v -> error_value "integer vtestop" v

let vl_to_float_vtestop : value -> RI.Ast.void = function
  | v -> error_value "float vtestop" v

let vl_to_vtestop : value list -> RI.Ast.vtestop =
  vl_to_vop vl_to_int_vtestop vl_to_float_vtestop

let vl_to_vbitmaskop : value list -> RI.Ast.vbitmaskop = function
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I8" ]], []); z ]) ] when z = sixteen -> V128 (RI.V128.I8x16 (RI.Ast.V128Op.Bitmask))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); z ]) ] when z = eight   -> V128 (RI.V128.I16x8 (RI.Ast.V128Op.Bitmask))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I32"]], []); z ]) ] when z = four    -> V128 (RI.V128.I32x4 (RI.Ast.V128Op.Bitmask))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I64"]], []); z ]) ] when z = two     -> V128 (RI.V128.I64x2 (RI.Ast.V128Op.Bitmask))
  | l -> error_values "vbitmaskop" l

let vl_to_int_vrelop : value -> RI.Ast.V128Op.irelop = function
  | CaseV ([["EQ"]   ], [  ]) -> RI.Ast.V128Op.Eq
  | CaseV ([["NE"]   ], [  ]) -> RI.Ast.V128Op.Ne
  | CaseV ([["LT"];[]], [sx]) -> RI.Ast.V128Op.Lt (vl_to_sx sx)
  | CaseV ([["LE"];[]], [sx]) -> RI.Ast.V128Op.Le (vl_to_sx sx)
  | CaseV ([["GT"];[]], [sx]) -> RI.Ast.V128Op.Gt (vl_to_sx sx)
  | CaseV ([["GE"];[]], [sx]) -> RI.Ast.V128Op.Ge (vl_to_sx sx)
  | v -> error_value "integer vrelop" v

let vl_to_float_vrelop : value -> RI.Ast.V128Op.frelop = function
  | CaseV ([["EQ"]], []) -> RI.Ast.V128Op.Eq
  | CaseV ([["NE"]], []) -> RI.Ast.V128Op.Ne
  | CaseV ([["LT"]], []) -> RI.Ast.V128Op.Lt
  | CaseV ([["LE"]], []) -> RI.Ast.V128Op.Le
  | CaseV ([["GT"]], []) -> RI.Ast.V128Op.Gt
  | CaseV ([["GE"]], []) -> RI.Ast.V128Op.Ge
  | v -> error_value "float vrelop" v

let vl_to_vrelop : value list -> RI.Ast.vrelop =
  vl_to_vop vl_to_int_vrelop vl_to_float_vrelop

let vl_to_int_vunop : value -> RI.Ast.V128Op.iunop = function
  | CaseV ([["ABS"   ]], []) -> RI.Ast.V128Op.Abs
  | CaseV ([["NEG"   ]], []) -> RI.Ast.V128Op.Neg
  | CaseV ([["POPCNT"]], []) -> RI.Ast.V128Op.Popcnt
  | v -> error_value "integer vunop" v

let vl_to_float_vunop : value -> RI.Ast.V128Op.funop = function
  | CaseV ([["ABS"    ]], []) -> RI.Ast.V128Op.Abs
  | CaseV ([["NEG"    ]], []) -> RI.Ast.V128Op.Neg
  | CaseV ([["SQRT"   ]], []) -> RI.Ast.V128Op.Sqrt
  | CaseV ([["CEIL"   ]], []) -> RI.Ast.V128Op.Ceil
  | CaseV ([["FLOOR"  ]], []) -> RI.Ast.V128Op.Floor
  | CaseV ([["TRUNC"  ]], []) -> RI.Ast.V128Op.Trunc
  | CaseV ([["NEAREST"]], []) -> RI.Ast.V128Op.Nearest
  | v -> error_value "float vunop" v

let vl_to_vunop : value list -> RI.Ast.vunop =
  vl_to_vop vl_to_int_vunop vl_to_float_vunop

let vl_to_int_vbinop : value -> RI.Ast.V128Op.ibinop = function
  | CaseV ([["ADD"             ]   ], [  ]     ) -> RI.Ast.V128Op.Add
  | CaseV ([["SUB"             ]   ], [  ]     ) -> RI.Ast.V128Op.Sub
  | CaseV ([["MUL"             ]   ], [  ]     ) -> RI.Ast.V128Op.Mul
  | CaseV ([["MIN"             ];[]], [sx]     ) -> RI.Ast.V128Op.Min (vl_to_sx sx)
  | CaseV ([["MAX"             ];[]], [sx]     ) -> RI.Ast.V128Op.Max (vl_to_sx sx)
  | CaseV ([["AVGRU"           ]   ], [(* U *)]) -> RI.Ast.V128Op.AvgrU
  | CaseV ([["ADD_SAT"         ];[]], [sx]     ) -> RI.Ast.V128Op.AddSat (vl_to_sx sx)
  | CaseV ([["SUB_SAT"         ];[]], [sx]     ) -> RI.Ast.V128Op.SubSat (vl_to_sx sx)
  | CaseV ([["Q15MULR_SATS"    ]   ], [(* S *)]) -> RI.Ast.V128Op.Q15MulRSatS
  | CaseV ([["RELAXED_Q15MULRS"]   ], [(* S *)]) -> RI.Ast.V128Op.RelaxedQ15MulRS
  | v -> error_value "integer vbinop" v

let vl_to_float_vbinop : value -> RI.Ast.V128Op.fbinop = function
  | CaseV ([["ADD"        ]], []) -> RI.Ast.V128Op.Add
  | CaseV ([["SUB"        ]], []) -> RI.Ast.V128Op.Sub
  | CaseV ([["MUL"        ]], []) -> RI.Ast.V128Op.Mul
  | CaseV ([["DIV"        ]], []) -> RI.Ast.V128Op.Div
  | CaseV ([["MIN"        ]], []) -> RI.Ast.V128Op.Min
  | CaseV ([["MAX"        ]], []) -> RI.Ast.V128Op.Max
  | CaseV ([["PMIN"       ]], []) -> RI.Ast.V128Op.Pmin
  | CaseV ([["PMAX"       ]], []) -> RI.Ast.V128Op.Pmax
  | CaseV ([["RELAXED_MIN"]], []) -> RI.Ast.V128Op.RelaxedMin
  | CaseV ([["RELAXED_MAX"]], []) -> RI.Ast.V128Op.RelaxedMax
  | v -> error_value "float vbinop" v

let vl_to_vbinop : value list -> RI.Ast.vbinop = vl_to_vop vl_to_int_vbinop vl_to_float_vbinop

let vl_to_int_vternop : value -> RI.Ast.V128Op.iternop = function
  | CaseV ([["RELAXED_LANESELECT"]], []) -> RI.Ast.V128Op.RelaxedLaneselect
  | v -> error_value "integer vternop" v

let vl_to_float_vternop : value -> RI.Ast.V128Op.fternop = function
  | CaseV ([["RELAXED_MADD" ]], []) -> RI.Ast.V128Op.RelaxedMadd
  | CaseV ([["RELAXED_NMADD"]], []) -> RI.Ast.V128Op.RelaxedNmadd
  | v -> error_value "float vternop" v

let vl_to_vternop : value list -> RI.Ast.vternop = vl_to_vop vl_to_int_vternop vl_to_float_vternop

let vl_to_half : value -> RI.Ast.V128Op.half = function
  | CaseV ([["HIGH"]], []) -> RI.Ast.V128Op.High
  | CaseV ([["LOW" ]], []) -> RI.Ast.V128Op.Low
  | v -> error_value "half" v

let vl_to_special_vbinop = function
  | CaseV ([["VSWIZZLOP"];[];[]], [ CaseV ([[];["X"];[]], [ CaseV ([["I8"]], []); z ]); op ]) as v when z = sixteen ->
    (match op with
    | CaseV ([["SWIZZLE"        ]], []) -> RI.Value.V128 (RI.V128.I8x16 (RI.Ast.V128Op.Swizzle       ))
    | CaseV ([["RELAXED_SWIZZLE"]], []) -> RI.Value.V128 (RI.V128.I8x16 (RI.Ast.V128Op.RelaxedSwizzle))
    | _ ->  error_value "special vbinop" v
    )
  | CaseV ([["VSHUFFLE" ];[];[]   ], [ CaseV ([[];["X"];[]], [ CaseV ([["I8" ]], []); z ]); l ]) when z = sixteen -> RI.Value.V128 (RI.V128.I8x16 (RI.Ast.V128Op.Shuffle (vl_to_list vl_to_nat8 l)))
  | CaseV ([["VNARROW"  ];[];[];[]], [ CaseV ([[];["X"];[]], [ CaseV ([["I8" ]], []); z1 ]); CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); z2 ]); CaseV ([["S"]], []) ]) when z1 = sixteen && z2 = eight -> V128 (RI.V128.I8x16 RI.Ast.V128Op.(Narrow S))
  | CaseV ([["VNARROW"  ];[];[];[]], [ CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); z1 ]); CaseV ([[];["X"];[]], [ CaseV ([["I32"]], []); z2 ]); CaseV ([["S"]], []) ]) when z1 = eight   && z2 = four  -> V128 (RI.V128.I16x8 RI.Ast.V128Op.(Narrow S))
  | CaseV ([["VNARROW"  ];[];[];[]], [ CaseV ([[];["X"];[]], [ CaseV ([["I8" ]], []); z1 ]); CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); z2 ]); CaseV ([["U"]], []) ]) when z1 = sixteen && z2 = eight -> V128 (RI.V128.I8x16 RI.Ast.V128Op.(Narrow U))
  | CaseV ([["VNARROW"  ];[];[];[]], [ CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); z1 ]); CaseV ([[];["X"];[]], [ CaseV ([["I32"]], []); z2 ]); CaseV ([["U"]], []) ]) when z1 = eight   && z2 = four  -> V128 (RI.V128.I16x8 RI.Ast.V128Op.(Narrow U))
  | CaseV ([["VEXTBINOP"];[];[];[]], [ c1; c2; ext ]) as v ->
    let ext' =
      match ext with
      | CaseV ([["EXTMUL"      ];[];[]], [half; sx]) -> RI.Ast.V128Op.(ExtMul (vl_to_half half, vl_to_sx sx))
      | CaseV ([["DOTS"        ]      ], [(* S *) ]) -> RI.Ast.V128Op.DotS
      | CaseV ([["RELAXED_DOTS"]      ], [(* S *) ]) -> RI.Ast.V128Op.RelaxedDot
      | _ -> error_value "special vextbinop operator" ext
    in
    (match c1, c2 with
    | CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); z1 ]), CaseV ([[];["X"];[]], [ CaseV ([["I8" ]], []); z2 ]) when z1 = eight && z2 = sixteen -> V128 (RI.V128.I16x8 ext')
    | CaseV ([[];["X"];[]], [ CaseV ([["I32"]], []); z1 ]), CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); z2 ]) when z1 = four  && z2 = eight   -> V128 (RI.V128.I32x4 ext')
    | CaseV ([[];["X"];[]], [ CaseV ([["I64"]], []); z1 ]), CaseV ([[];["X"];[]], [ CaseV ([["I32"]], []); z2 ]) when z1 = two   && z2 = four    -> V128 (RI.V128.I64x2 ext')
    | _   -> error_value "special vextbinop shapes" v)
  | v -> error_value "special vbinop" v

let vl_to_special_vternop = function
  | CaseV ([["VEXTTERNOP"];[];[];[]], [ c1; c2; ext ]) as v ->
    let ext' =
      match ext with
      | CaseV ([["RELAXED_DOT_ADDS"]], [(* S *)]) -> RI.Ast.V128Op.RelaxedDotAddS
      | _ -> error_value "special vextternop operator" ext
    in
    (match c1, c2 with
    | CaseV ([[];["X"];[]], [ CaseV ([["I32"]], []); z1 ]),
      CaseV ([[];["X"];[]], [ CaseV ([["I8" ]], []); z2 ])
      when z1 = four && z2 = sixteen -> RI.Value.V128 (RI.V128.I32x4 ext')
    | _   -> error_value "special vextternop shapes" v)
  | v -> error_value "special vternop" v

let vl_to_int_vcvtop : value list -> RI.Ast.V128Op.icvtop = function
  | [ _sh; CaseV ([["EXTEND"   ];[];[]], [ half; sx ] ) ] -> RI.Ast.V128Op.Extend (vl_to_half half, vl_to_sx sx)
  | [  sh; CaseV ([["TRUNC_SAT"];[];[]], [ sx; _zero ] ) ] as l ->
    (match sh with
    | CaseV ([[];["X"];[]], [ CaseV ([["F32"]], []); z ]) when z = four -> RI.Ast.V128Op.TruncSatF32x4     (vl_to_sx sx)
    | CaseV ([[];["X"];[]], [ CaseV ([["F64"]], []); z ]) when z = two  -> RI.Ast.V128Op.TruncSatZeroF64x2 (vl_to_sx sx)
    | _ -> error_values "integer vcvtop" l
    )
  | [ sh; CaseV ([["RELAXED_TRUNC"];[];[]], [ sx; _zero ] ) ] as l ->
    (match sh with
    | CaseV ([[];["X"];[]], [ CaseV ([["F32"]], []); z ]) when z = four -> RI.Ast.V128Op.RelaxedTruncF32x4     (vl_to_sx sx)
    | CaseV ([[];["X"];[]], [ CaseV ([["F64"]], []); z ]) when z = two  -> RI.Ast.V128Op.RelaxedTruncZeroF64x2 (vl_to_sx sx)
    | _ -> error_values "integer vcvtop" l
    )
  | l -> error_values "integer vcvtop" l

let vl_to_float_vcvtop : value list -> RI.Ast.V128Op.fcvtop = function
  | [ _sh; CaseV ([["DEMOTE" ];[]   ], [ _zero     ]) ] -> RI.Ast.V128Op.DemoteZeroF64x2
  | [ _sh; CaseV ([["CONVERT"];[];[]], [ _half; sx ]) ] -> RI.Ast.V128Op.ConvertI32x4 (vl_to_sx sx)
  | [ _sh; CaseV ([["PROMOTE"]      ], [           ]) ] -> RI.Ast.V128Op.PromoteLowF32x4
  | l -> error_values "float vcvtop" l

let vl_to_vcvtop : value list -> RI.Ast.vcvtop = function
  | CaseV ([[];["X"];[]], [ CaseV ([["I8" ]], []); z ]) :: op when z = sixteen -> V128 (RI.V128.I8x16 (vl_to_int_vcvtop   op))
  | CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); z ]) :: op when z = eight   -> V128 (RI.V128.I16x8 (vl_to_int_vcvtop   op))
  | CaseV ([[];["X"];[]], [ CaseV ([["I32"]], []); z ]) :: op when z = four    -> V128 (RI.V128.I32x4 (vl_to_int_vcvtop   op))
  | CaseV ([[];["X"];[]], [ CaseV ([["I64"]], []); z ]) :: op when z = two     -> V128 (RI.V128.I64x2 (vl_to_int_vcvtop   op))
  | CaseV ([[];["X"];[]], [ CaseV ([["F32"]], []); z ]) :: op when z = four    -> V128 (RI.V128.F32x4 (vl_to_float_vcvtop op))
  | CaseV ([[];["X"];[]], [ CaseV ([["F64"]], []); z ]) :: op when z = two     -> V128 (RI.V128.F64x2 (vl_to_float_vcvtop op))
  | l -> error_values "vcvtop" l

let vl_to_special_vcvtop = function
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); z1 ])
    ; CaseV ([[];["X"];[]], [ CaseV ([["I8" ]], []); z2 ])
    ; CaseV ([["EXTADD_PAIRWISE"]], [ sx ]) ] when z1 = eight && z2 = sixteen ->
    RI.Value.V128 (RI.V128.I16x8 (RI.Ast.V128Op.ExtAddPairwise (vl_to_sx sx)))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I32"]], []); z1 ])
    ; CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); z2 ])
    ; CaseV ([["EXTADD_PAIRWISE"]], [ sx ]) ] when z1 = four  && z2 = eight   ->
    RI.Value.V128 (RI.V128.I32x4 (RI.Ast.V128Op.ExtAddPairwise (vl_to_sx sx)))
  | l -> error_values "special vcvtop" l

let vl_to_int_vshiftop : value -> RI.Ast.V128Op.ishiftop = function
  | CaseV ([["SHL"]   ], []  ) -> RI.Ast.V128Op.Shl
  | CaseV ([["SHR"];[]], [sx]) -> RI.Ast.V128Op.Shr (vl_to_sx sx)
  | v -> error_value "integer vshiftop" v
let vl_to_float_vshiftop : value -> RI.Ast.void = error_value "float vshiftop"
let vl_to_vshiftop : value list -> RI.Ast.vshiftop = vl_to_vop vl_to_int_vshiftop vl_to_float_vshiftop

let vl_to_vvtestop' : value -> RI.Ast.V128Op.vtestop = function
  | CaseV ([["ANY_TRUE"]], []) -> RI.Ast.V128Op.AnyTrue
  | v -> error_value "vvtestop" v
let vl_to_vvtestop : value list -> RI.Ast.vvtestop = vl_to_vvop vl_to_vvtestop'

let vl_to_vvunop' : value -> RI.Ast.V128Op.vunop = function
  | CaseV ([["NOT"]], []) -> RI.Ast.V128Op.Not
  | v -> error_value "vvunop" v
let vl_to_vvunop : value list -> RI.Ast.vvunop = vl_to_vvop vl_to_vvunop'

let vl_to_vvbinop' = function
  | CaseV ([["AND"   ]], []) -> RI.Ast.V128Op.And
  | CaseV ([["OR"    ]], []) -> RI.Ast.V128Op.Or
  | CaseV ([["XOR"   ]], []) -> RI.Ast.V128Op.Xor
  | CaseV ([["ANDNOT"]], []) -> RI.Ast.V128Op.AndNot
  | v -> error_value "vvbinop" v
let vl_to_vvbinop : value list -> RI.Ast.vvbinop = vl_to_vvop vl_to_vvbinop'

let vl_to_vvternop' : value -> RI.Ast.V128Op.vternop = function
  | CaseV ([["BITSELECT"]], []) -> RI.Ast.V128Op.Bitselect
  | v -> error_value "vvternop" v
let vl_to_vvternop : value list -> RI.Ast.vvternop = vl_to_vvop vl_to_vvternop'

let vl_to_vsplatop : value list -> RI.Ast.vsplatop = function
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I8" ]], []); z ]) ] when z = sixteen -> V128 (RI.V128.I8x16 Splat)
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); z ]) ] when z = eight   -> V128 (RI.V128.I16x8 Splat)
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I32"]], []); z ]) ] when z = four    -> V128 (RI.V128.I32x4 Splat)
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I64"]], []); z ]) ] when z = two     -> V128 (RI.V128.I64x2 Splat)
  | [ CaseV ([[];["X"];[]], [ CaseV ([["F32"]], []); z ]) ] when z = four    -> V128 (RI.V128.F32x4 Splat)
  | [ CaseV ([[];["X"];[]], [ CaseV ([["F64"]], []); z ]) ] when z = two     -> V128 (RI.V128.F64x2 Splat)
  | vs -> error_values "vsplatop" vs

let vl_to_vextractop : value list -> RI.Ast.vextractop = function
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I8" ]], []); z ]); OptV (Some sx); n ] when z = sixteen -> V128 (RI.V128.I8x16 (Extract (vl_to_nat8 n, vl_to_sx sx)))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); z ]); OptV (Some sx); n ] when z = eight   -> V128 (RI.V128.I16x8 (Extract (vl_to_nat8 n, vl_to_sx sx)))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I32"]], []); z ]); OptV None     ; n ] when z = four    -> V128 (RI.V128.I32x4 (Extract (vl_to_nat8 n, ())))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I64"]], []); z ]); OptV None     ; n ] when z = two     -> V128 (RI.V128.I64x2 (Extract (vl_to_nat8 n, ())))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["F32"]], []); z ]); OptV None     ; n ] when z = four    -> V128 (RI.V128.F32x4 (Extract (vl_to_nat8 n, ())))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["F64"]], []); z ]); OptV None     ; n ] when z = two     -> V128 (RI.V128.F64x2 (Extract (vl_to_nat8 n, ())))
  | vs -> error_values "vextractop" vs

let vl_to_vreplaceop : value list -> RI.Ast.vreplaceop = function
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I8" ]], []); z ]); n ] when z = sixteen -> V128 (RI.V128.I8x16 (Replace (vl_to_nat8 n)))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); z ]); n ] when z = eight   -> V128 (RI.V128.I16x8 (Replace (vl_to_nat8 n)))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I32"]], []); z ]); n ] when z = four    -> V128 (RI.V128.I32x4 (Replace (vl_to_nat8 n)))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["I64"]], []); z ]); n ] when z = two     -> V128 (RI.V128.I64x2 (Replace (vl_to_nat8 n)))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["F32"]], []); z ]); n ] when z = four    -> V128 (RI.V128.F32x4 (Replace (vl_to_nat8 n)))
  | [ CaseV ([[];["X"];[]], [ CaseV ([["F64"]], []); z ]); n ] when z = two     -> V128 (RI.V128.F64x2 (Replace (vl_to_nat8 n)))
  | vs -> error_values "vreplaceop" vs


let vl_to_packsize : value -> RI.Pack.packsize = function
  | z when z = eight     -> RI.Pack.Pack8
  | z when z = sixteen   -> RI.Pack.Pack16
  | z when z = thirtytwo -> RI.Pack.Pack32
  | z when z = sixtyfour -> RI.Pack.Pack64
  | v -> error_value "packsize" v

let vl_to_memop (f: value -> 'p) vs : RI.Ast.idx * (RI.Types.numtype, 'p) RI.Ast.memop =
  match vs with
  | [nt; p; idx; str] ->
    vl_to_idx idx,
    {
      ty = vl_to_numtype nt;
      align  = as_str_field "ALIGN"  str |> as_singleton_case |> as_nat_value |> Z.to_int;
      offset = as_str_field "OFFSET" str |> vl_to_uN_64;
      pack = f p;
    }
  | _ -> error_values "memop" vs


let vl_to_packsize_sx v : RI.Pack.packsize * RI.Pack.sx =
  match match_caseV "packsize sx" v with
  | [[];["_"];[]], [sz; sx] -> vl_to_packsize sz, vl_to_sx sx
  | _ -> error_value "packsize sx" v

let vl_to_loadop  : value list -> RI.Ast.idx * RI.Ast.loadop  =
  vl_to_opt vl_to_packsize_sx |> vl_to_memop

let vl_to_storeop : value list -> RI.Ast.idx * RI.Ast.storeop =
  vl_to_opt (fun p -> as_singleton_case p |> vl_to_packsize) |> vl_to_memop

let vl_to_vmemop' (f: value -> 'p) : value list -> (RI.Types.vectype, 'p) RI.Ast.memop = function
  | [ StrV str ] ->
    {
      ty = V128T;
      align  = Record.find "ALIGN"  str |> as_singleton_case |> vl_to_int;
      offset = Record.find "OFFSET" str |> vl_to_uN_64;
      pack = f (natV Z.zero);
    }
  | [ p; StrV str ] ->
    {
      ty = V128T;
      align  = Record.find "ALIGN"  str |> as_singleton_case |> vl_to_int;
      offset = Record.find "OFFSET" str |> vl_to_uN_64;
      pack = f p;
    }
  | v -> error_values "vmemop" v

let vl_to_vmemop (f: value -> 'p) (g: value list -> value * (value list)) (vl: value list) :
                 RI.Ast.idx * (RI.Types.vectype, 'p) RI.Ast.memop =
  let idx, vl' = g vl in vl_to_idx idx, vl_to_vmemop' f vl'

let vl_to_packshape = function
  | z1, NumV (`Nat z2) when z1 = eight     && z2 = Z.of_int 8 -> RI.Pack.Pack8x8
  | z1, NumV (`Nat z2) when z1 = sixteen   && z2 = Z.of_int 4 -> RI.Pack.Pack16x4
  | z1, NumV (`Nat z2) when z1 = thirtytwo && z2 = Z.of_int 2 -> RI.Pack.Pack32x2
  | z1, z2 -> error_value "packshape" (TupV [z1; z2])

let vl_to_vloadop': value -> RI.Pack.packsize * RI.Pack.vext = function
  | CaseV ([["SHAPE"];["X"];["_"];[]], [ v1; v2; ext ]) ->
    let packshape = vl_to_packshape (v1, v2) in
    (
      RI.Pack.Pack64,
      RI.Pack.ExtLane (packshape, vl_to_sx ext)
    )
  | CaseV ([["SPLAT"];[]], [ packsize ]) -> vl_to_packsize packsize, RI.Pack.ExtSplat
  | CaseV ([["ZERO" ];[]], [ packsize ]) -> vl_to_packsize packsize, RI.Pack.ExtZero
  | v -> error_value "vloadop'" v

let vl_to_vloadop: value list -> RI.Ast.idx * RI.Ast.vloadop = function
  | CaseV ([["V128"]], []) :: vl ->
    let split vl =
      match vl with
      | memop :: idx :: vl' -> idx, memop :: vl'
      | _ -> error_values "vloadop" vl
    in
    vl_to_vmemop (vl_to_opt vl_to_vloadop') split vl
  | vs -> error_value "vloadop" (TupV vs)

let vl_to_vstoreop = function
  | CaseV ([["V128"]], []) :: vl ->
    let split = Util.Lib.List.split_hd in
    vl_to_vmemop (Fun.const ()) split vl
  | vs -> error_value "vstoreop" (TupV vs)

let vl_to_vlaneop: value list -> RI.Ast.idx * RI.Ast.vlaneop * RI.I8.t = function
  | CaseV ([["V128"]], []) :: vl ->
    let h, t = Util.Lib.List.split_last vl in
    let split vl =
      match vl with
      | ps :: idx :: vl' -> idx, ps :: vl'
      | _ -> error_values "vlaneop" vl
    in
    let idx, op = vl_to_vmemop vl_to_packsize split h in
    idx, op, vl_to_nat8 t
  | vs -> error_value "vlaneop" (TupV vs)


(* Destruct expressions *)

let vl_to_catch' v : RI.Ast.catch' =
  match match_caseV "catch" v with
  | [["CATCH"];[];[]]     , [idx1; idx2] -> Catch       (vl_to_idx idx1, vl_to_idx idx2)
  | [["CATCH_REF"];[];[]] , [idx1; idx2] -> CatchRef    (vl_to_idx idx1, vl_to_idx idx2)
  | [["CATCH_ALL"];[]]    , [idx]        -> CatchAll    (vl_to_idx idx)
  | [["CATCH_ALL_REF"];[]], [idx]        -> CatchAllRef (vl_to_idx idx)
  | _ -> error_value "catch" v
let vl_to_catch v : RI.Ast.catch = vl_to_phrase vl_to_catch' v

let vl_to_num v : RI.Value.num =
  match match_caseV "num" v with
  | [["CONST"];[];[]], [numtype; num_] ->
    (match match_caseV "numtype" numtype with
    | [["I32"]], [] -> I32 (vl_to_uN_32   num_)
    | [["I64"]], [] -> I64 (vl_to_uN_64   num_)
    | [["F32"]], [] -> F32 (vl_to_float32 num_)
    | [["F64"]], [] -> F64 (vl_to_float64 num_)
    | v -> error_value "numtype" numtype
    )
  | _ -> error_value "num" v

let vl_to_vec v : RI.Value.vec =
  let _, [vectype; vec_] = match_caseV "vec" v in
  match match_caseV "vectype" vectype with
  | [["V128"]], [] -> V128 (vl_to_vec128 (as_singleton_case vec_))
  | _ -> error_value "vectype" vectype


let rec vl_to_instr v : RI.Ast.instr = vl_to_phrase vl_to_instr' v
and vl_to_instr' v : RI.Ast.instr' =
  match match_caseV "instr" v with
  (* wasm values *)
  | [["CONST"];[];[]], _ -> Const (vl_to_phrase vl_to_num v)
  | [["VCONST"];[];[]], _ -> VecConst (vl_to_phrase vl_to_vec v)
  | [["REF.NULL"];[]], [ht] -> RefNull (vl_to_heaptype ht)
  (* wasm instructions *)
  | [["UNREACHABLE"]], [] -> Unreachable
  | [["NOP"]], [] -> Nop
  | [["DROP"]], [] -> Drop
  | [["UNOP"];[];[]], op -> Unary (vl_to_unop op)
  | [["BINOP"];[];[]], op -> Binary (vl_to_binop op)
  | [["TESTOP"];[];[]], op -> Test (vl_to_testop op)
  | [["RELOP"];[];[]], op -> Compare (vl_to_relop op)
  | [["CVTOP"];[];[];[]], op -> Convert (vl_to_cvtop op)
  | [["VTESTOP"];[];[]], vop -> VecTest (vl_to_vtestop vop)
  | [["VRELOP"];[];[]], vop -> VecCompare (vl_to_vrelop vop)
  | [["VUNOP"];[];[]], vop -> VecUnary (vl_to_vunop vop)
  | [["VBINOP"];[];[]], vop -> VecBinary (vl_to_vbinop vop)
  | [["VTERNOP"];[];[]], vop -> VecTernary (vl_to_vternop vop)
  | [[("VSWIZZLOP" | "VSHUFFLE")];[];[]], _ -> VecBinary (vl_to_special_vbinop v)
  | [[("VNARROW" | "VEXTBINOP")];[];[];[]], _ -> VecBinary (vl_to_special_vbinop v)
  | [["VEXTTERNOP"];[];[];[]], _ -> VecTernary (vl_to_special_vternop v)
  | [["VCVTOP"];[];[];[]], vop -> VecConvert (vl_to_vcvtop vop)
  | [["VEXTUNOP"];[];[];[]], vop -> VecConvert (vl_to_special_vcvtop vop)
  | [["VSHIFTOP"];[];[]], vop -> VecShift (vl_to_vshiftop vop)
  | [["VBITMASK"];[]], vop -> VecBitmask (vl_to_vbitmaskop vop)
  | [["VVTESTOP"];[];[]], vop -> VecTestBits (vl_to_vvtestop vop)
  | [["VVUNOP"];[];[]], vop -> VecUnaryBits (vl_to_vvunop vop)
  | [["VVBINOP"];[];[]], vop -> VecBinaryBits (vl_to_vvbinop vop)
  | [["VVTERNOP"];[];[]], vop -> VecTernaryBits (vl_to_vvternop vop)
  | [["VSPLAT"];[]], vop -> VecSplat (vl_to_vsplatop vop)
  | [["VEXTRACT_LANE"];[];[];[]], vop -> VecExtract (vl_to_vextractop vop)
  | [["VREPLACE_LANE"];[];[]], vop -> VecReplace (vl_to_vreplaceop vop)
  | [["REF.IS_NULL"]], [] -> RefIsNull
  | [["REF.FUNC"];[]], [idx] -> RefFunc (vl_to_idx idx)
  | [["SELECT"];[]], [vtl_opt] -> Select (vl_to_opt (vl_to_list vl_to_valtype) vtl_opt)
  | [["LOCAL.GET"];[]], [idx] -> LocalGet (vl_to_idx idx)
  | [["LOCAL.SET"];[]], [idx] -> LocalSet (vl_to_idx idx)
  | [["LOCAL.TEE"];[]], [idx] -> LocalTee (vl_to_idx idx)
  | [["GLOBAL.GET"];[]], [idx] -> GlobalGet (vl_to_idx idx)
  | [["GLOBAL.SET"];[]], [idx] -> GlobalSet (vl_to_idx idx)
  | [["TABLE.GET"];[]], [idx] -> TableGet (vl_to_idx idx)
  | [["TABLE.SET"];[]], [idx] -> TableSet (vl_to_idx idx)
  | [["TABLE.SIZE"];[]], [idx] -> TableSize (vl_to_idx idx)
  | [["TABLE.GROW"];[]], [idx] -> TableGrow (vl_to_idx idx)
  | [["TABLE.FILL"];[]], [idx] -> TableFill (vl_to_idx idx)
  | [["TABLE.COPY"];[];[]], [idx1; idx2] -> TableCopy (vl_to_idx idx1, vl_to_idx idx2)
  | [["TABLE.INIT"];[];[]], [idx1; idx2] -> TableInit (vl_to_idx idx1, vl_to_idx idx2)
  | [["ELEM.DROP"];[]], [idx] -> ElemDrop (vl_to_idx idx)
  | [["BLOCK"];[];[]], [bt; instrs] ->
    Block (vl_to_blocktype bt, vl_to_list vl_to_instr instrs)
  | [["LOOP"];[];[]], [bt; instrs] ->
    Loop (vl_to_blocktype bt, vl_to_list vl_to_instr instrs)
  | [["IF"];[];["ELSE"];[]], [bt; instrs1; instrs2] ->
    If (vl_to_blocktype bt, vl_to_list vl_to_instr instrs1, vl_to_list vl_to_instr instrs2)
  | [["BR"];[]], [idx] -> Br (vl_to_idx idx)
  | [["BR_IF"];[]], [idx] -> BrIf (vl_to_idx idx)
  | [["BR_TABLE"];[];[]], [idxs; idx] -> BrTable (vl_to_list vl_to_idx idxs, vl_to_idx idx)
  | [["BR_ON_NULL"];[]], [idx] -> BrOnNull (vl_to_idx idx)
  | [["BR_ON_NON_NULL"];[]], [idx] -> BrOnNonNull (vl_to_idx idx)
  | [["BR_ON_CAST"];[];[];[]], [idx; rt1; rt2] -> BrOnCast (vl_to_idx idx, vl_to_reftype rt1, vl_to_reftype rt2)
  | [["BR_ON_CAST_FAIL"];[];[];[]], [idx; rt1; rt2] -> BrOnCastFail (vl_to_idx idx, vl_to_reftype rt1, vl_to_reftype rt2)
  | [["RETURN"]], [] -> Return
  | [["CALL"];[]], [idx] -> Call (vl_to_idx idx)
  | [["CALL_REF"];[]], [typeuse] -> CallRef (vl_to_idx_of_typeuse typeuse)
  | [["CALL_INDIRECT"];[];[]], [idx1; typeuse2] -> CallIndirect (vl_to_idx idx1, vl_to_idx_of_typeuse typeuse2)
  | [["RETURN_CALL"];[]], [idx] -> ReturnCall (vl_to_idx idx)
  | [["RETURN_CALL_REF"];[]], [typeuse] -> ReturnCallRef (vl_to_idx_of_typeuse typeuse)
  | [["RETURN_CALL_INDIRECT"];[];[]], [idx1; typeuse2] -> ReturnCallIndirect (vl_to_idx idx1, vl_to_idx_of_typeuse typeuse2)
  | [["THROW"];[]], [idx] -> Throw (vl_to_idx idx)
  | [["THROW_REF"]], [] -> ThrowRef
  | [["TRY_TABLE"];[];[];[]], [bt; catches; instrs] ->
    TryTable (vl_to_blocktype bt, vl_to_list' vl_to_catch catches, vl_to_list vl_to_instr instrs)
  | [["LOAD"];[];[];[];[]], loadop -> let idx, op = vl_to_loadop loadop in Load (idx, op)
  | [["STORE"];[];[];[];[]], storeop -> let idx, op = vl_to_storeop storeop in Store (idx, op)
  | [["VLOAD"];[];[];[];[]], vloadop -> let idx, op = vl_to_vloadop vloadop in VecLoad (idx, op)
  | [["VLOAD_LANE"];[];[];[];[];[]], vlaneop ->
    let idx, op, i = vl_to_vlaneop vlaneop in VecLoadLane (idx, op, i)
  | [["VSTORE"];[];[];[]], vstoreop -> let idx, op = vl_to_vstoreop vstoreop in VecStore (idx, op)
  | [["VSTORE_LANE"];[];[];[];[];[]], vlaneop ->
    let idx, op, i = vl_to_vlaneop vlaneop in VecStoreLane (idx, op, i)
  | [["MEMORY.SIZE"];[]], [idx] -> MemorySize (vl_to_idx idx)
  | [["MEMORY.GROW"];[]], [idx] -> MemoryGrow (vl_to_idx idx)
  | [["MEMORY.FILL"];[]], [idx] -> MemoryFill (vl_to_idx idx)
  | [["MEMORY.COPY"];[];[]], [idx1; idx2] -> MemoryCopy (vl_to_idx idx1, vl_to_idx idx2)
  | [["MEMORY.INIT"];[];[]], [idx1; idx2] -> MemoryInit (vl_to_idx idx1, vl_to_idx idx2)
  | [["DATA.DROP"];[]], [idx] -> DataDrop (vl_to_idx idx)
  | [["REF.AS_NON_NULL"]], [] -> RefAsNonNull
  | [["REF.TEST"];[]], [rt] -> RefTest (vl_to_reftype rt)
  | [["REF.CAST"];[]], [rt] -> RefCast (vl_to_reftype rt)
  | [["REF.EQ"]], [] -> RefEq
  | [["REF.I31"]], [] -> RefI31
  | [["I31.GET"];[]], [sx] -> I31Get (vl_to_sx sx)
  | [["STRUCT.NEW"];[]], [idx] -> StructNew (vl_to_idx idx, Explicit)
  | [["STRUCT.NEW_DEFAULT"];[]], [idx] -> StructNew (vl_to_idx idx, Implicit)
  | [["STRUCT.GET"];[];[];[]], [sx_opt; idx1; idx2] ->
    StructGet (vl_to_idx idx1, vl_to_uN_32 idx2, vl_to_opt vl_to_sx sx_opt)
  | [["STRUCT.SET"];[];[]], [idx1; idx2] -> StructSet (vl_to_idx idx1, vl_to_uN_32 idx2)
  | [["ARRAY.NEW"];[]], [idx] -> ArrayNew (vl_to_idx idx, Explicit)
  | [["ARRAY.NEW_DEFAULT"];[]], [idx] -> ArrayNew (vl_to_idx idx, Implicit)
  | [["ARRAY.NEW_FIXED"];[];[]], [idx; i32] -> ArrayNewFixed (vl_to_idx idx, vl_to_uN_32 i32)
  | [["ARRAY.NEW_ELEM"];[];[]], [idx1; idx2] -> ArrayNewElem (vl_to_idx idx1, vl_to_idx idx2)
  | [["ARRAY.NEW_DATA"];[];[]], [idx1; idx2] -> ArrayNewData (vl_to_idx idx1, vl_to_idx idx2)
  | [["ARRAY.GET"];[];[]], [sx_opt; idx] -> ArrayGet (vl_to_idx idx, vl_to_opt vl_to_sx sx_opt)
  | [["ARRAY.SET"];[]], [idx] -> ArraySet (vl_to_idx idx)
  | [["ARRAY.LEN"]], [] -> ArrayLen
  | [["ARRAY.COPY"];[];[]], [idx1; idx2] -> ArrayCopy (vl_to_idx idx1, vl_to_idx idx2)
  | [["ARRAY.FILL"];[]], [idx] -> ArrayFill (vl_to_idx idx)
  | [["ARRAY.INIT_DATA"];[];[]], [idx1; idx2] -> ArrayInitData (vl_to_idx idx1, vl_to_idx idx2)
  | [["ARRAY.INIT_ELEM"];[];[]], [idx1; idx2] -> ArrayInitElem (vl_to_idx idx1, vl_to_idx idx2)
  | [["ANY.CONVERT_EXTERN"]], [] -> ExternConvert Internalize
  | [["EXTERN.CONVERT_ANY"]], [] -> ExternConvert Externalize
  | _ -> error_value "instruction" v

let vl_to_const : value -> RI.Ast.const = vl_to_list vl_to_instr |> vl_to_phrase


(* Deconstruct module *)

let vl_to_type v : RI.Ast.type_ =
  match match_caseV "type" v with
  | [["TYPE"];[]], [rt] -> vl_to_phrase vl_to_rectype rt
  | _ -> error_value "type" v

let vl_to_local' v : RI.Ast.local' =
  match match_caseV "local" v with
  | [["LOCAL"];[]], [vt] -> Local (vl_to_valtype vt)
  | _ -> error_value "local" v
let vl_to_local v : RI.Ast.local = vl_to_phrase vl_to_local' v

let vl_to_func' v : RI.Ast.func' =
  match match_caseV "func" v with
  | [["FUNC"];[];[];[]], [idx; locals; instrs] ->
    Func (vl_to_idx idx, vl_to_list vl_to_local locals, vl_to_list vl_to_instr instrs)
  | _ -> error_value "func" v
let vl_to_func v : RI.Ast.func = vl_to_phrase vl_to_func' v

let vl_to_global' v : RI.Ast.global' =
  match match_caseV "global" v with
  | [["GLOBAL"];[];[]], [gt; const] ->
    Global (vl_to_globaltype gt, vl_to_const const)
  | _ -> error_value "global" v
let vl_to_global : value -> RI.Ast.global = vl_to_phrase vl_to_global'

let vl_to_table' v : RI.Ast.table' =
  match match_caseV "table" v with
  | [["TABLE"];[];[]], [tt; const] ->
    Table (vl_to_tabletype tt, vl_to_const const)
  | _ -> error_value "table" v
let vl_to_table : value -> RI.Ast.table = vl_to_phrase vl_to_table'

let vl_to_memory' v : RI.Ast.memory' =
  match match_caseV "memory" v with
  | [["MEMORY"];[]], [mt] -> Memory (vl_to_memorytype mt)
  | _ -> error_value "memory" v
let vl_to_memory : value -> RI.Ast.memory = vl_to_phrase vl_to_memory'

let vl_to_tag' v : RI.Ast.tag' =
  match match_caseV "tag" v with
  | [["TAG"];[]], [tt] -> Tag (vl_to_tagtype tt)
  | _ -> error_value "tag" v
let vl_to_tag : value -> RI.Ast.tag = vl_to_phrase vl_to_tag'

let vl_to_segmentmode' v : RI.Ast.segmentmode' =
  match match_caseV "segmentmode" v with
  | [["PASSIVE"]], [] -> Passive
  | [["ACTIVE"];[];[]], [idx; const] -> Active (vl_to_idx idx, vl_to_const const)
  | [["DECLARE"]], [] -> Declarative
  | _ -> error_value "segmentmode" v
let vl_to_segmentmode : value -> RI.Ast.segmentmode = vl_to_phrase vl_to_segmentmode'

let vl_to_elem' v : RI.Ast.elem' =
  match match_caseV "elem" v with
  | [["ELEM"];[];[];[]], [rt; consts; mode] ->
    Elem (vl_to_reftype rt, vl_to_list vl_to_const consts, vl_to_segmentmode mode)
  | _ -> error_value "elem" v
let vl_to_elem : value -> RI.Ast.elem = vl_to_phrase vl_to_elem'

let vl_to_data' v : RI.Ast.data' =
  match match_caseV "data" v with
  | [["DATA"];[];[]], [bytes; mode] ->
    Data (vl_to_bytes bytes, vl_to_segmentmode mode)
  | _ -> error_value "data" v
let vl_to_data : value -> RI.Ast.data = vl_to_phrase vl_to_data'

let vl_to_externtype v : RI.Types.externtype =
  match match_caseV "externtype" v with
  | [["FUNC"]  ;[]], [typeuse]    -> ExternFuncT   (vl_to_typeuse    typeuse   )
  | [["GLOBAL"];[]], [globaltype] -> ExternGlobalT (vl_to_globaltype globaltype)
  | [["TABLE"] ;[]], [tabletype]  -> ExternTableT  (vl_to_tabletype  tabletype )
  | [["MEM"]   ;[]], [memtype]    -> ExternMemoryT (vl_to_memorytype memtype   )
  | [["TAG"]   ;[]], [tagtype]    -> ExternTagT    (vl_to_tagtype    tagtype   )
  | _ -> error_value "externtype" v

let vl_to_import' v : RI.Ast.import' =
  match match_caseV "import" v with
  | [["IMPORT"];[];[];[]], [module_name; item_name; xt] ->
    RI.Ast.Import (vl_to_name module_name, vl_to_name item_name, vl_to_externtype xt)
  | _ -> error_value "import" v
let vl_to_import : value -> RI.Ast.import = vl_to_phrase vl_to_import'

let vl_to_externidx' v : RI.Ast.externidx' =
  match match_caseV "externidx" v with
  | [["FUNC"]  ;[]], [idx] -> FuncX   (vl_to_idx idx)
  | [["TABLE"] ;[]], [idx] -> TableX  (vl_to_idx idx)
  | [["MEM"]   ;[]], [idx] -> MemoryX (vl_to_idx idx)
  | [["GLOBAL"];[]], [idx] -> GlobalX (vl_to_idx idx)
  | [["TAG"]   ;[]], [idx] -> TagX    (vl_to_idx idx)
  | _ -> error_value "externidx" v
let vl_to_externidx : value -> RI.Ast.externidx = vl_to_phrase vl_to_externidx'

let vl_to_start' v : RI.Ast.start' =
  match match_caseV "start" v with
  | [["START"];[]], [idx] -> Start (vl_to_idx idx)
  | _ -> error_value "start" v
let vl_to_start : value -> RI.Ast.start = vl_to_phrase vl_to_start'

let vl_to_export' v : RI.Ast.export' =
  match match_caseV "export" v with
  | [["EXPORT"];[];[]], [name; xx] -> Export (vl_to_name name, vl_to_externidx xx)
  | _ -> error_value "export" v
let vl_to_export : value -> RI.Ast.export = vl_to_phrase vl_to_export'

let vl_to_module' v : RI.Ast.module_' =
  match match_caseV "module" v with
  | [["MODULE"];[];[];[];[];[];[];[];[];[];[];[]], [
      types; imports; tags; globals; memories; tables; funcs; datas; elems; start; exports
    ] ->
    {
      types    = vl_to_list vl_to_type   types   ;
      imports  = vl_to_list vl_to_import imports ;
      tags     = vl_to_list vl_to_tag    tags    ;
      globals  = vl_to_list vl_to_global globals ;
      memories = vl_to_list vl_to_memory memories;
      tables   = vl_to_list vl_to_table  tables  ;
      funcs    = vl_to_list vl_to_func   funcs   ;
      datas    = vl_to_list vl_to_data   datas   ;
      elems    = vl_to_list vl_to_elem   elems   ;
      start    = vl_to_opt  vl_to_start  start   ;
      exports  = vl_to_list vl_to_export exports ;
    }
  | _ -> error_value "module" v
let vl_to_module : value -> RI.Ast.module_ = vl_to_phrase vl_to_module'


(* Destruct value *)

let rec vl_to_field v : RI.Aggr.field =
  match match_caseV "field" v with
  | [["PACK"];[];[]], [pt; c] -> RI.Aggr.PackField (vl_to_packtype pt, ref (as_nat_value c |> Z.to_int))
  | _ -> RI.Aggr.ValField (ref (vl_to_value v))

and vl_to_array v : RI.Aggr.array =
  if has_str_field "TYPE" v && has_str_field "FIELDS" v then
    RI.Aggr.Array (
      vl_to_deftype (as_str_field "TYPE" v),
      vl_to_list vl_to_field (as_str_field "FIELDS" v)
    )
  else
    error_value "array" v

and vl_to_struct v : RI.Aggr.struct_ =
  if has_str_field "TYPE" v && has_str_field "FIELDS" v then
    RI.Aggr.Struct (
      vl_to_deftype (as_str_field "TYPE" v),
      vl_to_list vl_to_field (as_str_field "FIELDS" v)
    )
  else
    error_value "struct" v

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

and vl_to_funcinst v : RI.Instance.funcinst =
  if has_str_field "TYPE" v && has_str_field "MODULE" v && has_str_field "CODE" v then
    RI.Func.AstFunc (
      vl_to_deftype (as_str_field "TYPE" v),
      Reference_interpreter.Lib.Promise.make (), (* TODO: Fulfill the promise with module instance *)
      vl_to_func (as_str_field "CODE" v)
    )
  else
    error_value "funcinst" v

and vl_to_ref v : RI.Value.ref_ =
  let open RI in
  let open Value in
  match match_caseV "ref" v with
  | [["REF.NULL"];[]], [ht] -> NullRef (vl_to_heaptype ht)
  | [["REF.I31_NUM"];[]], [i] -> RI.I31.I31Ref (as_nat_value i |> Z.to_int)
  | [["REF.STRUCT_ADDR"];[]], [addr] ->
    let struct_insts = State_v.Store.access "STRUCTS" in
    let struct_ = addr |> as_nat_value |> nth_of_list struct_insts |> vl_to_struct in
    Aggr.StructRef struct_
  | [["REF.ARRAY_ADDR"];[]], [addr] ->
    let arr_insts = State_v.Store.access "ARRAYS" in
    let arr = addr |> as_nat_value |> nth_of_list arr_insts |> vl_to_array in
    Aggr.ArrayRef arr
  | [["REF.FUNC_ADDR"];[]], [addr] ->
    let func_insts = State_v.Store.access "FUNCS" in
    let func = addr |> as_nat_value |> nth_of_list func_insts |> vl_to_funcinst in
    Instance.FuncRef func
  | [["REF.HOST_ADDR"];[]], [i32] -> RI.Script.HostRef (vl_to_nat32 i32)
  | [["REF.EXTERN"];[]], [r] -> Extern.ExternRef (vl_to_ref r)
  | _ -> error_value "ref" v

and vl_to_value v : RI.Value.value =
  match match_caseV "val" v with
  | [["CONST" ];[];[]], _ -> RI.Value.Num (vl_to_num v)
  | [["VCONST"];[];[]], _ -> RI.Value.Vec (vl_to_vec v)
  | [[ref_con];[]], _ when String.starts_with ~prefix:"REF." ref_con ->
    RI.Value.Ref (vl_to_ref v)
  | _ -> error_value "val" v
