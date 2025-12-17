(* Writing my own because I can't find them in the Reference_interpreter module *)

open Printf
open Backend_interpreter
open Reference_interpreter

let string_of_var (v : Script.var) = "$" ^ v.it

let string_of_var_opt (v : Script.var option) = match v with 
  | Some v -> string_of_var v
  | None -> "<none>"

let string_of_literal_list (xs : Script.literal list) =
  sprintf "[%d literal(s)]" (List.length xs)

let string_of_result_list (xs : Script.result list) =
  sprintf "[%d result(s)]" (List.length xs)

let string_of_start_opt (string_of_start : Ast.start option) =
  match string_of_start with
  | None -> "<none>"
  | Some _ -> "<some>"

let string_of_final = function
  | Types.NoFinal -> "no final"
  | Types.Final   -> "final"

let string_of_null = function
  | Types.Null    -> "null"
  | Types.NoNull -> "no null"

let string_of_heaptype = function
  | _ -> "heaptype"

let rec string_of_valtype vt = match vt with 
  | Types.RefT (null, ht) -> sprintf "null: %s;\n heaptype: %s" (string_of_null null) (string_of_heaptype ht)
  | Types.NumT nt -> "numtype val"
  | Types.VecT _  -> "V128_valtype"
  | Types.BotT    -> "BOT_valtype"

and string_of_storagetype = function
  | Types.ValStorageT  vt -> begin match vt with 
    | Types.NumT nt         -> "numtype_storage"
    | Types.VecT _          -> "V128_storagetype"
    | Types.RefT (null, ht) -> "REF_storagetype (string_of_null null, string_of_heaptype ht)"
    | Types.BotT            -> "BOT_storagetype"
    end
  | Types.PackStorageT pt -> begin match pt with 
    | Types.I8T  -> "I8_storagetype"
    | Types.I16T -> "I16_storagetype"
    end

and string_of_resulttype rt = String.concat "; " (List.map string_of_valtype rt)

and string_of_fieldtype = function
  | Types.FieldT (mut, st) -> "fieldtype"

and string_of_typeuse = function
  | Types.Idx idx -> "IDX typeuse " ^ Int32.to_string idx
  | Types.Rec n   -> "REC typeuse " ^ Int32.to_string n
  | Types.Def (DefT (rt, n))  -> "DEF typeuse " ^ Int32.to_string n

and string_of_comptype _ = "comptype"
and string_of_subtype = function
  | Types.SubT (fin, tul, st) -> sprintf "final: %s; typeuses: [%s]; comp: %s" (string_of_final fin) (String.concat ", " (List.map string_of_typeuse tul)) (string_of_comptype st)

let string_of_rectype (rt : Types.rectype) = match rt with 
  | Types.RecT stl -> 
    let st_strs = List.map (fun st -> string_of_subtype st) stl in
    sprintf "RecT([%s])" (String.concat "; " st_strs)

let string_of_type_ (ty : Ast.type_) = string_of_rectype ty.it

let string_of_mod_ (m : Ast.module_) =
  sprintf "{\n \
  \ types : [%s];
  \ tags : [%s];
  \ globals : [%s];
  \ memories : [%s];
  \ tables : [%s];
  \ funcs : [%s];
  \ datas : [%s];
  \ elems : [%s];
  \ start : %s;
  \ imports : [%s];
  \ exports : [%s];
}" 
  (String.concat "; " (List.map string_of_type_ m.it.types))
  (String.concat "; " (List.map (fun _ -> "tag") m.it.tags))
  (String.concat "; " (List.map (fun _ -> "global") m.it.globals))
  (String.concat "; " (List.map (fun _ -> "memory") m.it.memories))
  (String.concat "; " (List.map (fun _ -> "table") m.it.tables))
  (String.concat "; " (List.map (fun _ -> "func") m.it.funcs))
  (String.concat "; " (List.map (fun _ -> "data") m.it.datas))
  (String.concat "; " (List.map (fun _ -> "elem") m.it.elems))
  (Option.value ~default:"<none>" (Option.map (fun _ -> "start") m.it.start))
  (String.concat "; " (List.map (fun _ -> "import") m.it.imports))
  (String.concat "; " (List.map (fun _ -> "export") m.it.exports))


let string_of_definition (d : Script.definition) =
  match d.it with
  | Textual (mod_, _) -> sprintf "Textual(mod=%s)" (string_of_mod_ mod_)
  | Encoded _ -> "Encoded"
  | Quoted _  -> "Quoted"

let string_of_action (a : Script.action) =
  match a.it with
  | Invoke (vopt, name, lits) ->
      sprintf "Invoke(mod=%s, name=%s, args=%s)"
        (string_of_var_opt vopt) (Utf8.encode name) (string_of_literal_list lits)
  | Get (vopt, name) ->
      sprintf "Get(mod=%s, name=%s)"
        (string_of_var_opt vopt) (Utf8.encode name)

let string_of_assertion (asrt : Script.assertion) =
  match asrt.it with
  | AssertMalformed (_def, msg) ->
      sprintf "AssertMalformed(%s)" msg
  | AssertMalformedCustom (_def, msg) ->
      sprintf "AssertMalformedCustom(%s)" msg
  | AssertInvalid (_def, msg) ->
      sprintf "AssertInvalid(%s)" msg
  | AssertInvalidCustom (_def, msg) ->
      sprintf "AssertInvalidCustom(%s)" msg
  | AssertUnlinkable (vopt, msg) ->
      sprintf "AssertUnlinkable(mod=%s, %s)" (string_of_var_opt vopt) msg
  | AssertUninstantiable (vopt, msg) ->
      sprintf "AssertUninstantiable(mod=%s, %s)" (string_of_var_opt vopt) msg
  | AssertReturn (act, results) ->
      sprintf "AssertReturn(%s, %s)" (string_of_action act) (string_of_result_list results)
  | AssertException act ->
      sprintf "AssertException(%s)" (string_of_action act)
  | AssertTrap (act, msg) ->
      sprintf "AssertTrap(%s, %s)" (string_of_action act) msg
  | AssertExhaustion (act, msg) ->
      sprintf "AssertExhaustion(%s, %s)" (string_of_action act) msg

let string_of_meta (m : Script.meta) =
  match m.it with
  | Input (vopt, path) ->
      sprintf "Input(ns=%s, path=%s)" (string_of_var_opt vopt) path
  | Output (vopt, sopt) ->
      sprintf "Output(ns=%s, out=%s)" (string_of_var_opt vopt) (Option.value ~default:"<none>" sopt)
  | Script (vopt, _script) ->
      sprintf "Script(ns=%s, <commands>)" (string_of_var_opt vopt)

let string_of_command (c : Script.command) : string =
  match c.it with
  | Module (vopt, defn) ->
      sprintf "Module:\n(%s, %s)" (string_of_var_opt vopt) (string_of_definition defn)
  | Instance (as_opt, of_opt) ->
      sprintf "Instance:\n(as=%s, of=%s)" (string_of_var_opt as_opt) (string_of_var_opt of_opt)
  | Register (name, vopt) ->
      sprintf "Register(name=%s, mod=%s)" (Utf8.encode name) (string_of_var_opt vopt)
  | Action a ->
      sprintf "Action(%s)" (string_of_action a)
  | Assertion asrt ->
      sprintf "Assertion(%s)" (string_of_assertion asrt)
  | Meta m ->
      sprintf "Meta(%s)" (string_of_meta m)

let string_of_instr (instr : Ast.instr) : string = match instr.it with
  | Unreachable -> "Unreachable"
  | Nop -> "Nop"
  | Drop -> "Drop"
  | Select _ -> "Select"
  | Block _ -> "Block"
  | Loop _ -> "Loop"
  | If _ -> "If"
  | Br _ -> "Br"
  | BrIf _ -> "BrIf"
  | BrTable _ -> "BrTable"
  | BrOnNull _ -> "BrOnNull"
  | BrOnNonNull _ -> "BrOnNonNull"
  | BrOnCast _ -> "BrOnCast"
  | BrOnCastFail _ -> "BrOnCastFail"
  | Return -> "Return"
  | Call _ -> "Call"
  | CallRef _ -> "CallRef"
  | CallIndirect _ -> "CallIndirect"
  | ReturnCall _ -> "ReturnCall"
  | ReturnCallRef _ -> "ReturnCallRef"
  | ReturnCallIndirect _ -> "ReturnCallIndirect"
  | Throw _ -> "Throw"
  | ThrowRef -> "ThrowRef"
  | TryTable _ -> "TryTable"
  | LocalGet _ -> "LocalGet"
  | LocalSet _ -> "LocalSet"
  | LocalTee _ -> "LocalTee"
  | GlobalGet _ -> "GlobalGet"
  | GlobalSet _ -> "GlobalSet"
  | TableGet _ -> "TableGet"
  | TableSet _ -> "TableSet"
  | TableSize _ -> "TableSize"
  | TableGrow _ -> "TableGrow"
  | TableFill _ -> "TableFill"
  | TableCopy _ -> "TableCopy"
  | TableInit _ -> "TableInit"
  | ElemDrop _ -> "ElemDrop"
  | Load _ -> "Load"
  | Store _ -> "Store"
  | VecLoad _ -> "VecLoad"
  | VecStore _ -> "VecStore"
  | VecLoadLane _ -> "VecLoadLane"
  | VecStoreLane _ -> "VecStoreLane"
  | MemorySize _ -> "MemorySize"
  | MemoryGrow _ -> "MemoryGrow"
  | MemoryFill _ -> "MemoryFill"
  | MemoryCopy _ -> "MemoryCopy"
  | MemoryInit _ -> "MemoryInit"
  | DataDrop _ -> "DataDrop"
  | Const _ -> "Const"
  | Test _ -> "Test"
  | Compare _ -> "Compare"
  | Unary _ -> "Unary"
  | Binary _ -> "Binary"
  | Convert _ -> "Convert"
  | RefNull _ -> "RefNull"
  | RefFunc _ -> "RefFunc"
  | RefIsNull -> "RefIsNull"
  | RefAsNonNull -> "RefAsNonNull"
  | RefTest _ -> "RefTest"
  | RefCast _ -> "RefCast"
  | RefEq -> "RefEq"
  | RefI31 -> "RefI31"
  | I31Get _ -> "I31Get"
  | StructNew _ -> "StructNew"
  | StructGet _ -> "StructGet"
  | StructSet _ -> "StructSet"
  | ArrayNew _ -> "ArrayNew"
  | ArrayNewFixed _ -> "ArrayNewFixed"
  | ArrayNewData _ -> "ArrayNewData"
  | ArrayNewElem _ -> "ArrayNewElem"
  | ArrayGet _ -> "ArrayGet"
  | ArraySet _ -> "ArraySet"
  | ArrayLen -> "ArrayLen"
  | ArrayCopy _ -> "ArrayCopy"
  | ArrayFill _ -> "ArrayFill"
  | ArrayInitData _ -> "ArrayInitData"
  | ArrayInitElem _ -> "ArrayInitElem"
  | ExternConvert _ -> "ExternConvert"
  | VecConst _ -> "VecConst"
  | VecTest _ -> "VecTest"
  | VecCompare _ -> "VecCompare"
  | VecUnary _ -> "VecUnary"
  | VecBinary _ -> "VecBinary"
  | VecTernary _ -> "VecTernary"
  | VecConvert _ -> "VecConvert"
  | VecShift _ -> "VecShift"
  | VecBitmask _ -> "VecBitmask"
  | VecTestBits _ -> "VecTestBits"
  | VecUnaryBits _ -> "VecUnaryBits"
  | VecBinaryBits _ -> "VecBinaryBits"
  | VecTernaryBits _ -> "VecTernaryBits"
  | VecSplat _ -> "VecSplat"
  | VecExtract _ -> "VecExtract"
  | VecReplace _ -> "VecReplace"
