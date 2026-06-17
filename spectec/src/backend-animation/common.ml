let step_relids = ["Step"; "Step_pure"; "Step_read"]

module Map = Map.Make(String)

let step_table : (string * string) Map.t ref =
  let step_pure_table = [
    "NOP"                     ;
    "UNREACHABLE"             ;
    "DROP"                    ;
    "SELECT"                  ;
    "IF"                      ;
    (* "BR"                      ; *)
    "BR_IF"                   ;
    "BR_TABLE"                ;
    "BR_ON_NULL"              ;
    "BR_ON_NON_NULL"          ;
    "CALL_INDIRECT"           ;
    (* "RETURN"                  ; *)
    "RETURN_CALL_INDIRECT"    ;
    "UNOP"                    ;
    "BINOP"                   ;
    "TESTOP"                  ;
    "RELOP"                   ;
    "CVTOP"                   ;
    "REF.I31"                 ;
    "REF.IS_NULL"             ;
    "REF.AS_NON_NULL"         ;
    "REF.EQ"                  ;
    "I31.GET"                 ;
    "ARRAY.NEW"               ;
    "EXTERN.CONVERT_ANY"      ;
    "ANY.CONVERT_EXTERN"      ;
    "VVUNOP"                  ;
    "VVBINOP"                 ;
    "VVTERNOP"                ;
    "VVTESTOP"                ;
    "VUNOP"                   ;
    "VBINOP"                  ;
    "VTERNOP"                 ;
    "VTESTOP"                 ;
    "VRELOP"                  ;
    "VSHIFTOP"                ;
    "VBITMASK"                ;
    "VSWIZZLOP"               ;
    "VSHUFFLE"                ;
    "VSPLAT"                  ;
    "VEXTRACT_LANE"           ;
    "VREPLACE_LANE"           ;
    "VEXTUNOP"                ;
    "VEXTBINOP"               ;
    "VEXTTERNOP"              ;
    "VNARROW"                 ;
    "VCVTOP"                  ;
    "LOCAL.TEE"               ;
  ] |> List.map (fun op -> op, ("Step_pure", String.lowercase_ascii op))
  in
  let step_read_table = [
    "BLOCK"                   ;
    "LOOP"                    ;
    "BR_ON_CAST"              ;
    "BR_ON_CAST_FAIL"         ;
    "CALL"                    ;
    "RETURN_CALL"             ;
    (* "RETURN_CALL_REF"         ; *)
    "THROW_REF"               ;
    "TRY_TABLE"               ;
    "REF.NULL"                ;
    "REF.FUNC"                ;
    "REF.TEST"                ;
    "REF.CAST"                ;
    "STRUCT.NEW_DEFAULT"      ;
    "STRUCT.GET"              ;
    "ARRAY.NEW_DEFAULT"       ;
    "ARRAY.NEW_ELEM"          ;
    "ARRAY.NEW_DATA"          ;
    "ARRAY.GET"               ;
    "ARRAY.LEN"               ;
    "ARRAY.FILL"              ;
    "ARRAY.COPY"              ;
    "ARRAY.INIT_DATA"         ;
    "ARRAY.INIT_ELEM"         ;
    "LOCAL.GET"               ;
    "GLOBAL.GET"              ;
    "TABLE.GET"               ;
    "TABLE.SIZE"              ;
    "TABLE.FILL"              ;
    "TABLE.COPY"              ;
    "TABLE.INIT"              ;
    "LOAD"                    ;
    "VLOAD"                   ;
    "VLOAD_LANE"              ;
    "MEMORY.SIZE"             ;
    "MEMORY.FILL"             ;
    "MEMORY.COPY"             ;
    "MEMORY.INIT"             ;
  ] |> List.map (fun op -> op, ("Step_read", String.lowercase_ascii op))
  in
  let step_table = [
    "CALL_REF"                ;
    "THROW"                   ;
    "STRUCT.NEW"              ;
    "STRUCT.SET"              ;
    "ARRAY.NEW_FIXED"         ;
    "ARRAY.SET"               ;
    "LOCAL.SET"               ;
    "GLOBAL.SET"              ;
    "TABLE.SET"               ;
    "TABLE.GROW"              ;
    "ELEM.DROP"               ;
    "STORE"                   ;
    "VSTORE"                  ;
    "VSTORE_LANE"             ;
    "MEMORY.GROW"             ;
    "DATA.DROP"               ;
  ] |> List.map (fun op -> op, ("Step", String.lowercase_ascii op))
  in
  (* These opcode never appears in the head position. *)
  (* "CATCH"              ;*)
  (* "CATCH_REF"          ;*)
  (* "CATCH_ALL"          ;*)
  (* "CATCH_ALL_REF"      ;*)
  let table_ref =
    (step_pure_table @ step_read_table @ step_table) |> Map.of_list |> ref
  in
  table_ref
