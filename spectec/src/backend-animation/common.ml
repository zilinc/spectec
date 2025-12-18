let typ_infers = []
let typ_checks = []

let step_relids = ["Step"; "Step_pure"; "Step_read"]

let admin_instrs = ["LABEL_"; "FRAME_"; "HANDLER_"]

module Map = Map.Make(String)

let step_table : (string * string * int) Map.t ref =
  let step_pure_table = [
    ("NOP"                 , 0);
    ("UNREACHABLE"         , 0);
    ("DROP"                , 1);
    ("SELECT"              , 3);
    ("IF"                  , 1);
    ("BR"                  , 0);  (* ??? *)
    ("BR_IF"               , 1);
    ("BR_TABLE"            , 1);
    ("BR_ON_NULL"          , 1);
    ("BR_ON_NON_NULL"      , 1);
    ("CALL_INDIRECT"       , 0);
    ("RETURN"              , 0);  (* ??? *)
    ("RETURN_CALL_INDIRECT", 0);
    ("TRAP"                , -1);
    ("UNOP"                , 0);
    ("BINOP"               , 0);
    ("TESTOP"              , 0);
    ("RELOP"               , 0);
    ("CVTOP"               , 0);
    ("REF.I31"             , 0);
    ("REF.IS_NULL"         , 0);
    ("REF.AS_NON_NULL"     , 0);
    ("REF.EQ"              , 0);
    ("I31.GET"             , 0);
    ("ARRAY.NEW"           , 0);
    ("EXTERN.CONVERT_ANY"  , 0);
    ("ANY.CONVERT_EXTERN"  , 0);
    ("VVUNOP"              , 0);
    ("VVBINOP"             , 0);
    ("VVTERNOP"            , 0);
    ("VVTESTOP"            , 0);
    ("VUNOP"               , 0);
    ("VBINOP"              , 0);
    ("VTERNOP"             , 0);
    ("VTESTOP"             , 0);
    ("VRELOP"              , 0);
    ("VSHIFTOP"            , 0);
    ("VBITMASK"            , 0);
    ("VSWIZZLOP"           , 0);
    ("VSHUFFLE"            , 0);
    ("VSPLAT"              , 0);
    ("VEXTRACT_LANE"       , 0);
    ("VREPLACE_LANE"       , 0);
    ("VEXTUNOP"            , 0);
    ("VEXTBINOP"           , 0);
    ("VEXTTERNOP"          , 0);
    ("VNARROW"             , 0);
    ("VCVTOP"              , 0);
    ("LOCAL.TEE"           , 0);
  ] |> List.map (fun (op, nargs) -> op, ("Step_pure", String.lowercase_ascii op, nargs))
  in
  let step_read_table = [
    ("BLOCK"               , 0);
    ("LOOP"                , 0);
    ("BR_ON_CAST"          , 0);
    ("BR_ON_CAST_FAIL"     , 0);
    ("CALL"                , 0);
    ("RETURN_CALL"         , 0);
    ("RETURN_CALL_REF"     , 0);
    ("THROW_REF"           , 0);
    ("TRY_TABLE"           , 0);
    ("REF.NULL"            , 0);
    ("REF.FUNC"            , 0);
    ("REF.TEST"            , 0);
    ("REF.CAST"            , 0);
    ("STRUCT.NEW_DEFAULT"  , 0);
    ("STRUCT.GET"          , 0);
    ("ARRAY.NEW_DEFAULT"   , 0);
    ("ARRAY.NEW_ELEM"      , 0);
    ("ARRAY.NEW_DATA"      , 0);
    ("ARRAY.GET"           , 0);
    ("ARRAY.LEN"           , 0);
    ("ARRAY.FILL"          , 0);
    ("ARRAY.COPY"          , 0);
    ("ARRAY.INIT_DATA"     , 0);
    ("ARRAY.INIT_ELEM"     , 0);
    ("LOCAL.GET"           , 0);
    ("GLOBAL.GET"          , 0);
    ("TABLE.GET"           , 0);
    ("TABLE.SIZE"          , 0);
    ("TABLE.FILL"          , 0);
    ("TABLE.COPY"          , 0);
    ("TABLE.INIT"          , 0);
    ("LOAD"                , 0);
    ("VLOAD"               , 0);
    ("VLOAD_LANE"          , 0);
    ("MEMORY.SIZE"         , 0);
    ("MEMORY.FILL"         , 0);
    ("MEMORY.COPY"         , 0);
    ("MEMORY.INIT"         , 0);
  ] |> List.map (fun (op, nargs) -> op, ("Step_read", String.lowercase_ascii op, nargs))
  in
  let step_table = [
    ("CALL_REF"            , 0);
    ("THROW"               , 0);
    ("STRUCT.NEW"          , 0);
    ("STRUCT.SET"          , 0);
    ("ARRAY.NEW_FIXED"     , 0);
    ("ARRAY.SET"           , 0);
    ("LOCAL.SET"           , 0);
    ("GLOBAL.SET"          , 0);
    ("TABLE.SET"           , 0);
    ("TABLE.GROW"          , 0);
    ("ELEM.DROP"           , 0);
    ("STORE"               , 0);
    ("VSTORE"              , 0);
    ("VSTORE_LANE"         , 0);
    ("MEMORY.GROW"         , 0);
    ("DATA.DROP"           , 0);
  ] |> List.map (fun (op, nargs) -> op, ("Step", String.lowercase_ascii op, nargs))
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
