module RI = Reference_interpreter
open RI.Embed

module Engine : Engine = struct
  type moduleinst = RI.Instance.moduleinst
  type taginst    = RI.Instance.taginst
  type globalinst = RI.Instance.globalinst
  type memoryinst = RI.Instance.memoryinst
  type tableinst  = RI.Instance.tableinst
  type funcinst   = RI.Instance.funcinst

  type externinst =
    | ExternTag of taginst
    | ExternGlobal of globalinst
    | ExternMemory of memoryinst
    | ExternTable of tableinst
    | ExternFunc of funcinst

  type error = RI.Source.region * string
  type 'a return =
    | Return of 'a
    | Exn of RI.Source.region * taginst * value list
    | Trap of error
    | Exhaustion of error
  let undefined = Obj.magic ""

  let validate m =
    try Ok (RI.Valid.check_module m) with
    | RI.Valid.Invalid (at, msg) -> Error (at, msg)

  let validate_with_custom (m, cs) =
    try Ok (RI.Valid.check_module_with_custom (m, cs)) with
    | RI.Valid.Invalid (at, msg) -> Error (at, msg)

  let instantiate :
    module_ -> externinst list -> (moduleinst return, error) result = undefined

  let module_export : moduleinst -> RI.Ast.name -> externinst option = undefined

  let tag_type : taginst -> RI.Types.tagtype = undefined

  let global_type : globalinst -> RI.Types.globaltype = undefined
  let global_get : globalinst -> value             = undefined
  let global_set : globalinst -> value -> unit     = undefined

  let memory_type : memoryinst -> RI.Types.memorytype               = undefined
  let memory_size : memoryinst -> int64                             = undefined
  let memory_grow : memoryinst -> int64 -> unit option              = undefined
  let memory_load_byte : memoryinst -> int64 -> int option          = undefined
  let memory_store_byte : memoryinst -> int64 -> int -> unit option = undefined

  let table_type : tableinst -> RI.Types.tabletype           = undefined
  let table_size : tableinst -> int64                        = undefined
  let table_grow : tableinst -> int64 -> ref_ -> unit option = undefined
  let table_get : tableinst -> int64 -> ref_ option          = undefined
  let table_set : tableinst -> int64 -> ref_ -> unit option  = undefined

  let func_type : funcinst -> RI.Types.deftype                = undefined
  let func_call : funcinst -> value list -> value list return = undefined

end

include RI.Runner.Make(Engine)




