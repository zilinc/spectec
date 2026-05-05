open Ast
open Types

exception Invalid of Source.region * string

type ellipses = NoEllipses | Ellipses
type infer_resulttype = ellipses * valtype list
type infer_functype = {ins : infer_resulttype; outs : infer_resulttype}
type infer_instrtype = infer_functype * idx list
type context =
{
  types : deftype list;
  tags : tagtype list;
  globals : globaltype list;
  memories : memorytype list;
  tables : tabletype list;
  funcs : deftype list;
  datas : unit list;
  elems : reftype list;
  locals : localtype list;
  labels : resulttype list;
  results : valtype list;
  refs : Free.t;
}

val check_block : context -> instr list -> instrtype -> Source.region -> unit
val check_instrs : context -> infer_resulttype -> instr list -> infer_resulttype * idx list
val check_instr : context -> instr -> infer_resulttype -> infer_instrtype
val check_module : Ast.module_ -> Types.moduletype (* raises Invalid *)
val check_module_with_custom : Ast.module_ * Custom.section list -> Types.moduletype (* raises Invalid, Custom.Check *)
