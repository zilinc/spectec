open Il.Ast
open Def
open Util.Source


let rec dl2il (dl: dl_def list) : script =
  List.map (function
  | TypeDef { it = (id, ps, insts); at; _ } -> TypD (id, ps, insts) $ at
  | FuncDef { it = (id, osubid, ps, t, cls, _); at; _ } ->
    let id' = id.it ^ (match osubid with | None -> "" | Some subid -> "/" ^ subid.it) $ id.at in
    let cls' = List.map snd cls in
    DecD (id', ps, t, cls') $ at
  | RecDef ds as d -> RecD (dl2il ds) $ (dl_loc d)
  ) dl
