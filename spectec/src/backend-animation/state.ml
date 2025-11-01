open Il.Ast
open Il_util
module Ds = Backend_interpreter.Ds


(* Register, Modules *)

module Register = Ds.Register(struct type t = exp end)
module Modules  = Ds.Modules

(* Record *)

module Record   = Util.Record


(* Context *)

module Context = struct
  type t = Label   of exp * exp list
         | Frame   of exp * exp list
         | Handler of exp * exp list

  let context: t list ref = ref []

  let enter t : unit = context := t :: !context
  let get () : t =
    match !context with
    | [] -> raise (Failure "Context is empty.")
    | c::_ -> c
  let leave () : unit =
    match !context with
    | [] -> raise (Failure "Context is empty.")
    | c::cs -> context := cs
  let get_label () : exp * exp list =
    let c = get () in
    match c with
    | Label (n, instrs) -> n, instrs
    | _ -> raise (Failure "Not a LABEL_ context.")
  let get_frame () : exp * exp list =
    let c = get () in
    match c with
    | Frame (n, frame) -> n, frame
    | _ -> raise (Failure "Not a FRAME_ context.")
  let get_handler () : exp * exp list =
    let c = get () in
    match c with
    | Handler (n, catches) -> n, catches
    | _ -> raise (Failure "Not a HANDLER_ context.")
end


(* Store *)

module Store = struct
  type t = exp

  let store = ref Record.empty

  let init () =
    store := Record.empty
      |> Record.add "TAGS"    (listE (t_star "taginst"    ) [])
      |> Record.add "GLOBALS" (listE (t_star "globalinst" ) [])
      |> Record.add "MEMS"    (listE (t_star "meminst"    ) [])
      |> Record.add "TABLES"  (listE (t_star "tableinst"  ) [])
      |> Record.add "FUNCS"   (listE (t_star "funcinst"   ) [])
      |> Record.add "DATAS"   (listE (t_star "datainst"   ) [])
      |> Record.add "ELEMS"   (listE (t_star "eleminst"   ) [])
      |> Record.add "STRUCTS" (listE (t_star "structinst" ) [])
      |> Record.add "ARRAYS"  (listE (t_star "arrayinst"  ) [])
      |> Record.add "EXNS"    (listE (t_star "exninst"    ) [])

    (* Ds.Store.init () *)  (* NOTE: I don't think there's anything that depends on Ds. / zilinc *)


  let get () = mk_str "store" (List.map (fun (f, er) -> (f, !er)) !store)

  let access field = Record.find field !store
  let update field f = let v = access field in
                       store := Record.add field (f v) !store

  let put s =
    let tags    = find_str_field "TAGS"    s in
    let globals = find_str_field "GLOBALS" s in
    let mems    = find_str_field "MEMS"    s in
    let tables  = find_str_field "TABLES"  s in
    let funcs   = find_str_field "FUNCS"   s in
    let datas   = find_str_field "DATAS"   s in
    let elems   = find_str_field "ELEMS"   s in
    let structs = find_str_field "STRUCTS" s in
    let arrays  = find_str_field "ARRAYS"  s in
    let exns    = find_str_field "EXNS"    s in
    update "TAGS"    (Fun.const tags   );
    update "GLOBALS" (Fun.const globals);
    update "MEMS"    (Fun.const mems   );
    update "TABLES"  (Fun.const tables );
    update "FUNCS"   (Fun.const funcs  );
    update "DATAS"   (Fun.const datas  );
    update "ELEMS"   (Fun.const elems  );
    update "STRUCTS" (Fun.const structs);
    update "ARRAYS"  (Fun.const arrays );
    update "EXNS"    (Fun.const exns   );
end