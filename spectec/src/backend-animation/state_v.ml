open Value
module Ds = Backend_interpreter.Ds


(* Register, Modules *)

module Register = Ds.Register(struct type t = value end)
module Modules  = Ds.Modules

(* Record *)

module Record   = Util.Record


(* Context *)

module Context = struct
  type t = Label   of value * value list
         | Frame   of value * value list
         | Handler of value * value list

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
  let get_label () : value * value list =
    let c = get () in
    match c with
    | Label (n, instrs) -> n, instrs
    | _ -> raise (Failure "Not a LABEL_ context.")
  let get_frame () : value * value list =
    let c = get () in
    match c with
    | Frame (n, frame) -> n, frame
    | _ -> raise (Failure "Not a FRAME_ context.")
  let get_handler () : value * value list =
    let c = get () in
    match c with
    | Handler (n, catches) -> n, catches
    | _ -> raise (Failure "Not a HANDLER_ context.")
end


(* Store *)

module Store = struct
  type t = value

  let store = ref Record.empty

  let init () =
    store := Record.empty
      |> Record.add "TAGS"    (listV [||])
      |> Record.add "GLOBALS" (listV [||])
      |> Record.add "MEMS"    (listV [||])
      |> Record.add "TABLES"  (listV [||])
      |> Record.add "FUNCS"   (listV [||])
      |> Record.add "DATAS"   (listV [||])
      |> Record.add "ELEMS"   (listV [||])
      |> Record.add "STRUCTS" (listV [||])
      |> Record.add "ARRAYS"  (listV [||])
      |> Record.add "EXNS"    (listV [||])

    (* Ds.Store.init () *)  (* NOTE: I don't think there's anything that depends on Ds. / zilinc *)


  let get () = strV (List.map (fun (f, er) -> (f, !er)) !store)

  let access field = Record.find field !store
  let update field f = let v = access field in
                       store := Record.add field (f v) !store

  let put s =
    let tags    = as_str_field "TAGS"    s in
    let globals = as_str_field "GLOBALS" s in
    let mems    = as_str_field "MEMS"    s in
    let tables  = as_str_field "TABLES"  s in
    let funcs   = as_str_field "FUNCS"   s in
    let datas   = as_str_field "DATAS"   s in
    let elems   = as_str_field "ELEMS"   s in
    let structs = as_str_field "STRUCTS" s in
    let arrays  = as_str_field "ARRAYS"  s in
    let exns    = as_str_field "EXNS"    s in
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