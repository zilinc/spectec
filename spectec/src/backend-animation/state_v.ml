open Value
open Il.Ast
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


(* Host state *)

module HostState = struct
  (* Global host state *)
  let timestamp : int ref = ref 0
  let get_glb_state () : value = vl_of_nat !timestamp
  let inc_glb_timestamp () = timestamp := !timestamp + 1
  let reset_glb_timestamp () = timestamp := 0

  module EffectDomain : Map.OrderedType with type t = int * string = struct
    type t = int * string
    let compare = Stdlib.compare
  end

  module Map = Map.Make(EffectDomain)
  type effect_ = Print of string

  (* Global effects map. *)
  let effect_map : ((value * effect_ list) Map.t) ref = ref Map.empty

  let add_effects (hf_name: string) res effs =
    effect_map := Map.add (!timestamp, hf_name) (res, effs) !effect_map;
    List.iter (function
    | Print s -> print_string s
    ) effs;
    inc_glb_timestamp ()

  let lookup_effect hf_name ts = Map.find_opt (ts, hf_name) !effect_map

  let get_effects () : effect_ list =
    Map.bindings !effect_map |> List.map (fun x -> snd (snd x)) |> List.concat


  (* Local host state *)
  let mk_state ts : value = vl_of_nat ts
  let get_timestamp hs : int = as_nat_value hs |> Z.to_int
  let inc_timestamp hs : value =
    let ts = get_timestamp hs in
    let ts' = ts + 1 in
    mk_state ts'


  (* Functions *)
  type ts_cmp = Earlier | Good | Later

  let chk_state hs : ts_cmp =
    let global_ts = !timestamp in
    let local_ts = as_nat_value hs |> Z.to_int in
    if local_ts < global_ts then Earlier
    else if local_ts = global_ts then Good
    else Later
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
      |> Record.add "HOST"    (HostState.mk_state 0)

    (* Ds.Store.init () *)  (* NOTE: I don't think there's anything that depends on Ds. / zilinc *)


  let get () = strV !store

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
    let hstate  = as_str_field "HOST"    s in
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
    update "HOST"    (Fun.const hstate )

end


(* Hints about animation *)

module Hints = struct
  module M  = Map.Make(String)
  module IM = Map.Make(Int)
  type mode = In | Out
  type t = { mutable no_animate_funcs: string list
           ; mutable animate_funcs   : (mode list * mode) M.t  (* arguments * result *)
           ; mutable animate_inv     : string list
           ; mutable animate_rels    : mode IM.t M.t           (* in the order of expressions in the CaseE *)
           ; mutable animate_builtin : mode IM.t M.t
           ; mutable no_animate_rules: (string * string) list  (* relid * ruleid *)
           }

  let animation_hints : t = { no_animate_funcs = []; animate_funcs = M.empty; animate_inv = []
                            ; animate_rels = M.empty; animate_builtin = M.empty; no_animate_rules = []
                            }
  let init_animation_hints () = animation_hints.no_animate_funcs <- [];
                                animation_hints.animate_funcs    <- M.empty;
                                animation_hints.animate_inv      <- [];
                                animation_hints.animate_rels     <- M.empty;
                                animation_hints.animate_builtin  <- M.empty;
                                animation_hints.no_animate_rules <- []

  let add_na_func fid          = animation_hints.no_animate_funcs <- animation_hints.no_animate_funcs @ [fid]
  let add_a_func  fid args res = animation_hints.animate_funcs    <- M.add fid (args, res) animation_hints.animate_funcs
  let add_a_inv fid            = animation_hints.animate_inv      <- animation_hints.animate_inv @ [fid]
  let add_a_rel   rid mm       = animation_hints.animate_rels     <- M.add rid mm animation_hints.animate_rels
  let add_a_builtin rid mm     = animation_hints.animate_builtin  <- M.add rid mm animation_hints.animate_builtin

  let is_na_func   fid = List.mem fid animation_hints.no_animate_funcs
  let is_a_func    fid = M.mem fid animation_hints.animate_funcs
  let is_a_inv     fid = (List.mem fid animation_hints.animate_inv) || (String.starts_with ~prefix:"proj_" fid)
  let is_a_rel     rid = M.mem rid animation_hints.animate_rels
  let is_a_builtin rid = M.mem rid animation_hints.animate_builtin

  let find_a_func    fid = M.find fid animation_hints.animate_funcs
  let find_a_rel     rid = M.find rid animation_hints.animate_rels
  let find_a_builtin rid = M.find rid animation_hints.animate_builtin

  type side = L | R

  let parse_hintexp : El.Ast.exp -> mode IM.t =
    let rec go side (exp: El.Ast.exp) mm = match exp.it with
    | HoleE (`Num i) -> if side = L then IM.add i In mm else IM.add i Out mm
    | VarE (b, []) when b.it = "bool" -> mm
    | ParenE e -> go side e mm
    | TupE es | SeqE es -> List.fold_left (fun acc e -> go side e acc) mm es
    | _ -> mm
    in
    fun exp -> match exp.it with
    | InfixE (lhs, atom, rhs) when atom.it = Xl.Atom.Arrow ->
      let lm = go L lhs IM.empty in
      let rm = go R rhs lm in
      rm
    | _ -> print_endline ("Warning: Possibly ill-formed animate hint: " ^ El.Print.string_of_exp exp); IM.empty

  (* A list of function ids that should be automatically inverted. *)
  let invert_funcs : id list ref = ref []  (* Def.func_def list *)

  let add_invert_func id = invert_funcs := id :: !invert_funcs
  let rm_invert_func id = invert_funcs := List.filter (fun x -> Il.Eq.eq_id x id |> not) !invert_funcs

  (* kashish's temp debugging things *)
  let hints_to_string () =
    let h = animation_hints in
    let b = Buffer.create 1024 in
    let add = Buffer.add_string b in

    add "=== Animation Hints ===\n";

    add "\nno_animate_funcs:\n";
    List.iter (fun f -> add (Printf.sprintf "  %s\n" f)) h.no_animate_funcs;

    add "\nanimate_funcs:\n";
    M.iter (fun fid (args, res) ->
      let mode_str m = match m with In -> "In" | Out -> "Out" in
      let args_str = String.concat ", " (List.map mode_str args) in
      add (Printf.sprintf "  %s: (%s) -> %s\n" fid args_str (mode_str res))
    ) h.animate_funcs;

    add "\nanimate_inv:\n";
    List.iter (fun f -> add (Printf.sprintf "  %s\n" f)) h.animate_inv;

    add "\nanimate_rels:\n";
    M.iter (fun rid mm ->
      add (Printf.sprintf "  %s:\n" rid);
      IM.iter (fun i m ->
        add (Printf.sprintf "    %d -> %s\n" i (match m with In -> "In" | Out -> "Out"))
      ) mm
    ) h.animate_rels;

    add "\nanimate_builtin:\n";
    M.iter (fun rid mm ->
      add (Printf.sprintf "  %s:\n" rid);
      IM.iter (fun i m ->
        add (Printf.sprintf "    %d -> %s\n" i (match m with In -> "In" | Out -> "Out"))
      ) mm
    ) h.animate_builtin;

    add "\nno_animate_rules:\n";
    List.iter (fun (rid, ruleid) ->
      add (Printf.sprintf "  %s / %s\n" rid ruleid)
    ) h.no_animate_rules;

    Buffer.contents b

(* takes in a wf relation and creates an animation hint for it *)
let hint_of_relD (id : id) (mixop : mixop) : unit =
  let n_holes = List.length mixop - 1 in
  let mm =
    List.fold_left (fun acc i -> IM.add i In acc)
      IM.empty (List.init n_holes (fun i -> i + 1))
  in
  add_a_rel id.it mm

end
