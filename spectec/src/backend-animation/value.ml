open Xl
open Il.Ast
open Util
open Source

let no = Source.no_region


type 'a growable_array = 'a array ref

type ('a, 'b) record = ('a * 'b ref) list

type mixop = string list list

and value =
  | BoolV of bool                      (* boolean *)
  | NumV of num                        (* number *)
  | TextV of string                    (* string *)
  | ListV of value growable_array      (* list of values *)
  | TupV of value list                 (* tuple of values *)
  | OptV of value option               (* optional value *)
  | CaseV of mixop * value list        (* constructor *)
  | StrV of (string, value) record     (* key-value mapping *)

and arg =
  | ValA of value                      (* value *)
  | TypA of typ                        (* `syntax` typ *)
  | DefA of id                         (* `def` defid *)
  | GramA of sym                       (* `grammar` sym *)

type iter =
  | Opt
  | List
  | List1
  | ListN of value * id option


let vl_of_mixop : Xl.Mixop.mixop -> mixop = function
  | mss -> List.map (fun ms -> List.map Atom.to_string ms) mss


let rec string_of_mixop =
  let rec go = function
           | []  -> ""
           | [a] -> a
           | a::as_ -> a ^ ":" ^ go as_
  in
  function
  | []    -> assert false
  | [l]   -> go l
  | l::ls -> go l ^ "%" ^ string_of_mixop ls

let rec string_of_value = function
  | BoolV b -> string_of_bool b
  | NumV  n -> Num.to_string n
  | TextV t -> "\"" ^ String.escaped t ^ "\""
  | ListV a -> "[" ^ string_of_array a ^ "]"
  | TupV vs -> "(" ^ string_of_values ", " vs ^ ")"
  | OptV ov -> "?(" ^ string_of_values "" (Option.to_list ov) ^ ")"
  | CaseV (m, vs) -> string_of_mixop m ^ "(" ^ string_of_values ", " vs ^ ")"
  | StrV  r -> string_of_record r

and string_of_values delim = function
  | [] -> ""
  | [v] -> string_of_value v
  | v::vs -> string_of_value v ^ delim ^ string_of_values delim vs

and string_of_array (a: value growable_array) =
  string_of_values "; " (Array.to_list !a)

and string_of_record r =
  let str = List.fold_left (fun str (k, v) -> str ^ ", " ^ k ^ " = " ^ string_of_value !v) "" r in
  "{" ^ str ^ "}"

and string_of_arg = function
  | ValA  v -> string_of_value v
  | TypA  t -> "syntax " ^ Il.Print.string_of_typ t
  | DefA  f -> "def $" ^ f.it
  | GramA s -> "grammar " ^ Il.Print.string_of_sym s

and string_of_args = function
  | [] -> ""
  | as_ -> "(" ^ String.concat ", " (List.map string_of_arg as_) ^ ")"


let error at msg = Error.error at "animation/value" msg
let error_value ?(at = no) name val_ = error at ("Invalid " ^ name ^ ": " ^ string_of_value val_)
let error_values ?(at = no) name vals = error at ("Invalid " ^ name ^ ": " ^ string_of_values ", " vals)




let eq_record f r1 r2 = List.length r1 =
  List.length r1 && List.for_all2 (fun (k1, v1) (k2, v2) -> k1 = k2 && f !v1 !v2) r1 r2

let rec eq_value v1 v2 = match v1, v2 with
  | BoolV b1, BoolV b2 -> b1 = b2
  | NumV n1 , NumV n2  -> n1 = n2
  | TextV t1, TextV t2 -> t1 = t2
  | ListV a1, ListV a2 -> Array.length !a1 = Array.length !a2 && Array.for_all2 (=) !a1 !a2
  | TupV vs1, TupV vs2 -> List.for_all2 eq_value vs1 vs2
  | OptV ov1, OptV ov2 -> Option.equal eq_value ov1 ov2
  | CaseV (m1, vs1), CaseV (m2, vs2) -> m1 = m2 && List.for_all2 eq_value vs1 vs2
  | StrV r1 , StrV r2  -> eq_record eq_value r1 r2
  | _ -> false

let as_opt_value = function
  | OptV ov -> ov
  | v -> error no ("as_opt_value: " ^ string_of_value v)

let as_list_value = function
  | ListV vs -> vs
  | v -> error no ("as_list_value: " ^ string_of_value v)

let as_list_value' v = !(as_list_value v) |> Array.to_list

let find_list_elem p = function
  | ListV vs -> Array.find_opt p !vs |> Option.get
  | v -> error no ("find_list_elem: " ^ string_of_value v)

let as_num_value = function
  | NumV num' -> num'
  | v -> error no ("as_num_value: " ^ string_of_value v)

let as_nat_value : value -> Z.t = function
  | NumV (`Nat n) -> n
  | v -> error no ("as_nat_value: " ^ string_of_value v)

let as_int_value : value -> Z.t = function
  | NumV (`Int n) -> n
  | v -> error no ("as_int_value: " ^ string_of_value v)

let as_text_value : value -> string = function
  | TextV s -> s
  | v -> error no ("as_text_value: " ^ string_of_value v)

let as_singleton_case = function
  | CaseV ([[];[]], [v]) -> v
  | v -> error no ("as_singleton_case: " ^ string_of_value v)

let as_case_value = function
  | CaseV (_, vs) -> vs
  | v ->  error no ("as_case_value: " ^ string_of_value v)

let as_str_value = function
  | StrV str -> str
  | v -> error no ("as_str_value: " ^ string_of_value v)

let has_str_field atom str : bool =
  match str with
  | StrV fvs -> List.exists (fun (atom', _) -> atom' = atom) fvs
  | _ -> error no ("has_str_field: " ^ string_of_value str)

let as_str_field atom str : value =
  match str with
  | StrV fvs -> !(List.find (fun (atom', _) -> atom' = atom) fvs |> snd)
  | _ -> error no ("as_str_field: " ^ string_of_value str)

let nth_of_list lst (idx: Z.t) : value =
  match lst with
  | ListV vs -> Array.get !vs (Z.to_int idx)
  | _ -> error no ("nth_of_list: " ^ string_of_value lst)

let of_bool_value = function
  | BoolV b -> Some b
  | _ -> None

let of_num_value = function
  | NumV n -> Some n
  | _ -> None

let match_caseV name v : string list list * value list =
  match v with
  | CaseV (tag, vs) -> tag, vs
  | _ -> error_value (name ^ " (match_caseV)") v



let listV a = ListV (ref a)
let listV_of_list l = Array.of_list l |> listV

let natV z = NumV (`Nat z)
let intV z = NumV (`Int z)
let numV n = NumV n
let boolV b = BoolV b
let textV s = TextV s
let optV ov = OptV ov
let caseV mixop vs = CaseV (mixop, vs)
let caseV1 v = caseV [[];[]] [v]
let tupV vs = TupV vs
let strV fvs = StrV fvs

(* dim *)
let num i = natV (Z.of_int i) |> caseV1
let two       = num 2
let four      = num 4
let eight     = num 8
let sixteen   = num 16
let thirtytwo = num 32
let sixtyfour = num 64

let int_of_bool b = Stdlib.Bool.to_int b

let vl_of_nat (n: int): value = natV (Z.of_int n)
let vl_of_int (n: int): value = intV (Z.of_int n)

let vl_of_list f l = List.map f l |> listV_of_list
let vl_of_seq f s = List.of_seq s |> vl_of_list f
let vl_of_opt f opt = Option.map f opt |> optV
let vl_of_tup fvl = List.map (fun (f, v) -> f v) fvl |> tupV

let valA a = ValA a
let typA a = TypA a

let none = optV None
let some v = optV (Some v)
let nullary con = caseV [[String.uppercase_ascii con]] []
let singleton v = listV [|v|]
let listv_singleton = function
  | ListV arr_ref when Array.length !arr_ref = 1 -> Array.get !arr_ref 0
  | v -> error_value "listv_singleton" v
