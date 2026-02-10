module L = Util.Lib
open Il.Ast
open Il.Print
open Def

type line = string
type text = line list

let return a = Some a
let fail a = None


let vcat_f f ls = List.concat_map f ls
let hcat_f d f xs = String.concat d (List.map f xs)

let indent n ls = List.map (fun l -> (String.make n ' ') ^ l) ls

let lister lv n =
  match lv with
  | 0 -> string_of_int n ^ "."
  | 1 -> (Char.chr (n + 96) |> String.make 1) ^ "."
  | 2 ->
    (match n with
    | 1 -> "i"
    | 2 -> "ii"
    | 3 -> "iii"
    | 4 -> "iv"
    | 5 -> "v"
    | 6 -> "vi"
    | 7 -> "vii"
    | 8 -> "viii"
    | 9 -> "ix"
    | 10 -> "x"
    | _ -> raise (Failure "Invalid or too large Roman number")
    ) ^ "."
  | _ -> raise (Failure "Invalid level")

let text_prose_nth (n: int): string =
  string_of_int n ^
  (if List.mem (n mod 100) [11; 12; 13] then "th" else
  if n mod 10 = 1 then "st" else
  if n mod 10 = 2 then "nd" else
  if n mod 10 = 3 then "rd" else
  "th")


let text_prose_num (num: num) : string = Xl.Num.to_string num

let text_prose_arg arg : line = string_of_arg arg
let text_prose_args args : line = hcat_f ", " text_prose_arg args


let text_prose_unop : unop -> string = function
  | `NotOp -> "¬"
  | `PlusOp -> ""
  | `MinusOp -> "−"

let text_prose_binop : binop -> string = function
  | `AndOp -> "∧"
  | `OrOp -> "∨"
  | `ImplOp -> "⟶"
  | `EquivOp -> "⟷"
  | `AddOp -> "+"
  | `SubOp -> "−"
  | `MulOp -> "×"
  | `DivOp -> "÷"
  | `ModOp -> "mod"
  | `PowOp -> "^"

let text_prose_cmpop : cmpop -> string = function
  | `EqOp -> "="
  | `NeOp -> "≠"
  | `LtOp -> "<"
  | `GtOp -> ">"
  | `LeOp -> "≤"
  | `GeOp -> "≥"

let rec text_prose_exp (exp: exp) : string =
  match exp.it with
  | VarE v -> v.it
  | BoolE b -> string_of_bool b
  | NumE n -> Xl.Num.to_string n
  | TextE s -> "\"" ^ s ^ "\""
  | UnE (unop, optyp, exp') -> text_prose_unop unop ^ " " ^ text_prose_exp exp'
  | BinE (binop, optyp, exp1, exp2) -> "(" ^ text_prose_exp exp1 ^ " " ^ text_prose_binop binop ^ " " ^ text_prose_exp exp2 ^ ")"
  | CmpE (cmpop, optyp, exp1, exp2) -> "(" ^ text_prose_exp exp1 ^ " " ^ text_prose_cmpop cmpop ^ " " ^ text_prose_exp exp2 ^ ")"
  | TupE [] -> ""
  | TupE exps -> "a tuple of " ^ hcat_f ", " text_prose_exp exps
  | ProjE (exp', n) -> "the " ^ text_prose_nth n ^ " projection of " ^ text_prose_exp exp'
  | CaseE (mixop, { it = TupE []; _ }) -> string_of_mixop mixop
  | CaseE (mixop, { it = TupE es; _ }) -> string_of_mixop mixop ^ "(" ^ hcat_f ", " text_prose_exp es ^ ")"
  | UncaseE (exp', mixop) -> "the payload of " ^ text_prose_exp exp'
  | OptE None -> "none"
  | OptE (Some exp') -> "some " ^ text_prose_exp exp'
  | TheE exp' -> "the " ^ text_prose_exp exp'
  | StrE expfields -> "struct of " ^ String.concat ", " (List.map string_of_expfield expfields)
  | DotE (exp', atom) -> "the " ^ string_of_atom atom ^ " field of struct " ^ text_prose_exp exp'
  | CompE (exp1, exp2) -> "composition of " ^ text_prose_exp exp1 ^ " and " ^ text_prose_exp exp2
  | ListE exps -> "list of " ^ hcat_f ", " text_prose_exp exps
  | LiftE exp' -> text_prose_exp exp'
  | MemE (elt, set) -> text_prose_exp elt ^ " is an element of set " ^ text_prose_exp set
  | LenE exp' -> "the length of list " ^ text_prose_exp exp'
  | CatE (exp1, exp2) -> "the concatenation of " ^ text_prose_exp exp1 ^ " and " ^ text_prose_exp exp2
  | IdxE (exp', idx) -> "the element of " ^ text_prose_exp exp' ^ " at index " ^ text_prose_exp idx
  | SliceE (exp', init, len) -> "taking a slice of " ^ text_prose_exp exp' ^
                                " from the index " ^ text_prose_exp init ^
                                " of length " ^ text_prose_exp len
  | UpdE (exp', path, to_) -> text_prose_exp exp' ^ " with its path " ^ string_of_path path ^ " updated to " ^ text_prose_exp to_
  | ExtE (exp', path, with_) -> text_prose_exp exp' ^ " with its path " ^ string_of_path path ^ " extended with " ^ text_prose_exp with_
  | CallE (fid, args) -> "call function " ^ fid.it ^ " with arguments " ^ text_prose_args args
  | IterE (exp', ((iter, xes) as iterexp)) -> "iterated " ^ text_prose_exp exp'
  | CvtE (exp', numtyp1, numtyp2) -> text_prose_exp exp'
  | SubE (exp', typ1, typ2) -> text_prose_exp exp'
  | IfE (c, th, el) -> "if " ^ text_prose_exp c ^ " then " ^ text_prose_exp th ^ " else " ^ text_prose_exp c

let rec text_prose_premise (lv: int) (nth: int option) (prem: prem) : text =
  let number = (match nth with | None -> "" | Some n -> lister lv n ^ " ") in
  match prem.it with
  | RulePr (id, mixop, exp) -> assert false
  | IfPr e -> [number ^ "If " ^ text_prose_exp e ^ ", continue; otherwise fail."]
  | LetPr (lhs, rhs, _bs) -> [number ^ "Let " ^ text_prose_exp lhs ^ " be " ^ text_prose_exp rhs ^ "."]
  | ElsePr -> [number ^ "If no clause above succeeds:"]
  | IterPr (prems, ((iter, xes) as iterexp)) ->
    let text_iter = (match iter with
    | Opt   -> [number ^ "Run optionally:"]
    | List  -> [number ^ "Iterate through the lists:"]
    | List1 -> [number ^ "Iterate at least once:"]
    | ListN (n, None)   -> [number ^ "Iterate " ^ string_of_exp n ^ " times"]
    | ListN (n, Some i) -> [number ^ "Let " ^ string_of_id i ^ " iterate from 0 until " ^ string_of_exp n ^ "."]
    ) in
    let text_prems = text_prose_premises (lv + 1) (Some 1) prems in
    text_iter @ indent 2 text_prems
  | NegPr prem' -> "It is not true that:" :: text_prose_premise lv None prem'

and text_prose_premises (lv: int) (nth: int option) (prems: prem list) : text =
  List.mapi (fun i prem ->
    let nth' = Option.map (fun n -> n + i) nth in
    text_prose_premise lv nth' prem
  ) prems |> List.concat

let text_prose_clause (params: param list) (fc: func_clause) : text =
  let DefD (_binds, args, exp, prems) = (snd fc).it in
  let text_args = text_prose_args args in
  let text_prems = text_prose_premises 0 (Some 1) prems in
  let text_rhs = text_prose_exp exp in
  assert (List.length args = 1);
  [ "* Suppose the input is " ^ text_args ^ "." ] @
  text_prems @
  [ "Finally, return " ^ text_rhs ^ "."; "" ]

let text_prose_func : func_def -> text = fun fdef ->
  let fid, osubid, params, _ty, clauses, _ = fdef.it in
  if List.exists (fun step_id -> step_id = fid.it) Common.step_relids then
    let heading = "### " ^ fid.it in
    let body = vcat_f (text_prose_clause params) clauses in
    heading :: body @ [""]
  else
    []

let rec text_prose_def : dl_def -> text = function
  | TypeDef tdef -> []
  | FuncDef fdef -> text_prose_func fdef
  | RecDef defs  -> vcat_f text_prose_def defs
  | RuleDef _    -> assert false

let text_prose_script (dl: dl_def list) : string = String.concat "\n" (vcat_f text_prose_def dl)
