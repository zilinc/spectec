open Xl
open Il.Ast 

let uncaseE (e : exp) op =
  match e.it with
  | CaseE (o, e) when (Mixop.eq o op) -> 
    (match e.it with 
    | TupE tupe -> ListE tupe (* convert tuple to list in case we need to index *)
    | e' -> e')
  | _ -> failwith "uncase: expected UncaseE"

let projE lst n =
  match lst with
  | ListE es -> (match List.nth_opt es n with
    | Some v -> v
    | None -> failwith "list too short")
  | _ -> failwith "projE: expected ListE"
let mixop_to_atom_str ?(typename = false) (mixop : Mixop.mixop) = match mixop with 
  | [{it = Atom.Atom a; _}]::tail when List.for_all ((=) []) tail -> (*"Atom " ^*) a 
  | mixop -> 
    let lowercase name = 
      if typename then String.lowercase_ascii name 
      else name
    in
    let s =
      String.concat "_pct_" (List.map (
        fun atoms -> String.concat "" (List.map (fun x -> x |> Atom.to_string |> lowercase) atoms)) mixop
      )
    in
    (*"Atom " ^*) s 
