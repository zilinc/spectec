open Il.Ast
open Il2al.Def
open Il2al.Il2al_util
open Il2al.Print
open Util.Source

let flatten_rec def =
  match def.it with
  | RecD defs -> defs
  | _ -> [ def ]

(* FIXME(zilinc): we may want to do differently than the AL route. *)
let is_anim_target def =
  match def.it with
  | DecD (id, _, _, _) when id.it = "utf8" -> None
  | RelD (id, mixop, t, rules) when List.mem id.it [ "Step"; "Step_read"; "Step_pure" ] ->
    (* HARDCODE: Exclude administrative rules *)
    let filter_rule rule =
      ["pure"; "read"; "trap"; "ctxt"]
      |> List.mem (name_of_rule rule)
      |> not
    in
    Some (RelD (id, mixop, t, List.filter filter_rule rules) $ def.at)
  | RelD _ -> None
  | _ -> Some def


(* Entry *)
let animate il print_dl =
  let dl = il
           |> List.concat_map flatten_rec
           |> List.filter_map is_anim_target
           |> Il2dl.il2dl
           |> fun dl -> (dl, il)
           |> Animate.animate
  in
  match Valid.validate dl with
  | Some errs -> Printf.eprintf "Animation validation:\n%s" (String.concat "\n" errs)
  | None -> if print_dl then
              print_endline (List.map string_of_dl_def dl |> String.concat "\n")
            else
              print_endline ("Animation validation passed.")
