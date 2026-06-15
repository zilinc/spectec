open Lean_ast

let empty_modifier : decl_modifier = {
  comment = None;
  visibility = None;
  noncomputable = false;
  unsafe = false;
  recursion_modifer = None;
}

let simple_lambda (param : ident) (body : term) : term =
  Lambda {
    params = { head = Ident_FB param; tail = [] }; (* TODO: non empty list util *)
    body = body
  }

(* let rec write__abbrev (dm : decl_modifier) (id : ) : _abbrev =
  AbbrevAsgn {
    modifier = dm;
    id = id;
    signature = opt_decl_sig;
    body = term;
  } *)