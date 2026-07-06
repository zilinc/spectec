open Lean_ast
open Util.Lib

let empty_modifier : decl_modifier = {
  comment = None;
  visibility = None;
  noncomputable = false;
  unsafe = false;
  recursion_modifer = None;
}

let simple_lambda (param : ident) (body : term) : term =
  Lambda {
    params = NonEmptyList.from_list_unsafe [Ident_FB param];
    (* params = { head = Ident_FB param; tail = [] }; TODO: non empty list util *)
    body = body
  }

let opaque_def = By [
  TacticFirst [
    [TacticExact (DotProj (Ident "Inhabited", Ident "default"))];
    [TacticIntros []; TacticAssumption];
  ]
]

(* TODO: consider how this is implemented; opaque? Mathlib? *)
let rat_to_nat : command =
  (*
    opaque rat_to_nat (r : Rat) : Nat := by
      first
      | exact Inhabited.default
      | intros ; assumption

    Converts a Rat to Nat by truncation toward zero (same semantics as SpecTec's $() cast).
    Defined opaquely to avoid noncomputable issues; the spec treats this as a primitive.
  *)
  Opaque {
    modifier = empty_modifier;
    id = "rat_to_nat";
    signature = (
      [ BracketedBinder (ExplicitParam (
          NonEmptyList.from_list_unsafe [Ident_IOH "r"],
          Ident "Rat"
        )) ],
      Ident "Nat"
    );
    rhs = Some opaque_def;
  }

let list_ap : command =
  (*
    def List.ap (fs : List (α → β)) (xs : List α) : List β :=
      List.zipWith (· ·) fs xs
  *)
  Def (DefAsgn {
    modifier = empty_modifier;
    id = "List.ap";
    signature = (
      [ BracketedBinder (ExplicitParam (NonEmptyList.from_list_unsafe [Ident_IOH "fs"],
          FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (FunType (Ident "α", Ident "β"))])));
        BracketedBinder (ExplicitParam (NonEmptyList.from_list_unsafe [Ident_IOH "xs"],
          FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (Ident "α")]))) ],
      Some (FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (Ident "β")]))
    );
    body = FunApp (
      FunApp (DotProj (Ident "List", Ident "zipWith"), NonEmptyList.from_list_unsafe [Term AnonymousApp]),
      NonEmptyList.from_list_unsafe [Term (Ident "fs"); Term (Ident "xs")]
    );
  })

let option_ap : command =
  (*
    def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
      f.bind (fun f => x.map f)
  *)
  Def (DefAsgn {
    modifier = empty_modifier;
    id = "Option.ap";
    signature = (
      [ BracketedBinder (ExplicitParam (NonEmptyList.from_list_unsafe [Ident_IOH "f"],
          FunApp (Ident "Option", NonEmptyList.from_list_unsafe [Term (FunType (Ident "α", Ident "β"))])));
        BracketedBinder (ExplicitParam (NonEmptyList.from_list_unsafe [Ident_IOH "x"],
          FunApp (Ident "Option", NonEmptyList.from_list_unsafe [Term (Ident "α")]))) ],
      Some (FunApp (Ident "Option", NonEmptyList.from_list_unsafe [Term (Ident "β")]))
    );
    body = FunApp (
      DotProj (Ident "f", Ident "bind"),
      NonEmptyList.from_list_unsafe [Term (Lambda {
        params = NonEmptyList.from_list_unsafe [Ident_FB "f"];
        body = FunApp (DotProj (Ident "x", Ident "map"), NonEmptyList.from_list_unsafe [Term (Ident "f")])
      })]
    );
  })



(* let rec write__abbrev (dm : decl_modifier) (id : ) : _abbrev =
  AbbrevAsgn {
    modifier = dm;
    id = id;
    signature = opt_decl_sig;
    body = term;
  } *)