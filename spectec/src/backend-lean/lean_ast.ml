(* 

A tiny subset of the grammar of Lean4, mostly taken from https://lean-lang.org/doc/reference/latest

Just here to separate the logic for rendering Lean code into raw strings from building the Lean code.

snake_case names directly correspond to camelCase names in the Lean reference, whereas names starting with underscores (like _params) do not, and are my own refactorings for convenience.
*)

type doc_comment = string
type decl_id = string
type ident = string
type hole = Hole

type 'a non_empty_list = {
  head: 'a;
  tail: 'a list;
}

(* TODO: check again *)
type level =
  | LevelLit of int           (* 0, 1, 2, ... *)
  | LevelVar of ident         (* u, v *)
  | LevelAdd of level * int   (* Level + n *)
  | LevelMax of level * level
  | LevelIMax of level * level

type _index_type =
  | Plain
  | Option
  | Unsafe

type term =
  | Hole of hole
  | Fun of term * term
  | Ident of ident
  | Sort of level
  | Type of level option
  | Prop
  | Prod of term * term (* According to https://lean-lang.org/doc/reference/latest/Basic-Types/Tuples/ this should technically be term * term, but I'm doing this for convenience *)
  | FunApp of term * argument non_empty_list
  | FunAppEllipsis of term * argument list
  | Num of _numtype (* check if this makes sense *)
  | Text of string
  (*
    BinaryInfixFunApp does not exist in core Lean4 grammar;
    
    e.g. x + y desugars to HAdd.hAdd x y

    Nevertheless, this serves our conventional rendering
  *)
  | BinaryInfixFunApp of argument * term * argument
  | Tuple of term list (* unsure if this is officially in the Lean 4 grammar *)
  | DotProj of term * term (* unsure if this is officially in the Lean 4 grammar *)
  | Struct of {
    fields: struct_inst_field list;
    type_annotation: term option;
  }
  | List of term list
  | Index of {
    collection: term;
    index: term;
    index_type: _index_type;
  }
  | Slice of {
    collection: term;
    bounds: _slice_bounds;
  }
  | UpdateStruct of {
    struct_to_update: term;
    fields_to_update: struct_inst_field list;
  }

  | Lambda of {
    params: fun_binder non_empty_list;
    body: term;
  }

  | IfThenElse of {
    cond: term;
    then_branch: term;
    else_branch: term;
  }

  (* | UpdateList of {
    name_of_list_to_update: term;
    index: term;
    new_value: term;
  } *)

and fun_binder =
  | Ident_FB of ident

and _slice_bounds =
  | SliceFrom of term
  | SliceTo of term
  | SliceBetween of term * term

and struct_inst_field =
  | Ident_SIF of ident
  | AssignedField of {
    l_val: struct_inst_l_val;
    is_private: bool;
    term: term;
  }



and struct_inst_l_val =
  | Ident_SILV of ident
  | Num_SILV of int
  (*
    TODO: currently unused and thus not yet implemented, but there is one more form described in:

    https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#Lean___Parser___Term___structInstLVal:~:text=a%20term%20in%20square%20brackets%2C%20followed%20by%20a%20sequence%20of%20zero%20or%20more%20subfields
  *)

and argument =
  | Term of term



and _numtype =
  | LeanNat of Z.t
  | LeanInt of Z.t
  | LeanRat of Q.t
  | LeanReal of float


type _ident_or_hole =
  | Ident of ident
  | Hole of hole
type bracketed_binder =
  | ExplicitParam of _ident_or_hole non_empty_list * term
  | OptAutoParam of _ident_or_hole non_empty_list * term * term
  | ImplicitParam of _ident_or_hole non_empty_list * term

type _params =
  | Ident of ident
  | Hole of hole
  | BracketedBinder of bracketed_binder
type decl_sig = _params list * term
type opt_decl_sig = _params list * term option



type visibility =
  | Private
  | Protected
  | Public

type recursion_modifer =
  | Partial
  | NonRec

type decl_modifier = {
  comment: doc_comment option;
  (* TODO: attribute *)
  visibility: visibility option;
  noncomputable: bool;
  unsafe: bool;
  recursion_modifer: recursion_modifer option;
}
type _deriving = ident list

type _def_case = term * term
type _def =
  | DefAsgn of {
      modifier: decl_modifier;
      id: decl_id;
      signature: opt_decl_sig;
      body: term;
    }
  | DefCases of {
      modifier: decl_modifier;
      id: decl_id;
      signature: opt_decl_sig;
      body: _def_case list;
    }

type _inductive_case = {
  modifier: decl_modifier;
  id: ident;
  signature: opt_decl_sig;
}

type _inductive = {
  modifier: decl_modifier;
  id: decl_id;
  signature: opt_decl_sig;
  cases: _inductive_case list;
  deriving: _deriving option
}

type _abbrev = 
  | AbbrevAsgn of {
      modifier: decl_modifier;
      id: decl_id;
      signature: opt_decl_sig;
      body: term;
    }
  | AbbrevCases of {
      modifier: decl_modifier;
      id: decl_id;
      signature: opt_decl_sig;
      body: _def_case list;
    }

type struct_field =
  | StructSimpleBinder of {
      modifier: decl_modifier;
      id: ident;
      signature: opt_decl_sig;
      (* TODO: := expr | by <tactic> *)
    }
  (* TODO: structExplicitBinder, structImplicitBinder, structInstBinder *)
type _structure = {
  modifier: decl_modifier;
  id: decl_id;
  binders: bracketed_binder list;
  universe: term option;
  (* TODO: extends *)
  constructor: (decl_modifier * ident) option;
  fields: struct_field list;
  deriving: _deriving option;
}

type opaque = {
  modifier: decl_modifier;
  id: decl_id;
  signature: decl_sig;
  rhs: term option;
}

(* TODO: technically, this is not just _def, but also theorems. *)
type mutual = _def list

type command =
  | Def of _def
  | Inductive of _inductive
  | Abbrev of _abbrev
  | Structure of _structure
  | Opaque of opaque
  | Mutual of mutual