open Util
open Error
open Source
open Il.Ast
open Il.Print
open Il_util
open Construct


let error at msg = Error.error at "ani.../int.../numerics" msg
let error_value name exp = error exp.at ("Invalid " ^ name ^ ": " ^ string_of_exp exp)
let error_values name exps =
  let at = over_region (List.map (fun e -> e.at) exps) in
  error at ("Invalid " ^ name ^ ": " ^ String.concat ", " (List.map string_of_exp exps))


type numerics = { name : string; f : exp list -> exp }

let maskN n = Z.(pred (shift_left one (to_int n)))


let signed : numerics =
  {
    name = "signed";
    f = fun es ->
      (match List.map it es with
      | [ NumE (`Nat z); NumE (`Nat n) ] ->
        let z = Z.to_int z in
        (if Z.lt n (Z.shift_left Z.one (z - 1)) then n else Z.(sub n (shift_left one z))) |> il_of_z_int
      | _ -> error_values "signed" es
      )
  }

let inv_signed =
  {
    name = "inv_signed";
    f = fun es ->
      (match List.map it es with
      | [ NumE (`Nat z); NumE (`Int n) ] ->
        let z = Z.to_int z in
        (if Z.(geq n zero) then n else Z.(add n (shift_left one z))) |> il_of_z_nat
      | _ -> error_values "inv_signed" es
      )
  }

let truncz : numerics =
  {
    name = "truncz";
    f = fun es ->
      (match List.map it es with
      | [ NumE (`Rat q) ] ->
        Q.to_bigint q |> il_of_z_int
      | _ -> error_values "truncz" es
      )
  }

let sat_u : numerics =
  {
    name = "sat_u";
    f = fun es ->
      (match List.map it es with
      | [ NumE (`Nat z); NumE (`Int i) ] ->
        if Z.(gt i (shift_left one (Z.to_int z) |> pred)) then
          Z.(shift_left one (Z.to_int z) |> pred) |> il_of_z_nat
        else if Z.(lt i zero) then
          Z.zero |> il_of_z_nat
        else
          il_of_z_nat i
      | _ -> error_values "sat_u" es
      );
  }

let sat_s : numerics =
  {
    name = "sat_s";
    f = fun es ->
      (match List.map it es with
      | [ NumE (`Nat z); NumE (`Int i) ] ->
        let n = Z.to_int z - 1 in
        let j =
          if Z.(lt i (shift_left one n |> neg)) then
            Z.(shift_left one n |> neg)
          else if Z.(gt i (shift_left one n |> pred)) then
            Z.(shift_left one n |> pred)
          else
            i
        in inv_signed.f [ il_of_z_nat z; il_of_z_int j ]
      | _ -> error_values "sat_s" es
      );
  }

let inot : numerics =
  {
    name = "inot";
    f =
      (function
      | [ {it = NumE (`Nat z); _ }; m ] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        Z.(logand (lognot m') (maskN z)) |> il_of_iN
      | es -> error_values "inot" es
      );
  }

let irev : numerics =
  {
    name = "irev";
    f =
      (function
      | [ {it = NumE (`Nat z); _ }; m ] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        let rec loop z m n =
          if z = Z.zero then
            n
          else
            let n' = Z.(logor (shift_left n 1) (logand m one)) in
            loop Z.(sub z one) (Z.shift_right m 1) n'
        in loop z m' Z.zero |> il_of_iN
      | es -> error_values "irev" es
      );
  }

let iand : numerics =
  {
    name = "iand";
    f =
      (function
      | [ { it = NumE (`Nat z); _}; m; n ] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        let NumE (`Nat n') = (unwrap_case n).it in
        Z.(logand (logand m' n') (maskN z)) |> il_of_iN
      | es -> error_values "iand" es
      );
  }

let iandnot : numerics =
  {
    name = "iandnot";
    f =
      (function
      | [ { it = NumE (`Nat z); _ }; m; n ] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        let NumE (`Nat n') = (unwrap_case n).it in
        Z.(logand (logand m' (lognot n')) (maskN z)) |> il_of_iN
      | es -> error_values "iandnot" es
      );
  }

let ior : numerics =
  {
    name = "ior";
    f =
      (function
      | [ { it = NumE (`Nat z); _ }; m; n ] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        let NumE (`Nat n') = (unwrap_case n).it in
        Z.(logand (logor m' n') (maskN z)) |> il_of_iN
      | es -> error_values "ior" es
      );
  }

let ixor : numerics =
  {
    name = "ixor";
    f =
      (function
      | [ { it = NumE (`Nat z); _ }; m; n ] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        let NumE (`Nat n') = (unwrap_case n).it in
        Z.(logand (logxor m' n') (maskN z)) |> il_of_iN
      | es -> error_values "ixor" es
      );
  }

let ishl : numerics =
  {
    name = "ishl";
    f =
      (function
      | [ { it = NumE (`Nat z); _ }; m; n ] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        let NumE (`Nat n') = (unwrap_case n).it in
        Z.(logand (shift_left m' (Z.to_int (rem n' z))) (maskN z)) |> il_of_iN
      | vs -> error_values "ishl" vs
      );
  }

let ishr : numerics =
  {
    name = "ishr";
    f =
      (function
      | [ { it = NumE (`Nat z); _ }; sx; m; n] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        let NumE (`Nat n') = (unwrap_case n).it in
        (match match_caseE "sx" sx with
        | [["U"]], [] -> Z.(shift_right m' (Z.to_int (rem n' z))) |> il_of_iN
        | [["S"]], [] ->
          let n'' = Z.(to_int (rem n' z)) in
          let s = Z.to_int z in
          let d = s - n'' in
          let msb = Z.shift_right m' (s - 1) in
          let pad = Z.(mul (shift_left one s - shift_left one d) msb) in
          Z.(logor pad (shift_right m' n'')) |> il_of_iN
        | _ -> error_value "sx" sx
        )
      | es -> error_values "ishr" es
      );
  }

let irotl : numerics =
  {
    name = "irotl";
    f =
      (function
      | [ { it = NumE (`Nat z); _ }; m; n ] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        let NumE (`Nat n') = (unwrap_case n).it in
        let n'' = Z.to_int (Z.rem n' z) in
        (Z.logor (Z.logand (Z.shift_left m' n'') (maskN z)) (Z.shift_right m' ((Z.to_int z - n'')))) |> il_of_iN
      | es -> error_values "irotl" es
      );
  }

let irotr : numerics =
  {
    name = "irotr";
    f =
      (function
      | [ { it = NumE (`Nat z); _ }; m; n ] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        let NumE (`Nat n') = (unwrap_case n).it in
        let n'' = Z.to_int (Z.rem n' z) in
        (Z.logor (Z.shift_right m' n'') (Z.logand (Z.shift_left m' ((Z.to_int z - n''))) (maskN z))) |> il_of_iN
      | es -> error_values "irotr" es
      );
  }

let iclz : numerics =
  {
    name = "iclz";
    f =
      (function
      | [ {it = NumE (`Nat z); _ }; m ] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        if m' = Z.zero then
          z |> il_of_iN
        else
          let z = Z.to_int z in
          let rec loop acc n =
            if Z.equal (Z.logand n (Z.shift_left Z.one (z - 1))) Z.zero then
              loop (1 + acc) (Z.shift_left n 1)
            else
              acc
          in loop 0 m' |> Z.of_int |> il_of_iN
      | es -> error_values "iclz" es
      );
  }

let ictz : numerics =
  {
    name = "ictz";
    f =
      (function
      | [ {it = NumE (`Nat z); _ }; m ] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        if m' = Z.zero then
          z |> il_of_iN
        else
          let rec loop acc n =
            if Z.(equal (logand n one) zero) then
              loop (1 + acc) (Z.shift_right n 1)
            else
              acc
          in loop 0 m' |> Z.of_int |> il_of_iN
      | es -> error_values "ictz" es
      );
  }

let ipopcnt : numerics =
  {
    name = "ipopcnt";
    f =
      (function
      | [ {it = NumE (`Nat z); _ }; m ] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        let rec loop acc i n =
          if i = 0 then
            acc
          else
            let acc' = if Z.(equal (logand n one) one) then acc + 1 else acc in
            loop acc' (i - 1) (Z.shift_right n 1)
        in loop 0 (Z.to_int z) m' |> Z.of_int |> il_of_iN
      | es -> error_values "ipopcnt" es
      );
  }

let ilt : numerics =
  {
    name = "ilt";
    f =
      (function
      | [ { it = NumE (`Nat _); _ } as z; sx; m; n] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        let NumE (`Nat n') = (unwrap_case n).it in
        (match match_caseE "sx" sx with
        | [["U"]], [] -> m' < n' |> int_of_bool |> Z.of_int |> il_of_iN
        | [["S"]], [] ->
          let m'' = signed.f [ z; m ] |> il_to_nat in
          let n'' = signed.f [ z; n ] |> il_to_nat in
          m'' < n'' |> int_of_bool |> Z.of_int |> il_of_iN
        | _ -> error_value "sx" sx
        )
      | es -> error_values "ilt" es
      );
  }

let igt : numerics =
  {
    name = "igt";
    f =
      (function
      | [ { it = NumE (`Nat _); _ } as z; sx; m; n] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        let NumE (`Nat n') = (unwrap_case n).it in
        (match match_caseE "sx" sx with
        | [["U"]], [] -> m' > n' |> int_of_bool |> Z.of_int |> il_of_iN
        | [["S"]], [] ->
          let m'' = signed.f [ z; m ] |> il_to_nat in
          let n'' = signed.f [ z; n ] |> il_to_nat in
          m'' > n'' |> int_of_bool |> Z.of_int |> il_of_iN
        | _ -> error_value "sx" sx
        )
      | es -> error_values "igt" es
      );
  }

let ibitselect : numerics =
  {
    name = "ibitselect";
    f =
      (function
      | [ { it = NumE (`Nat _); _ } as z; i1; i2; i3] ->
        let NumE (`Nat _) = (unwrap_case i1).it in
        let NumE (`Nat _) = (unwrap_case i2).it in
        let NumE (`Nat _) = (unwrap_case i3).it in
        ior.f [ z; iand.f [ z; i1; i3 ]; iand.f [ z; i2; inot.f [ z; i3 ]]]
      | es -> error_values "ibitselect" es
      );
  }

let irelaxed_laneselect : numerics =
  {
    name = "irelaxed_laneselect";
    f =
      (function
      | [ { it = NumE (`Nat _); _ } as z; n1; n2; n3] ->
        let NumE (`Nat _) = (unwrap_case n1).it in
        let NumE (`Nat _) = (unwrap_case n2).it in
        let NumE (`Nat _) = (unwrap_case n3).it in
        ibitselect.f [ z; n1; n2; n3 ] |> mk_singleton (* use deterministic behaviour *)
      | es -> error_values "irelaxed_laneselect" es
      );
  }

let imin : numerics =
  {
    name = "imin";
    f =
      (function
      | [ { it = NumE (`Nat _); _ } as z; { it = CaseE _; _ } as sx; m; n] ->
        let NumE (`Nat _) = (unwrap_case m).it in
        let NumE (`Nat _) = (unwrap_case n).it in
        (if il_to_nat (ilt.f [ z; sx; m; n ]) = Z.one then m else n)
      | es -> error_values "imin" es
      );
  }

let imax : numerics =
  {
    name = "imax";
    f =
      (function
      | [ { it = NumE (`Nat _); _ } as z; { it = CaseE _; _ } as sx; m; n] ->
        let NumE (`Nat _) = (unwrap_case m).it in
        let NumE (`Nat _) = (unwrap_case n).it in
        (if il_to_nat (igt.f [ z; sx; m; n ]) = Z.one then m else n)
      | es -> error_values "imax" es
      );
  }

let iavgr : numerics =
  {
    name = "iavgr";
    f =
      (function
      | [ { it = NumE (`Nat _); _ } as z; sx; m; n] ->
        let NumE (`Nat m') = (unwrap_case m).it in
        let NumE (`Nat n') = (unwrap_case n).it in
        (match match_caseE "sx" sx with
        | [["U"]], [] ->  Z.((m' + n' + one) / of_int 2) |> il_of_iN
        | [["S"]], [] ->
          let m'' = signed.f [ z; natE m' ] |> il_to_int |> Z.of_int in
          let n'' = signed.f [ z; natE n' ] |> il_to_int |> Z.of_int in
          Z.((m'' + n'' + one) / Z.of_int 2) |> il_of_iN
        | _ -> error_value "sx" sx
        )
      | es -> error_values "iavgr" es
      );
  }


let iq15mulr_sat : numerics = todo "iq15mul_sat"
(*
  {
    name = "iq15mulr_sat";
    f = fun es ->
      (match List.map it es with
      (function
      | [ NumV _ as z; sx; NumV _ as m; NumV _ as n ] ->
        let m = signed.f [ z; m ] |> al_to_z_int in
        let n = signed.f [ z; n ] |> al_to_z_int in
        sat.f [ z; sx; NumV (`Int Z.(shift_right (mul m n + of_int 0x4000) 15)) ]
      | vs -> error_values "iq15mulr_sat" vs
      );
  }
*)

let irelaxed_q15mulr : numerics = todo "irelaxed_q15mulr"
(*
  {
    name = "irelaxed_q15mulr";
    f = list_f
      (function
      | [ NumV _ as z; sx; NumV _ as m; NumV _ as n ] ->
        iq15mulr_sat.f [z; sx; m; n]  (* use deterministic behaviour *)
      | vs -> error_values "irelaxed_q15mulr" vs
      );
  }
*)

let numerics_list : numerics list = [
  (*
  profile_nd;
  r_fmadd;
  r_fmin;
  r_fmax;
  r_idot;
  r_iq15mulr;
  r_trunc_u;
  r_trunc_s;
  r_swizzle;
  r_laneselect;
  ibytes;
  inv_ibytes;
  nbytes;
  vbytes;
  inv_nbytes;
  inv_vbytes;
  inv_zbytes;
  inv_cbytes;
  bytes;
  inv_bytes;
  inv_concat;
  inv_concatn;
*)
  truncz;
  sat_u;
  sat_s;
  inot;
  irev;
  iand;
  iandnot;
  ior;
  ixor;
  ishl;
  ishr;
  irotl;
  irotr;
  iclz;
  ictz;
  ipopcnt;
  ibitselect;
  irelaxed_laneselect;
  imin;
  imax;
  iavgr;
  iq15mulr_sat;
  irelaxed_q15mulr;
  (*
  fadd;
  fsub;
  fmul;
  fdiv;
  fmin;
  fmax;
  fcopysign;
  fabs;
  fneg;
  fsqrt;
  fceil;
  ffloor;
  ftrunc;
  fnearest;
  feq;
  fne;
  flt;
  fgt;
  fle;
  fge;
  fpmin;
  fpmax;
  frelaxed_min;
  frelaxed_max;
  frelaxed_madd;
  frelaxed_nmadd;
  extend;
  wrap;
  trunc;
  trunc_sat;
  relaxed_trunc;
  narrow;
  promote;
  demote;
  convert;
  reinterpret;
  lanes;
  inv_lanes;
  inv_ibits;
  *)
]

let call_numerics fname args : exp =
  match List.find_opt (fun numerics -> numerics.name = fname) numerics_list with
  | Some numerics ->
    let args' = List.map (fun a -> match a.it with
    | ExpA e -> e
    | _ -> raise (Failure ("Wrong argument to numeric function " ^ fname ^ ": " ^ string_of_arg a))
    ) args in
    numerics.f args'
  | None -> raise (Failure ("Unknown numerics: " ^ fname))

let mem fname =
  List.exists (fun numerics -> numerics.name = fname) numerics_list
