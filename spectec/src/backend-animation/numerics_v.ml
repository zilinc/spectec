open Util
open Error
open Source
open Il_util
open Construct
open Value


let error at msg = Error.error at "ani.../int.../numerics" msg
let error_value ?(at = no) name v = error at ("Invalid " ^ name ^ ": " ^ string_of_value v)
let error_values ?(at = no) name vs =
  error at ("Invalid " ^ name ^ ": " ^ String.concat ", " (List.map string_of_value vs))


type numerics = { name : string; f : value list -> value }

let maskN n = Z.(pred (shift_left one (to_int n)))


let ibytes : numerics =
  {
    name = "ibytes";
    (* TODO: Handle the case where n > 16 (i.e. for v128 ) *)
    f =
      (function
      | [ {it = NumE (`Nat n); _}; i ] ->
        let NumE (`Nat i') = (unwrap_case i).it in
        let rec decompose n bits =
          if n = Z.zero then
            []
          else
            Z.(bits land of_int 0xff) :: decompose Z.(n - of_int 8) Z.(shift_right bits 8)
          in
        assert Z.(n >= Z.zero && rem n (of_int 8) = zero);
        decompose n i' |> List.map natE |> listE'
      | es -> error_values "ibytes" es
      );
  }

let inv_ibytes : numerics =
  {
    name = "inv_ibytes";
    f =
      (function
      | [ {it = NumE (`Nat n); _}; {it = ListE bs; _} ] ->
          assert (
            (* numtype *)
            n = Z.of_int (List.length bs * 8) ||
            (* packtype *)
            (n = Z.of_int 32 && List.length bs <= 2)
          );
          natE (List.fold_right (fun b acc ->
            match b.it with
            | NumE (`Nat b) when Z.zero <= b && b < Z.of_int 256 -> Z.add b (Z.shift_left acc 8)
            | _ -> error_value "inv_ibytes (byte)" b
          ) bs Z.zero)
      | es -> error_values "inv_ibytes" es
      );
  }

(*
let nbytes : numerics =
  {
    name = "nbytes";
    f =
      (function
      | [ CaseV ("I32", []); n ] -> ibytes.f [ NumV thirtytwo; n ]
      | [ CaseV ("I64", []); n ] -> ibytes.f [ NumV sixtyfour; n ]
      | [ CaseV ("F32", []); f ] -> ibytes.f [ NumV thirtytwo; al_to_float32 f |> F32.to_bits |> al_of_nat32 ]
      | [ CaseV ("F64", []); f ] -> ibytes.f [ NumV sixtyfour; al_to_float64 f |> F64.to_bits |> al_of_nat64 ]
      | vs -> error_values "nbytes" vs
      );
  }
let inv_nbytes : numerics =
  {
    name = "inv_nbytes";
    f =
      (function
      | [ CaseV ("I32", []); l ] -> inv_ibytes.f [ NumV thirtytwo; l ]
      | [ CaseV ("I64", []); l ] -> inv_ibytes.f [ NumV sixtyfour; l ]
      | [ CaseV ("F32", []); l ] -> inv_ibytes.f [ NumV thirtytwo; l ] |> al_to_nat32 |> F32.of_bits |> al_of_float32
      | [ CaseV ("F64", []); l ] -> inv_ibytes.f [ NumV sixtyfour; l ] |> al_to_nat64 |> F64.of_bits |> al_of_float64
      | vs -> error_values "inv_nbytes" vs
      );
  }

let vbytes : numerics =
  {
    name = "vbytes";
    f =
      (function
      | [ CaseV ("V128", []); v ] ->
        let s = v |> al_to_vec128 |> V128.to_bits in
        Array.init 16 (fun i -> s.[i] |> Char.code |> al_of_nat) |> listV
      | vs -> error_values "vbytes" vs
      );
  }
let inv_vbytes : numerics =
  {
    name = "inv_vbytes";
    f =
      (function
      | [ CaseV ("V128", []); ListV l ] ->
        let v1 = inv_ibytes.f [ NumV sixtyfour; Array.sub !l 0 8 |> listV ] in
        let v2 = inv_ibytes.f [ NumV sixtyfour; Array.sub !l 8 8 |> listV ] in

        (match v1, v2 with
        | NumV (`Nat n1), NumV (`Nat n2) -> al_of_vec128 (V128.I64x2.of_lanes [ z_to_int64 n1; z_to_int64 n2 ])
        | _ -> error_values "inv_vbytes" [ v1; v2 ]
        )

      | vs -> error_values "inv_vbytes" vs
      );
  }

let inv_zbytes : numerics =
  {
    name = "inv_zbytes";
    f =
      (function
      | [ CaseV ("I8", []); l ] -> inv_ibytes.f [ NumV eight; l ]
      | [ CaseV ("I16", []); l ] -> inv_ibytes.f [ NumV sixteen; l ]
      | args -> inv_nbytes.f args
      );
  }

let inv_cbytes : numerics =
  {
    name = "inv_cbytes";
    f = function
      | [ CaseV ("V128", []); _ ] as args -> inv_vbytes.f args
      | args -> inv_nbytes.f args
  }

let bytes : numerics = { name = "bytes"; f = nbytes.f }
let inv_bytes : numerics = { name = "inv_bytes"; f = inv_nbytes.f }

let wrap : numerics =
  {
    name = "wrap";
    f =
      (function
        | [ NumV _m; NumV (`Nat n); NumV (`Nat i) ] -> natV (Z.logand i (maskN n))
        | vs -> error_values "wrap" vs
      );
  }


let inv_ibits : numerics =
  {
    name = "inv_ibits";
    f =
      (function
      | [ NumV (`Nat n); ListV vs ] as vs' ->
        if Z.of_int (Array.length !vs) <> n then error_values "inv_ibits" vs';
        let na = Array.map (function | NumV (`Nat e) when e = Z.zero || e = Z.one -> e | v -> error_typ_value "inv_ibits" "bit" v) !vs in
        natV (Array.fold_left (fun acc e -> Z.logor e (Z.shift_left acc 1)) Z.zero na)
      | vs -> error_values "inv_ibits" vs
      );
  }

let narrow : numerics =
  {
    name = "narrow";
    f =
      (function
      | [ NumV _ as m; NumV _ as n; CaseV (_, []) as sx; NumV _ as i ] ->
        sat.f [ n; sx; signed.f [ m; i ]]
      | vs -> error_values "narrow" vs);
  }

let lanes : numerics =
  {
    name = "lanes";
    f =
      (function
      | [ CaseV ("X", [ CaseV ("I8", []); NumV (`Nat z) ]); v ] when z = Z.of_int 16 ->
        v |> al_to_vec128 |> V128.I8x16.to_lanes |> List.map al_of_nat8 |> listV_of_list
      | [ CaseV ("X", [ CaseV ("I16", []); NumV (`Nat z) ]); v ] when z = Z.of_int 8 ->
        v |> al_to_vec128 |> V128.I16x8.to_lanes |> List.map al_of_nat16 |> listV_of_list
      | [ CaseV ("X", [ CaseV ("I32", []); NumV (`Nat z) ]); v ] when z = Z.of_int 4 ->
        v |> al_to_vec128 |> V128.I32x4.to_lanes |> List.map al_of_nat32 |> listV_of_list
      | [ CaseV ("X", [ CaseV ("I64", []); NumV (`Nat z) ]); v ] when z = Z.of_int 2 ->
        v |> al_to_vec128 |> V128.I64x2.to_lanes |> List.map al_of_nat64 |> listV_of_list
      | [ CaseV ("X", [ CaseV ("F32", []); NumV (`Nat z) ]); v ] when z = Z.of_int 4 ->
        v |> al_to_vec128 |> V128.F32x4.to_lanes |> List.map al_of_float32 |> listV_of_list
      | [ CaseV ("X", [ CaseV ("F64", []); NumV (`Nat z) ]); v ] when z = Z.of_int 2 ->
        v |> al_to_vec128 |> V128.F64x2.to_lanes |> List.map al_of_float64 |> listV_of_list
      | vs -> error_values "lanes" vs
      );
  }
let inv_lanes : numerics =
  {
    name = "inv_lanes";
    f =
      (function
      | [ CaseV ("X",[ CaseV ("I8", []); NumV (`Nat z) ]); ListV lanes; ] when z = Z.of_int 16 && Array.length !lanes = 16 ->
        List.map al_to_int8 (!lanes |> Array.to_list) |> V128.I8x16.of_lanes |> al_of_vec128
      | [ CaseV ("X",[ CaseV ("I16", []); NumV (`Nat z) ]); ListV lanes; ] when z = Z.of_int 8 && Array.length !lanes = 8 ->
        List.map al_to_int16 (!lanes |> Array.to_list) |> V128.I16x8.of_lanes |> al_of_vec128
      | [ CaseV ("X",[ CaseV ("I32", []); NumV (`Nat z) ]); ListV lanes; ] when z = Z.of_int 4 && Array.length !lanes = 4 ->
        List.map al_to_nat32 (!lanes |> Array.to_list) |> V128.I32x4.of_lanes |> al_of_vec128
      | [ CaseV ("X",[ CaseV ("I64", []); NumV (`Nat z) ]); ListV lanes; ] when z = Z.of_int 2 && Array.length !lanes = 2 ->
        List.map al_to_nat64 (!lanes |> Array.to_list) |> V128.I64x2.of_lanes |> al_of_vec128
      | [ CaseV ("X",[ CaseV ("F32", []); NumV (`Nat z) ]); ListV lanes; ] when z = Z.of_int 4 && Array.length !lanes = 4 ->
        List.map al_to_float32 (!lanes |> Array.to_list) |> V128.F32x4.of_lanes |> al_of_vec128
      | [ CaseV ("X",[ CaseV ("F64", []); NumV (`Nat z) ]); ListV lanes; ] when z = Z.of_int 2 && Array.length !lanes = 2 ->
        List.map al_to_float64 (!lanes |> Array.to_list) |> V128.F64x2.of_lanes |> al_of_vec128
        | vs -> error_values "inv_lanes" vs
      );
  }

let rec inv_concat_helper = function
  | a :: b :: l ->
    [listV_of_list [a; b]] @ inv_concat_helper l
  | [] -> []
  | vs -> error_values "inv_concat_helper" vs

let inv_concat : numerics =
  {
    name = "inv_concat";
    f =
      (function
      | [ ListV _ as lv ] ->
        lv
        |> unwrap_listv_to_list
        |> inv_concat_helper
        |> listV_of_list
      | vs -> error_values "inv_concat" vs
      );
  }

let rec inv_concatn_helper n prev = function
  | a :: l ->
    let next = prev @ [a] in
    if List.length next = n then
      [listV_of_list (prev @ [a])] @ inv_concatn_helper n [] l
    else
      inv_concatn_helper n next l
  | [] -> []

let inv_concatn : numerics =
  {
    name = "inv_concatn";
    f =
      (function
      | [ NumV (`Nat len); ListV _ as lv] ->
        let n = Z.to_int len in
        let l =
          lv
          |> unwrap_listv_to_list
        in
        assert (List.length l mod n = 0);
        l
        |> inv_concatn_helper n []
        |> listV_of_list
      | vs -> error_values "inv_concatn" vs
      );
  }
*)

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
      | [ {it = NumE (`Nat z); _}; m ] ->
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
      | [ {it = NumE (`Nat z); _}; m ] ->
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
      | [ {it = NumE (`Nat z); _}; m; n ] ->
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
      | [ {it = NumE (`Nat z); _}; m; n ] ->
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
      | [ {it = NumE (`Nat z); _}; m; n ] ->
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
      | [ {it = NumE (`Nat z); _}; m; n ] ->
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
      | [ {it = NumE (`Nat z); _}; m; n ] ->
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
      | [ {it = NumE (`Nat z); _}; sx; m; n] ->
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
      | [ {it = NumE (`Nat z); _}; m; n ] ->
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
      | [ {it = NumE (`Nat z); _}; m; n ] ->
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
      | [ {it = NumE (`Nat z); _}; m ] ->
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
      | [ {it = NumE (`Nat z); _}; m ] ->
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
      | [ {it = NumE (`Nat z); _}; m ] ->
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
      | [ {it = NumE (`Nat _); _} as z; sx; m; n] ->
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
      | [ {it = NumE (`Nat _); _} as z; sx; m; n] ->
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
      | [ {it = NumE (`Nat _); _} as z; i1; i2; i3] ->
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
      | [ {it = NumE (`Nat _); _} as z; n1; n2; n3] ->
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
      | [ {it = NumE (`Nat _); _} as z; {it = CaseE _; _} as sx; m; n] ->
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
      | [ {it = NumE (`Nat _); _} as z; {it = CaseE _; _} as sx; m; n] ->
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
      | [ {it = NumE (`Nat _); _} as z; sx; m; n] ->
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


let iq15mulr_sat : numerics =
  {
    name = "iq15mulr_sat";
    f =
      (function
      | [ {it = NumE (`Nat _); _} as z; sx; m; n] ->
        let NumE (`Nat _) = (unwrap_case m).it in
        let NumE (`Nat _) = (unwrap_case n).it in
        let m' = signed.f [ z; m ] |> il_to_int |> Z.of_int in
        let n' = signed.f [ z; n ] |> il_to_int |> Z.of_int in
        (match match_caseE "sx" sx with
        | [["U"]], _ -> sat_u.f [ z; sx; Z.(shift_right (mul m' n' + of_int 0x4000) 15) |> intE ]
        | [["S"]], _ -> sat_s.f [ z; sx; Z.(shift_right (mul m' n' + of_int 0x4000) 15) |> intE ]
        | _ -> error_value "sx" sx
        )
      | es -> error_values "iq15mulr_sat" es
      );
  }

let irelaxed_q15mulr : numerics =
  {
    name = "irelaxed_q15mulr";
    f =
      (function
      | [ {it = NumE (`Nat _); _} as z; sx; m; n] ->
        iq15mulr_sat.f [z; sx; m; n] |> mk_singleton (* use deterministic behaviour *)
      | es -> error_values "irelaxed_q15mulr" es
      );
  }

let fgt : numerics =
  {
    name = "fgt";
    f =
      (function
      | [ {it = NumE (`Nat z); _}; {it = CaseE _; _} as f1; {it = CaseE _; _} as f2; ] when z = Z.of_int 32 ->
        RI.F32.gt (il_to_float32 f1) (il_to_float32 f2) |> int_of_bool |> Z.of_int |> il_of_iN
      | [ {it = NumE (`Nat z); _}; {it = CaseE _; _} as f1; {it = CaseE _; _} as f2; ] when z = Z.of_int 64 ->
        RI.F64.gt (il_to_float64 f1) (il_to_float64 f2) |> int_of_bool |> Z.of_int |> il_of_iN
      | es -> error_values "fgt" es
      );
  }

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
  *)
  ibytes;
  inv_ibytes;
  (*
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
  *)
  fgt;
  (*
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

let rec strip_suffix name =
  let last = String.length name - 1 in
  if name <> "" && name.[last] = '_' then
    strip_suffix (String.sub name 0 last)
  else
    name

let call_numerics fname args : value =
  let fname' = strip_suffix fname in  (* Yuck! *)
  match List.find_opt (fun numerics -> numerics.name = fname') numerics_list with
  | Some numerics ->
    let args' = List.map (function
    | ValA v -> v
    | a -> raise (Failure ("Wrong argument to numeric function " ^ fname ^ ": " ^ string_of_arg a))
    ) args in
    numerics.f args'
  | None -> raise (Failure ("Unknown numerics: " ^ fname'))

let mem fname =
  let fname' = strip_suffix fname in  (* Yuck! *)
  List.exists (fun numerics -> numerics.name = fname') numerics_list
