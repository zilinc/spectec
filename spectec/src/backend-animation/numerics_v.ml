open Util
open Error
open Source
open Construct_v
open Value


let error at msg = Error.error at "animation/numerics_v" msg
let error_value ?(at = no) name v = error at ("Invalid " ^ name ^ ": " ^ string_of_value v)
let error_values ?(at = no) name vs =
  error at ("Invalid " ^ name ^ ": " ^ String.concat ", " (List.map string_of_value vs))


type numerics = { name : string; f : value list -> value }

let maskN n = Z.(pred (shift_left one (to_int n)))

let mask64 = Z.of_int64_unsigned (-1L)

let z_to_int64 z = Z.(to_int64_unsigned (logand mask64 z))

let list_f f x = f x |> singleton
let unlist_f f x = f x |> listv_singleton
let bop_f32 f f1 f2 = f (vl_to_float32 f1) (vl_to_float32 f2) |> vl_of_float32
let bop_f64 f f1 f2 = f (vl_to_float64 f1) (vl_to_float64 f2) |> vl_of_float64
let bop_f32_b f f1 f2 = f (vl_to_float32 f1) (vl_to_float32 f2) |> int_of_bool |> Z.of_int |> vl_of_iN
let bop_f64_b f f1 f2 = f (vl_to_float64 f1) (vl_to_float64 f2) |> int_of_bool |> Z.of_int |> vl_of_iN
let uop_f32 f f1 = f (vl_to_float32 f1) |> vl_of_float32
let uop_f64 f f1 = f (vl_to_float64 f1) |> vl_of_float64

let catch_ixx_exception f = try f() |> some with
  | RI.Ixx.DivideByZero
  | RI.Ixx.Overflow
  | RI.Convert.InvalidConversion -> none


let ibytes : numerics =
  {
    name = "ibytes";
    (* TODO: Handle the case where n > 16 (i.e. for v128 ) *)
    f =
      (function
      | [ NumV (`Nat n); i ] ->
        let NumV (`Nat i') = as_singleton_case i in
        let rec decompose n bits =
          if n = Z.zero then
            []
          else
            Z.(bits land of_int 0xff) :: decompose Z.(n - of_int 8) Z.(shift_right bits 8)
          in
        assert Z.(n >= Z.zero && rem n (of_int 8) = zero);
        decompose n i' |> List.map vl_of_iN |> listV_of_list
      | vs -> error_values "ibytes" vs
      );
  }

let inv_ibytes : numerics =
  {
    name = "inv_ibytes";
    f =
      (function
      | [ NumV (`Nat n); ListV bs ] ->
          assert (
            (* numtype *)
            n = Z.of_int (Array.length !bs * 8) ||
            (* packtype *)
            (n = Z.of_int 32 && Array.length !bs <= 2)
          );
          vl_of_uN (Array.fold_right (fun b acc ->
            match as_singleton_case b with
            | NumV (`Nat b) when Z.zero <= b && b < Z.of_int 256 -> Z.add b (Z.shift_left acc 8)
            | _ -> error_value "inv_ibytes (byte)" b
          ) !bs Z.zero)
      | vs -> error_values "inv_ibytes" vs
      );
  }


let nbytes : numerics =
  {
    name = "nbytes";
    f =
      (function
      | [ CaseV ([["I32"]], []); n ] -> ibytes.f [ vl_of_nat 32; n ]
      | [ CaseV ([["I64"]], []); n ] -> ibytes.f [ vl_of_nat 64; n ]
      | [ CaseV ([["F32"]], []); f ] -> ibytes.f [ vl_of_nat 32; vl_to_float32 f |> RI.F32.to_bits |> vl_of_uN_32 ]
      | [ CaseV ([["F64"]], []); f ] -> ibytes.f [ vl_of_nat 64; vl_to_float64 f |> RI.F64.to_bits |> vl_of_uN_64 ]
      | vs -> error_values "nbytes" vs
      );
  }
let inv_nbytes : numerics =
  {
    name = "inv_nbytes";
    f =
      (function
      | [ CaseV ([["I32"]], []); l ] -> inv_ibytes.f [ vl_of_nat 32; l ]
      | [ CaseV ([["I64"]], []); l ] -> inv_ibytes.f [ vl_of_nat 64; l ]
      | [ CaseV ([["F32"]], []); l ] -> inv_ibytes.f [ vl_of_nat 32; l ] |> vl_to_uN_32 |> RI.F32.of_bits |> vl_of_float32
      | [ CaseV ([["F64"]], []); l ] -> inv_ibytes.f [ vl_of_nat 64; l ] |> vl_to_uN_64 |> RI.F64.of_bits |> vl_of_float64
      | vs -> error_values "inv_nbytes" vs
      );
  }

let vbytes : numerics =
  {
    name = "vbytes";
    f =
      (function
      | [ CaseV ([["V128"]], []); v ] ->
        let s = v |> as_singleton_case |> vl_to_vec128 |> RI.V128.to_bits in
        Array.init 16 (fun i -> s.[i] |> Char.code |> vl_of_nat |> caseV1) |> listV
      | vs -> error_values "vbytes" vs
      );
  }
let inv_vbytes : numerics =
  {
    name = "inv_vbytes";
    f =
      (function
      | [ CaseV ([["V128"]], []); ListV l ] ->
        let v1 = inv_ibytes.f [ vl_of_nat 64; Array.sub !l 0 8 |> listV ] in
        let v2 = inv_ibytes.f [ vl_of_nat 64; Array.sub !l 8 8 |> listV ] in
        (match as_singleton_case v1, as_singleton_case v2 with
        | NumV (`Nat n1), NumV (`Nat n2) -> vl_of_vec128 (RI.V128.I64x2.of_lanes [ z_to_int64 n1; z_to_int64 n2 ])
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
      | [ CaseV ([["I8" ]], []); l ] -> inv_ibytes.f [ vl_of_nat 8 ; l ]
      | [ CaseV ([["I16"]], []); l ] -> inv_ibytes.f [ vl_of_nat 16; l ]
      | args -> inv_nbytes.f args
      );
  }

let inv_cbytes : numerics =
  {
    name = "inv_cbytes";
    f = function
      | [ CaseV ([["V128"]], []); _ ] as args -> inv_vbytes.f args
      | args -> inv_nbytes.f args
  }

let bytes : numerics = { name = "bytes"; f = nbytes.f }
let inv_bytes : numerics = { name = "inv_bytes"; f = inv_nbytes.f }

let wrap : numerics =
  {
    name = "wrap";
    f =
      (function
        | [ NumV _m; NumV (`Nat n); CaseV ([[];[]], [NumV (`Nat i)]) ] -> vl_of_iN (Z.logand i (maskN n))
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
        let na = Array.map (function
                           | CaseV ([[];[]], [NumV (`Nat e)]) when e = Z.zero || e = Z.one -> e
                           | v -> error_value "bit in inv_ibits" v
                           ) !vs in
        vl_of_iN (Array.fold_left (fun acc e -> Z.logor e (Z.shift_left acc 1)) Z.zero na)
      | vs -> error_values "inv_ibits" vs
      );
  }

let signed : numerics =
  {
    name = "signed";
    f =
      (function
      | [ NumV (`Nat z); NumV (`Nat n) ] ->
        let z = Z.to_int z in
        (if Z.lt n (Z.shift_left Z.one (z - 1)) then n else Z.(sub n (shift_left one z))) |> vl_of_z_int
      | vs -> error_values "signed" vs
      )
  }

let inv_signed =
  {
    name = "inv_signed";
    f =
      (function
      | [ NumV (`Nat z); NumV (`Int n) ] ->
        let z = Z.to_int z in
        (if Z.(geq n zero) then n else Z.(add n (shift_left one z))) |> vl_of_z_nat
      | vs -> error_values "inv_signed" vs
      )
  }

let sat_u : numerics =
  {
    name = "sat_u";
    f =
      (function
      | [ NumV (`Nat z); NumV (`Int i) ] ->
        if Z.(gt i (shift_left one (Z.to_int z) |> pred)) then
          Z.(shift_left one (Z.to_int z) |> pred) |> vl_of_z_nat
        else if Z.(lt i zero) then
          Z.zero |> vl_of_z_nat
        else
          vl_of_z_nat i
      | vs -> error_values "sat_u" vs
      );
  }

let sat_s : numerics =
  {
    name = "sat_s";
    f =
      (function
      | [ NumV (`Nat z); NumV (`Int i) ] ->
        let n = Z.to_int z - 1 in
        let j =
          if Z.(lt i (shift_left one n |> neg)) then
            Z.(shift_left one n |> neg)
          else if Z.(gt i (shift_left one n |> pred)) then
            Z.(shift_left one n |> pred)
          else
            i
        in inv_signed.f [ vl_of_z_nat z; vl_of_z_int j ]
      | vs -> error_values "sat_s" vs
      );
  }

let narrow : numerics =
  {
    name = "narrow";
    f =
      (function
      | [ NumV _ as m; NumV _ as n; CaseV ([["S"]], []) as sx; CaseV ([[];[]], [(NumV _) as i]) ] ->
          sat_s.f [ n; signed.f [ m; i ]]
      | [ NumV _ as m; NumV _ as n; CaseV ([["U"]], []) as sx; CaseV ([[];[]], [(NumV _) as i]) ] ->
          sat_u.f [ n; signed.f [ m; i ]]
      | vs -> error_values "narrow" vs);
  }

let lanes : numerics =
  {
    name = "lanes";
    f =
      (function
      | [ CaseV ([[];["X"];[]], [ CaseV ([["I8"]], []); NumV (`Nat z) ]); v ] when z = Z.of_int 16 ->
        v |> vl_to_vec128 |> RI.V128.I8x16.to_lanes |> List.map vl_of_nat8 |> listV_of_list
      | [ CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); NumV (`Nat z) ]); v ] when z = Z.of_int 8 ->
        v |> vl_to_vec128 |> RI.V128.I16x8.to_lanes |> List.map vl_of_nat16 |> listV_of_list
      | [ CaseV ([[];["X"];[]], [ CaseV ([["I32"]], []); NumV (`Nat z) ]); v ] when z = Z.of_int 4 ->
        v |> vl_to_vec128 |> RI.V128.I32x4.to_lanes |> List.map vl_of_nat32 |> listV_of_list
      | [ CaseV ([[];["X"];[]], [ CaseV ([["I64"]], []); NumV (`Nat z) ]); v ] when z = Z.of_int 2 ->
        v |> vl_to_vec128 |> RI.V128.I64x2.to_lanes |> List.map vl_of_nat64 |> listV_of_list
      | [ CaseV ([[];["X"];[]], [ CaseV ([["F32"]], []); NumV (`Nat z) ]); v ] when z = Z.of_int 4 ->
        v |> vl_to_vec128 |> RI.V128.F32x4.to_lanes |> List.map vl_of_float32 |> listV_of_list
      | [ CaseV ([[];["X"];[]], [ CaseV ([["F64"]], []); NumV (`Nat z) ]); v ] when z = Z.of_int 2 ->
        v |> vl_to_vec128 |> RI.V128.F64x2.to_lanes |> List.map vl_of_float64 |> listV_of_list
      | vs -> error_values "lanes" vs
      );
  }
let inv_lanes : numerics =
  {
    name = "inv_lanes";
    f =
      (function
      | [ CaseV ([[];["X"];[]], [ CaseV ([["I8"]], []); NumV (`Nat z) ]); ListV lanes; ] when z = Z.of_int 16 && Array.length !lanes = 16 ->
        List.map vl_to_int8 (!lanes |> Array.to_list) |> RI.V128.I8x16.of_lanes |> vl_of_vec128
      | [ CaseV ([[];["X"];[]], [ CaseV ([["I16"]], []); NumV (`Nat z) ]); ListV lanes; ] when z = Z.of_int 8 && Array.length !lanes = 8 ->
        List.map vl_to_int16 (!lanes |> Array.to_list) |> RI.V128.I16x8.of_lanes |> vl_of_vec128
      | [ CaseV ([[];["X"];[]], [ CaseV ([["I32"]], []); NumV (`Nat z) ]); ListV lanes; ] when z = Z.of_int 4 && Array.length !lanes = 4 ->
        List.map vl_to_nat32 (!lanes |> Array.to_list) |> RI.V128.I32x4.of_lanes |> vl_of_vec128
      | [ CaseV ([[];["X"];[]], [ CaseV ([["I64"]], []); NumV (`Nat z) ]); ListV lanes; ] when z = Z.of_int 2 && Array.length !lanes = 2 ->
        List.map vl_to_nat64 (!lanes |> Array.to_list) |> RI.V128.I64x2.of_lanes |> vl_of_vec128
      | [ CaseV ([[];["X"];[]], [ CaseV ([["F32"]], []); NumV (`Nat z) ]); ListV lanes; ] when z = Z.of_int 4 && Array.length !lanes = 4 ->
        List.map vl_to_float32 (!lanes |> Array.to_list) |> RI.V128.F32x4.of_lanes |> vl_of_vec128
      | [ CaseV ([[];["X"];[]], [ CaseV ([["F64"]], []); NumV (`Nat z) ]); ListV lanes; ] when z = Z.of_int 2 && Array.length !lanes = 2 ->
        List.map vl_to_float64 (!lanes |> Array.to_list) |> RI.V128.F64x2.of_lanes |> vl_of_vec128
        | vs -> error_values "inv_lanes" vs
      );
  }

let extend : numerics =
  {
    name = "extend";
    f =
      (function
      | [ NumV (`Nat z); _; CaseV ([["U"]], []); v ] when z = Z.of_int 128 ->
        let NumV (`Nat v') = as_singleton_case v in
        RI.V128.I64x2.of_lanes [ z_to_int64 v'; 0L ] |> vl_of_vec128 (* HARDCODE *)
      | [ _; _; CaseV ([["U"]], []); v ] -> v
      | [ NumV _ as m; NumV _ as n; CaseV ([["S"]], []); CaseV ([[];[]], [(NumV _) as i]) ] ->
        inv_signed.f [ n; signed.f [ m; i ] ] |> caseV1
      | vs -> error_values "extend" vs
      );
  }

let reinterpret : numerics =
  {
    name = "reinterpret";
    f =
      (function
      | [ CaseV ([["I32"]], []); CaseV ([["F32"]], []); CaseV ([[];[]], [(NumV _)]) as i ] ->
        i |> vl_to_uN_32 |> RI.Convert.F32_.reinterpret_i32 |> vl_of_float32
      | [ CaseV ([["I64"]], []); CaseV ([["F64"]], []); CaseV ([[];[]], [(NumV _)]) as i ] ->
        i |> vl_to_uN_64 |> RI.Convert.F64_.reinterpret_i64 |> vl_of_float64
      | [ CaseV ([["F32"]], []); CaseV ([["I32"]], []); CaseV _ as i ] ->
        i |> vl_to_float32 |> RI.Convert.I32_.reinterpret_f32 |> vl_of_uN_32
      | [ CaseV ([["F64"]], []); CaseV ([["I64"]], []); CaseV _ as i ] ->
        i |> vl_to_float64 |> RI.Convert.I64_.reinterpret_f64 |> vl_of_uN_64
      | vs -> error_values "reinterpret" vs
      );
  }


let convert : numerics =
  {
    name = "convert";
    f =
      (function
      | [ NumV (`Nat m); NumV (`Nat n); CaseV ([["U"]], []); CaseV ([[];[]], [NumV _ as i]) ] as vs ->
        (match () with
        | () when m = Z.of_int 32 && n = Z.of_int 32 -> i |> vl_to_nat32 |> RI.Convert.F32_.convert_i32_u |> vl_of_float32
        | () when m = Z.of_int 64 && n = Z.of_int 32 -> i |> vl_to_nat64 |> RI.Convert.F32_.convert_i64_u |> vl_of_float32
        | () when m = Z.of_int 32 && n = Z.of_int 64 -> i |> vl_to_nat32 |> RI.Convert.F64_.convert_i32_u |> vl_of_float64
        | () when m = Z.of_int 64 && n = Z.of_int 64 -> i |> vl_to_nat64 |> RI.Convert.F64_.convert_i64_u |> vl_of_float64
        | _ -> error_values "convert" vs
        )
      | [ NumV (`Nat m); NumV (`Nat n); CaseV ([["S"]], []); CaseV ([[];[]], [NumV _ as i]) ] as vs ->
        (match () with
        | () when m = Z.of_int 32 && n = Z.of_int 32 -> i |> vl_to_nat32 |> RI.Convert.F32_.convert_i32_s |> vl_of_float32
        | () when m = Z.of_int 64 && n = Z.of_int 32 -> i |> vl_to_nat64 |> RI.Convert.F32_.convert_i64_s |> vl_of_float32
        | () when m = Z.of_int 32 && n = Z.of_int 64 -> i |> vl_to_nat32 |> RI.Convert.F64_.convert_i32_s |> vl_of_float64
        | () when m = Z.of_int 64 && n = Z.of_int 64 -> i |> vl_to_nat64 |> RI.Convert.F64_.convert_i64_s |> vl_of_float64
        | _ -> error_values "convert" vs
        )
      | vs -> error_values "convert" vs
      );
  }


let promote : numerics =
  {
    name = "promote";
    f = list_f
      (function
      | [ NumV (`Nat m); NumV (`Nat n); CaseV _ as i ] when m = Z.of_int 32 && n = Z.of_int 64 ->
        i |> vl_to_float32 |> RI.Convert.F64_.promote_f32 |> vl_of_float64
      | vs -> error_values "promote" vs
      );
  }

let demote : numerics =
  {
    name = "demote";
    f = list_f
      (function
      | [ NumV (`Nat m); NumV (`Nat n); CaseV _ as i ] when m = Z.of_int 64 && n = Z.of_int 32 ->
        i |> vl_to_float64 |> RI.Convert.F32_.demote_f64 |> vl_of_float32
      | vs -> error_values "demote" vs
      );
  }

let trunc : numerics =
  {
    name = "trunc";
    f =
      let open RI.Convert in
      (function
      | [ NumV (`Nat m); NumV (`Nat n); CaseV ([["U"]], []); CaseV _ as i ] as vs ->
        (match () with
        | () when m = Z.of_int 32 && n = Z.of_int 32 -> (fun _ -> i |> vl_to_float32 |> I32_.trunc_f32_u |> vl_of_uN_32) |> catch_ixx_exception
        | () when m = Z.of_int 64 && n = Z.of_int 32 -> (fun _ -> i |> vl_to_float64 |> I32_.trunc_f64_u |> vl_of_uN_32) |> catch_ixx_exception
        | () when m = Z.of_int 32 && n = Z.of_int 64 -> (fun _ -> i |> vl_to_float32 |> I64_.trunc_f32_u |> vl_of_uN_64) |> catch_ixx_exception
        | () when m = Z.of_int 64 && n = Z.of_int 64 -> (fun _ -> i |> vl_to_float64 |> I64_.trunc_f64_u |> vl_of_uN_64) |> catch_ixx_exception
        | _ -> error_values "trunc" vs
        )
      | [ NumV (`Nat m); NumV (`Nat n); CaseV ([["S"]], []); CaseV _ as i ] as vs ->
        (match () with
        | () when m = Z.of_int 32 && n = Z.of_int 32 -> (fun _ -> i |> vl_to_float32 |> I32_.trunc_f32_s |> vl_of_uN_32) |> catch_ixx_exception
        | () when m = Z.of_int 64 && n = Z.of_int 32 -> (fun _ -> i |> vl_to_float64 |> I32_.trunc_f64_s |> vl_of_uN_32) |> catch_ixx_exception
        | () when m = Z.of_int 32 && n = Z.of_int 64 -> (fun _ -> i |> vl_to_float32 |> I64_.trunc_f32_s |> vl_of_uN_64) |> catch_ixx_exception
        | () when m = Z.of_int 64 && n = Z.of_int 64 -> (fun _ -> i |> vl_to_float64 |> I64_.trunc_f64_s |> vl_of_uN_64) |> catch_ixx_exception
        | _ -> error_values "trunc" vs
        )
      | vs -> error_values "trunc" vs
      );
  }

let trunc_sat : numerics =
  {
    name = "trunc_sat";
    f =
      let open RI.Convert in
      (function
      | [ NumV (`Nat m); NumV (`Nat n); CaseV ([["U"]], []); CaseV _ as i ] as vs ->
        (match () with
        | () when m = Z.of_int 32 && n = Z.of_int 32 -> (fun _ -> i |> vl_to_float32 |> I32_.trunc_sat_f32_u |> vl_of_uN_32) |> catch_ixx_exception
        | () when m = Z.of_int 64 && n = Z.of_int 32 -> (fun _ -> i |> vl_to_float64 |> I32_.trunc_sat_f64_u |> vl_of_uN_32) |> catch_ixx_exception
        | () when m = Z.of_int 32 && n = Z.of_int 64 -> (fun _ -> i |> vl_to_float32 |> I64_.trunc_sat_f32_u |> vl_of_uN_64) |> catch_ixx_exception
        | () when m = Z.of_int 64 && n = Z.of_int 64 -> (fun _ -> i |> vl_to_float64 |> I64_.trunc_sat_f64_u |> vl_of_uN_64) |> catch_ixx_exception
        | _ -> error_values "trunc_sat" vs
        )
      | [ NumV (`Nat m); NumV (`Nat n); CaseV ([["S"]], []); CaseV _ as i ] as vs ->
        (match () with
        | () when m = Z.of_int 32 && n = Z.of_int 32 -> (fun _ -> i |> vl_to_float32 |> I32_.trunc_sat_f32_s |> vl_of_uN_32) |> catch_ixx_exception
        | () when m = Z.of_int 64 && n = Z.of_int 32 -> (fun _ -> i |> vl_to_float64 |> I32_.trunc_sat_f64_s |> vl_of_uN_32) |> catch_ixx_exception
        | () when m = Z.of_int 32 && n = Z.of_int 64 -> (fun _ -> i |> vl_to_float32 |> I64_.trunc_sat_f32_s |> vl_of_uN_64) |> catch_ixx_exception
        | () when m = Z.of_int 64 && n = Z.of_int 64 -> (fun _ -> i |> vl_to_float64 |> I64_.trunc_sat_f64_s |> vl_of_uN_64) |> catch_ixx_exception
        | _ -> error_values "trunc_sat" vs
        )
      | vs -> error_values "trunc_sat" vs
      );
  }

let relaxed_trunc : numerics =
  {
    name = "relaxed_trunc";
    f =
      (function
      | [ NumV _ as m; NumV _ as n; sx; CaseV _ as i ] ->
        trunc_sat.f [m; n; sx; i]  (* use deterministic behaviour *)
      | vs -> error_values "relaxed_trunc" vs
      );
  }


(* FIXME(zilinc): How does it handle poly-functions and their type arguments?
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

let truncz : numerics =
  {
    name = "truncz";
    f =
      (function
      | [ NumV (`Rat q) ] ->
        Q.to_bigint q |> vl_of_z_int
      | vs -> error_values "truncz" vs
      )
  }

let inot : numerics =
  {
    name = "inot";
    f =
      (function
      | [ NumV (`Nat z); m ] ->
        let NumV (`Nat m') = as_singleton_case m in
        Z.(logand (lognot m') (maskN z)) |> vl_of_iN
      | vs -> error_values "inot" vs
      );
  }

let irev : numerics =
  {
    name = "irev";
    f =
      (function
      | [ NumV (`Nat z); m ] ->
        let NumV (`Nat m') = as_singleton_case m in
        let rec loop z m n =
          if z = Z.zero then
            n
          else
            let n' = Z.(logor (shift_left n 1) (logand m one)) in
            loop Z.(sub z one) (Z.shift_right m 1) n'
        in loop z m' Z.zero |> vl_of_iN
      | vs -> error_values "irev" vs
      );
  }

let iand : numerics =
  {
    name = "iand";
    f =
      (function
      | [ NumV (`Nat z); m; n ] ->
        let NumV (`Nat m') = as_singleton_case m in
        let NumV (`Nat n') = as_singleton_case n in
        Z.(logand (logand m' n') (maskN z)) |> vl_of_iN
      | vs -> error_values "iand" vs
      );
  }

let iandnot : numerics =
  {
    name = "iandnot";
    f =
      (function
      | [ NumV (`Nat z); m; n ] ->
        let NumV (`Nat m') = as_singleton_case m in
        let NumV (`Nat n') = as_singleton_case n in
        Z.(logand (logand m' (lognot n')) (maskN z)) |> vl_of_iN
      | vs -> error_values "iandnot" vs
      );
  }

let ior : numerics =
  {
    name = "ior";
    f =
      (function
      | [ NumV (`Nat z); m; n ] ->
        let NumV (`Nat m') = as_singleton_case m in
        let NumV (`Nat n') = as_singleton_case n in
        Z.(logand (logor m' n') (maskN z)) |> vl_of_iN
      | vs -> error_values "ior" vs
      );
  }

let ixor : numerics =
  {
    name = "ixor";
    f =
      (function
      | [ NumV (`Nat z); m; n ] ->
        let NumV (`Nat m') = as_singleton_case m in
        let NumV (`Nat n') = as_singleton_case n in
        Z.(logand (logxor m' n') (maskN z)) |> vl_of_iN
      | vs -> error_values "ixor" vs
      );
  }

let ishl : numerics =
  {
    name = "ishl";
    f =
      (function
      | [ NumV (`Nat z); m; n ] ->
        let NumV (`Nat m') = as_singleton_case m in
        let NumV (`Nat n') = as_singleton_case n in
        Z.(logand (shift_left m' (Z.to_int (rem n' z))) (maskN z)) |> vl_of_iN
      | vs -> error_values "ishl" vs
      );
  }

let ishr : numerics =
  {
    name = "ishr";
    f =
      (function
      | [ NumV (`Nat z); sx; m; n] ->
        let NumV (`Nat m') = as_singleton_case m in
        let NumV (`Nat n') = as_singleton_case n in
        (match match_caseV "sx" sx with
        | [["U"]], [] -> Z.(shift_right m' (Z.to_int (rem n' z))) |> vl_of_iN
        | [["S"]], [] ->
          let n'' = Z.(to_int (rem n' z)) in
          let s = Z.to_int z in
          let d = s - n'' in
          let msb = Z.shift_right m' (s - 1) in
          let pad = Z.(mul (shift_left one s - shift_left one d) msb) in
          Z.(logor pad (shift_right m' n'')) |> vl_of_iN
        | _ -> error_value "sx" sx
        )
      | vs -> error_values "ishr" vs
      );
  }

let irotl : numerics =
  {
    name = "irotl";
    f =
      (function
      | [ NumV (`Nat z); m; n ] ->
        let NumV (`Nat m') = as_singleton_case m in
        let NumV (`Nat n') = as_singleton_case n in
        let n'' = Z.to_int (Z.rem n' z) in
        (Z.logor (Z.logand (Z.shift_left m' n'') (maskN z)) (Z.shift_right m' ((Z.to_int z - n'')))) |> vl_of_iN
      | vs -> error_values "irotl" vs
      );
  }

let irotr : numerics =
  {
    name = "irotr";
    f =
      (function
      | [ NumV (`Nat z); m; n ] ->
        let NumV (`Nat m') = as_singleton_case m in
        let NumV (`Nat n') = as_singleton_case n in
        let n'' = Z.to_int (Z.rem n' z) in
        (Z.logor (Z.shift_right m' n'') (Z.logand (Z.shift_left m' ((Z.to_int z - n''))) (maskN z))) |> vl_of_iN
      | vs -> error_values "irotr" vs
      );
  }

let iclz : numerics =
  {
    name = "iclz";
    f =
      (function
      | [ NumV (`Nat z); m ] ->
        let NumV (`Nat m') = as_singleton_case m in
        if m' = Z.zero then
          z |> vl_of_iN
        else
          let z = Z.to_int z in
          let rec loop acc n =
            if Z.equal (Z.logand n (Z.shift_left Z.one (z - 1))) Z.zero then
              loop (1 + acc) (Z.shift_left n 1)
            else
              acc
          in loop 0 m' |> Z.of_int |> vl_of_iN
      | vs -> error_values "iclz" vs
      );
  }

let ictz : numerics =
  {
    name = "ictz";
    f =
      (function
      | [ NumV (`Nat z); m ] ->
        let NumV (`Nat m') = as_singleton_case m in
        if m' = Z.zero then
          z |> vl_of_iN
        else
          let rec loop acc n =
            if Z.(equal (logand n one) zero) then
              loop (1 + acc) (Z.shift_right n 1)
            else
              acc
          in loop 0 m' |> Z.of_int |> vl_of_iN
      | vs -> error_values "ictz" vs
      );
  }

let ipopcnt : numerics =
  {
    name = "ipopcnt";
    f =
      (function
      | [ NumV (`Nat z); m ] ->
        let NumV (`Nat m') = as_singleton_case m in
        let rec loop acc i n =
          if i = 0 then
            acc
          else
            let acc' = if Z.(equal (logand n one) one) then acc + 1 else acc in
            loop acc' (i - 1) (Z.shift_right n 1)
        in loop 0 (Z.to_int z) m' |> Z.of_int |> vl_of_iN
      | vs -> error_values "ipopcnt" vs
      );
  }

let ilt : numerics =
  {
    name = "ilt";
    f =
      (function
      | [ NumV (`Nat _) as z; sx; CaseV ([[];[]], [m]); CaseV ([[];[]], [n]) ] ->
        let NumV (`Nat m') = m in
        let NumV (`Nat n') = n in
        (match match_caseV "sx" sx with
        | [["U"]], [] -> m' < n' |> int_of_bool |> Z.of_int |> vl_of_uN
        | [["S"]], [] ->
          let m'' = signed.f [ z; m ] |> as_nat_value in
          let n'' = signed.f [ z; n ] |> as_nat_value in
          m'' < n'' |> int_of_bool |> Z.of_int |> vl_of_uN
        | _ -> error_value "sx" sx
        )
      | vs -> error_values "ilt" vs
      );
  }

let igt : numerics =
  {
    name = "igt";
    f =
      (function
      | [ NumV (`Nat _) as z; sx; CaseV ([[];[]], [m]); CaseV ([[];[]], [n]) ] ->
        let NumV (`Nat m') = m in
        let NumV (`Nat n') = n in
        (match match_caseV "sx" sx with
        | [["U"]], [] -> m' > n' |> int_of_bool |> Z.of_int |> vl_of_uN
        | [["S"]], [] ->
          let m'' = signed.f [ z; m ] |> as_nat_value in
          let n'' = signed.f [ z; n ] |> as_nat_value in
          m'' > n'' |> int_of_bool |> Z.of_int |> vl_of_uN
        | _ -> error_value "sx" sx
        )
      | vs -> error_values "igt" vs
      );
  }

let ibitselect : numerics =
  {
    name = "ibitselect";
    f =
      (function
      | [ NumV (`Nat _) as z; i1; i2; i3] ->
        let NumV (`Nat _) = as_singleton_case i1 in
        let NumV (`Nat _) = as_singleton_case i2 in
        let NumV (`Nat _) = as_singleton_case i3 in
        ior.f [ z; iand.f [ z; i1; i3 ]; iand.f [ z; i2; inot.f [ z; i3 ]]]
      | vs -> error_values "ibitselect" vs
      );
  }

let irelaxed_laneselect : numerics =
  {
    name = "irelaxed_laneselect";
    f =
      (function
      | [ NumV (`Nat _) as z; n1; n2; n3] ->
        let NumV (`Nat _) = as_singleton_case n1 in
        let NumV (`Nat _) = as_singleton_case n2 in
        let NumV (`Nat _) = as_singleton_case n3 in
        ibitselect.f [ z; n1; n2; n3 ] |> singleton (* use deterministic behaviour *)
      | vs -> error_values "irelaxed_laneselect" vs
      );
  }

let imin : numerics =
  {
    name = "imin";
    f =
      (function
      | [ NumV (`Nat _) as z; CaseV _ as sx; m; n] ->
        let NumV (`Nat _) = as_singleton_case m in
        let NumV (`Nat _) = as_singleton_case n in
        (if as_nat_value (ilt.f [ z; sx; m; n ]) = Z.one then m else n)
      | vs -> error_values "imin" vs
      );
  }

let imax : numerics =
  {
    name = "imax";
    f =
      (function
      | [ NumV (`Nat _) as z; CaseV _ as sx; m; n] ->
        let NumV (`Nat _) = as_singleton_case m in
        let NumV (`Nat _) = as_singleton_case n in
        (if as_nat_value (igt.f [ z; sx; m; n ]) = Z.one then m else n)
      | vs -> error_values "imax" vs
      );
  }

let iavgr : numerics =
  {
    name = "iavgr";
    f =
      (function
      | [ NumV (`Nat _) as z; sx; m; n] ->
        let NumV (`Nat m') = as_singleton_case m in
        let NumV (`Nat n') = as_singleton_case n in
        (match match_caseV "sx" sx with
        | [["U"]], [] ->  Z.((m' + n' + one) / of_int 2) |> vl_of_iN
        | [["S"]], [] ->
          let m'' = signed.f [ z; natV m' ] |> as_int_value in
          let n'' = signed.f [ z; natV n' ] |> as_int_value in
          Z.((m'' + n'' + one) / Z.of_int 2) |> vl_of_iN
        | _ -> error_value "sx" sx
        )
      | vs -> error_values "iavgr" vs
      );
  }


let iq15mulr_sat : numerics =
  {
    name = "iq15mulr_sat";
    f =
      (function
      | [ NumV (`Nat _) as z; sx; m; n] ->
        let NumV (`Nat _) = as_singleton_case m in
        let NumV (`Nat _) = as_singleton_case n in
        let m' = signed.f [ z; m ] |> as_int_value in
        let n' = signed.f [ z; n ] |> as_int_value in
        (match match_caseV "sx" sx with
        | [["U"]], _ -> sat_u.f [ z; sx; Z.(shift_right (mul m' n' + of_int 0x4000) 15) |> intV ]
        | [["S"]], _ -> sat_s.f [ z; sx; Z.(shift_right (mul m' n' + of_int 0x4000) 15) |> intV ]
        | _ -> error_value "sx" sx
        )
      | vs -> error_values "iq15mulr_sat" vs
      );
  }

let irelaxed_q15mulr : numerics =
  {
    name = "irelaxed_q15mulr";
    f =
      (function
      | [ NumV (`Nat _) as z; sx; m; n] ->
        iq15mulr_sat.f [z; sx; m; n] |> singleton (* use deterministic behaviour *)
      | vs -> error_values "irelaxed_q15mulr" vs
      );
  }


let fadd : numerics =
  {
    name = "fadd";
    f = list_f
      (function
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 32 ->
        bop_f32 RI.F32.add f1 f2
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 64 ->
        bop_f64 RI.F64.add f1 f2
      | vs -> error_values "fadd" vs
      );
  }
let fsub : numerics =
  {
    name = "fsub";
    f = list_f
      (function
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 32 ->
        bop_f32 RI.F32.sub f1 f2
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 64 ->
        bop_f64 RI.F64.sub f1 f2
      | vs -> error_values "fsub" vs
      );
  }
let fmul : numerics =
  {
    name = "fmul";
    f = list_f
      (function
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 32 ->
        bop_f32 RI.F32.mul f1 f2
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 64 ->
        bop_f64 RI.F64.mul f1 f2
      | vs -> error_values "fmul" vs
      );
  }
let fdiv : numerics =
  {
    name = "fdiv";
    f = list_f
      (function
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 32 ->
        bop_f32 RI.F32.div f1 f2
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 64 ->
        bop_f64 RI.F64.div f1 f2
      | vs -> error_values "fdiv" vs
      );
  }
let fmin : numerics =
  {
    name = "fmin";
    f = list_f
      (function
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 32 ->
        bop_f32 RI.F32.min f1 f2
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 64 ->
        bop_f64 RI.F64.min f1 f2
      | vs -> error_values "fmin" vs
      );
  }
let fmax : numerics =
  {
    name = "fmax";
    f = list_f
      (function
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 32 ->
        bop_f32 RI.F32.max f1 f2
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 64 ->
        bop_f64 RI.F64.max f1 f2
      | vs -> error_values "fmax" vs
      );
  }
let fcopysign : numerics =
  {
    name = "fcopysign";
    f = list_f
      (function
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 32 ->
        bop_f32 RI.F32.copysign f1 f2
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 64 ->
        bop_f64 RI.F64.copysign f1 f2
      | vs -> error_values "fcopysign" vs
      );
  }
let fabs : numerics =
  {
    name = "fabs";
    f = list_f
      (function
      | [ NumV (`Nat z); CaseV _ as f ] when z = Z.of_int 32 ->
        uop_f32 RI.F32.abs f
      | [ NumV (`Nat z); CaseV _ as f ] when z = Z.of_int 64 ->
        uop_f64 RI.F64.abs f
      | vs -> error_values "fabs" vs
      );
  }
let fneg : numerics =
  {
    name = "fneg";
    f = list_f
      (function
      | [ NumV (`Nat z); CaseV _ as f ] when z = Z.of_int 32 ->
        uop_f32 RI.F32.neg f
      | [ NumV (`Nat z); CaseV _ as f ] when z = Z.of_int 64 ->
        uop_f64 RI.F64.neg f
      | vs -> error_values "fneg" vs
      );
  }
let fsqrt : numerics =
  {
    name = "fsqrt";
    f = list_f
      (function
      | [ NumV (`Nat z); CaseV _ as f ] when z = Z.of_int 32 ->
        uop_f32 RI.F32.sqrt f
      | [ NumV (`Nat z); CaseV _ as f ] when z = Z.of_int 64 ->
        uop_f64 RI.F64.sqrt f
      | vs -> error_values "fsqrt" vs
      );
  }
let fceil : numerics =
  {
    name = "fceil";
    f = list_f
      (function
      | [ NumV (`Nat z); CaseV _ as f ] when z = Z.of_int 32 ->
        uop_f32 RI.F32.ceil f
      | [ NumV (`Nat z); CaseV _ as f ] when z = Z.of_int 64 ->
        uop_f64 RI.F64.ceil f
      | vs -> error_values "fceil" vs
      );
  }
let ffloor : numerics =
  {
    name = "ffloor";
    f = list_f
      (function
      | [ NumV (`Nat z); CaseV _ as f ] when z = Z.of_int 32 ->
        uop_f32 RI.F32.floor f
      | [ NumV (`Nat z); CaseV _ as f ] when z = Z.of_int 64 ->
        uop_f64 RI.F64.floor f
      | vs -> error_values "ffloor" vs
      );
  }
let ftrunc : numerics =
  {
    name = "ftrunc";
    f = list_f
      (function
      | [ NumV (`Nat z); CaseV _ as f ] when z = Z.of_int 32 ->
        uop_f32 RI.F32.trunc f
      | [ NumV (`Nat z); CaseV _ as f ] when z = Z.of_int 64 ->
        uop_f64 RI.F64.trunc f
      | vs -> error_values "ftrunc" vs
      );
  }
let fnearest : numerics =
  {
    name = "fnearest";
    f = list_f
      (function
      | [ NumV (`Nat z); CaseV _ as f ] when z = Z.of_int 32 ->
        uop_f32 RI.F32.nearest f
      | [ NumV (`Nat z); CaseV _ as f ] when z = Z.of_int 64 ->
        uop_f64 RI.F64.nearest f
      | vs -> error_values "fnearest" vs
      );
  }
let feq : numerics =
  {
    name = "feq";
    f =
      (function
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 32 ->
        bop_f32_b RI.F32.eq f1 f2
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 64 ->
        bop_f64_b RI.F64.eq f1 f2
      | vs -> error_values "feq" vs
      );
  }
let fne : numerics =
  {
    name = "fne";
    f =
      (function
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 32 ->
        bop_f32_b RI.F32.ne f1 f2
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 64 ->
        bop_f64_b RI.F64.ne f1 f2
      | vs -> error_values "fne" vs
      );
  }
let flt : numerics =
  {
    name = "flt";
    f =
      (function
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 32 ->
        bop_f32_b RI.F32.lt f1 f2
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 64 ->
        bop_f64_b RI.F64.lt f1 f2
      | vs -> error_values "flt" vs
      );
  }
let fgt : numerics =
  {
    name = "fgt";
    f =
      (function
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 32 ->
        bop_f32_b RI.F32.gt f1 f2
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 64 ->
        bop_f64_b RI.F64.gt f1 f2
      | vs -> error_values "fgt" vs
      );
  }
let fle : numerics =
  {
    name = "fle";
    f =
      (function
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 32 ->
        bop_f32_b RI.F32.le f1 f2
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 64 ->
        bop_f64_b RI.F64.le f1 f2
      | vs -> error_values "fle" vs
      );
  }
let fge : numerics =
  {
    name = "fge";
    f =
      (function
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 32 ->
        bop_f32_b RI.F32.ge f1 f2
      | [ NumV (`Nat z); CaseV _ as f1; CaseV _ as f2; ] when z = Z.of_int 64 ->
        bop_f64_b RI.F64.ge f1 f2
      | vs -> error_values "fge" vs
      );
  }
let fpmin : numerics =
  {
    name = "fpmin";
    f = list_f
      (function
      | [ NumV _ as z; CaseV _ as f1; CaseV _ as f2; ] ->
        if (flt.f [ z; f2; f1 ] |> as_singleton_case |> as_nat_value = Z.one) then f2 else f1
      | vs -> error_values "fpmin" vs
      );
  }
let fpmax : numerics =
  {
    name = "fpmax";
    f = list_f
      (function
      | [ NumV _ as z; CaseV _ as f1; CaseV _ as f2; ] ->
        if (flt.f [ z; f1; f2 ] |> as_singleton_case |> as_nat_value = Z.one) then f2 else f1
      | vs -> error_values "fpmax" vs
      );
  }
let frelaxed_min : numerics =
  {
    name = "frelaxed_min";
    f =
      (function
      | [ NumV _ as z; CaseV _ as f1; CaseV _ as f2; ] ->
        fmin.f [ z; f1; f2 ]  (* use deterministic behaviour *)
      | vs -> error_values "frelaxed_min" vs
      );
  }
let frelaxed_max : numerics =
  {
    name = "frelaxed_max";
    f =
      (function
      | [ NumV _ as z; CaseV _ as f1; CaseV _ as f2; ] ->
        fmax.f [ z; f1; f2 ]  (* use deterministic behaviour *)
      | vs -> error_values "frelaxed_max" vs
      );
  }

let frelaxed_madd : numerics =
  {
    name = "frelaxed_madd";
    f =
      (function
      | [ NumV _ as z; CaseV _ as f1; CaseV _ as f2; CaseV _ as f3 ] ->
        fadd.f [ z; unlist_f fmul.f [ z; f1; f2 ]; f3 ]  (* use deterministic behaviour *)
      | vs -> error_values "frelaxed_madd" vs
      );
  }
let frelaxed_nmadd : numerics =
  {
    name = "frelaxed_nmadd";
    f =
      (function
      | [ NumV _ as z; CaseV _ as f1; CaseV _ as f2; CaseV _ as f3 ] ->
        frelaxed_madd.f [ z; unlist_f fneg.f [ z; f1 ]; f2; f3 ]  (* use deterministic behaviour *)
      | vs -> error_values "frelaxed_nmadd" vs
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
  nbytes;
  vbytes;
  inv_nbytes;
  inv_vbytes;
  inv_zbytes;
  inv_cbytes;
  bytes;
  inv_bytes;
  inv_ibits;
  (*
  inv_concat;
  inv_concatn;
  *)
  wrap;
  narrow;
  lanes;
  inv_lanes;
  truncz;
  sat_u;
  sat_s;
  extend;
  reinterpret;
  convert;
  promote;
  demote;
  trunc;
  trunc_sat;
  relaxed_trunc;
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
