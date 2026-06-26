theory reference_isabelle_output_wasm3
(* Imported Code *)
	imports Main
begin

inductive list_all3 :: "('a ⇒ 'b ⇒ 'c ⇒ bool) ⇒ 'a list ⇒ 'b list ⇒ 'c list ⇒ bool" where
	list_all3_nil : "list_all3 R [] [] []" |
	list_all3_cons: "R a b c ⟹ list_all3 R as bs cs ⟹ list_all3 R (a # as) (b # bs) (c # cs)"

definition list_zipWith :: "('a ⇒ 'b ⇒ 'c) ⇒ 'a list ⇒ 'b list ⇒ 'c list" where
	"list_zipWith f xs ys = map (λ (x, y). f x y) (zip xs ys)"

definition list_map3 :: "('a ⇒ 'b ⇒ 'c ⇒ 'd) ⇒ 'a list ⇒ 'b list ⇒ 'c list ⇒ 'd list" where
	"list_map3 f xs ys zs = map (λ (x, (y, z)). f x y z) (zip xs (zip ys zs))"

inductive foralli_help :: "(nat ⇒ 'a ⇒ bool) ⇒ nat ⇒ 'a list ⇒ bool" where
	foralli_nil : "foralli_help f n []" |
	foralli_cons : "f n x ⟹ foralli_help f (n + 1) l ⟹ foralli_help f n (x # l)"

definition list_foralli :: "(nat ⇒ 'a ⇒ bool) ⇒ 'a list ⇒ bool" where
	"list_foralli f xs = foralli_help f 0 xs"

fun option_zipWith :: "('a ⇒ 'b ⇒ 'c) ⇒ 'a option ⇒ 'b option ⇒ 'c option" where
	"option_zipWith f (Some x) (Some y) = Some (f x y)" |
	"option_zipWith _ _ _ = None"

fun option_map3 :: "('a ⇒ 'b ⇒ 'c ⇒ 'd) ⇒ 'a option ⇒ 'b option ⇒ 'c option ⇒ 'd option" where
	"option_map3 f (Some x) (Some y) (Some z) = Some (f x y z)" |
	"option_map3 f _ _ _ = None"

fun option_to_list :: "'a option ⇒'a list" where
	"option_to_list None = []" |
	"option_to_list (Some a) = [a]"

fun list_slice :: "'a list ⇒ nat ⇒ nat ⇒ 'a list" where
	"list_slice [] _ _ = []" |
	"list_slice (x # l) 0 0 = []" |
	"list_slice (x # l) (Suc n) 0 = []" |
	"list_slice (x # l) 0 (Suc m) = x # list_slice l 0 m" |
	"list_slice (x # l) (Suc n) m = list_slice l n m"

fun mkseq :: "(nat ⇒ 'a) ⇒ nat ⇒'a list" where
	"mkseq _ 0 = []" |
	"mkseq f (Suc n) = mkseq f n @ [f n]"

fun repeat :: "nat ⇒ 'a ⇒ 'a list" where
	"repeat 0 _ = []" |
	"repeat (Suc n) x = x # repeat n x"

fun list_update_func :: "'a list ⇒ nat ⇒ ('a ⇒ 'a) ⇒ 'a list" where
	"list_update_func [] _ _ = []" |
	"list_update_func (x # l) 0 y = (y x) # l" |
	"list_update_func (x # l) (Suc n) y = x # list_update_func l n y"

fun list_slice_update :: "'a list ⇒ nat ⇒ nat ⇒ 'a list ⇒ 'a list" where
	"list_slice_update [] _ _ _ = []" |
	"list_slice_update l _ _ [] = l" |
	"list_slice_update (x # l) _ 0 _ = []" |
	"list_slice_update (x # l) 0 (Suc m) (y # ul) = y # list_slice_update l 0 m ul" |
	"list_slice_update (x # l) (Suc n) m ul = x # list_slice_update l n m ul"

fun option_append :: "'a option ⇒ 'a option ⇒ 'a option" (infixl "@@@" 70) where
	"option_append (Some x) _ = Some x" |
	"option_append None y = y"

(* Generated Code *)
(* Type Alias Definition at: ../specification/wasm-3.0/0.1-aux.vars.spectec:5.1-5.32 *)
type_synonym N = "nat"

(* Type Alias Definition at: ../specification/wasm-3.0/0.1-aux.vars.spectec:6.1-6.32 *)
type_synonym M = "nat"

(* Type Alias Definition at: ../specification/wasm-3.0/0.1-aux.vars.spectec:7.1-7.32 *)
type_synonym K = "nat"

(* Type Alias Definition at: ../specification/wasm-3.0/0.1-aux.vars.spectec:8.1-8.32 *)
type_synonym n = "nat"

(* Type Alias Definition at: ../specification/wasm-3.0/0.1-aux.vars.spectec:9.1-9.32 *)
type_synonym m = "nat"

(* Auxiliary Definition at: ../specification/wasm-3.0/0.2-aux.num.spectec:5.1-5.25 *)
function (sequential) min :: "nat ⇒ nat ⇒ nat" where
		  "min i j = (if (i ≤ j) then i else j)"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/0.2-aux.num.spectec:9.1-9.56 *)
inductive fun_sum :: "(nat list) ⇒ nat ⇒ bool" where
	  fun_sum_case_0 :
		"fun_sum [] 0"
	| fun_sum_case_1 :
		"(fun_sum n'_lst var_0) ⟹
		 fun_sum ([v_n] @ n'_lst) (v_n + var_0)"

(* Mutual Recursion at: ../specification/wasm-3.0/0.2-aux.num.spectec:13.1-13.57 *)
inductive fun_prod :: "(nat list) ⇒ nat ⇒ bool" where
	  fun_prod_case_0 :
		"fun_prod [] 1"
	| fun_prod_case_1 :
		"(fun_prod n'_lst var_0) ⟹
		 fun_prod ([v_n] @ n'_lst) (v_n * var_0)"

(* Auxiliary Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:7.1-7.58 *)
function (sequential) opt_underscore :: "('X list) ⇒ (('X option) option)" where
		  "opt_underscore  [] = (Some None)"
		| "opt_underscore  [w] = (Some (Some w))"
		| "opt_underscore  x1 = None"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/0.3-aux.seq.spectec:14.1-14.82 *)
function (sequential) concat_underscore :: "(('X list) list) ⇒ ('X list)" where
		  "concat_underscore  [] = []"
		| "concat_underscore  (w_lst # w'_lst_lst) = (w_lst @ (concat_underscore  w'_lst_lst))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/0.3-aux.seq.spectec:18.1-18.89 *)
axiomatization concatn_underscore :: "(('X list) list) ⇒ nat ⇒ ('X list)"

(* Auxiliary Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:22.1-22.58 *)
function (sequential) concatopt_underscore :: "(('X option) list) ⇒ ('X list)" where
		  "concatopt_underscore  [] = []"
		| "concatopt_underscore  (w_opt # w'_opt_lst) = ((option_to_list w_opt) @ (concat_underscore  (map (λ (w'_opt :: ('X option)). (option_to_list w'_opt)) w'_opt_lst)))"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:26.1-26.39 *)
axiomatization inv_concat_underscore :: "('X list) ⇒ (('X list) list)"

(* Axiom Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:29.1-29.45 *)
axiomatization inv_concatn_underscore :: "nat ⇒ ('X list) ⇒ (('X list) list)"

(* Mutual Recursion at: ../specification/wasm-3.0/0.3-aux.seq.spectec:35.1-35.78 *)
function (sequential) disjoint_underscore :: "('X list) ⇒ bool" where
		  "disjoint_underscore  [] = True"
		| "disjoint_underscore  (w # w'_lst) = ((~ (w ∈ set w'_lst)) ∧ (disjoint_underscore  w'_lst))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/0.3-aux.seq.spectec:40.1-40.38 *)
function (sequential) setminus1_underscore :: "'X ⇒ ('X list) ⇒ ('X list)" where
		  "setminus1_underscore  w [] = [w]"
		| "setminus1_underscore  w (w_1 # w'_lst) = (if (w = w_1) then [] else (setminus1_underscore  w w'_lst))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/0.3-aux.seq.spectec:39.1-39.56 *)
function (sequential) setminus_underscore :: "('X list) ⇒ ('X list) ⇒ ('X list)" where
		  "setminus_underscore  [] w_lst = []"
		| "setminus_underscore  (w_1 # w'_lst) w_lst = ((setminus1_underscore  w_1 w_lst) @ (setminus_underscore  w'_lst w_lst))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/0.3-aux.seq.spectec:51.1-51.46 *)
function (sequential) setproduct2_underscore :: "'X ⇒ (('X list) list) ⇒ (('X list) list)" where
		  "setproduct2_underscore  w_1 [] = []"
		| "setproduct2_underscore  w_1 (w'_lst # w_lst_lst) = ([([w_1] @ w'_lst)] @ (setproduct2_underscore  w_1 w_lst_lst))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/0.3-aux.seq.spectec:50.1-50.47 *)
function (sequential) setproduct1_underscore :: "('X list) ⇒ (('X list) list) ⇒ (('X list) list)" where
		  "setproduct1_underscore  [] w_lst_lst = []"
		| "setproduct1_underscore  (w_1 # w'_lst) w_lst_lst = ((setproduct2_underscore  w_1 w_lst_lst) @ (setproduct1_underscore  w'_lst w_lst_lst))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/0.3-aux.seq.spectec:49.1-49.84 *)
function (sequential) setproduct_underscore :: "(('X list) list) ⇒ (('X list) list)" where
		  "setproduct_underscore  [] = [[]]"
		| "setproduct_underscore  (w_1_lst # w_lst_lst) = (setproduct1_underscore  w_1_lst (setproduct_underscore  w_lst_lst))"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-3.0/1.0-syntax.profiles.spectec:5.1-5.29 *)
axiomatization ND :: "bool"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:7.1-7.37 *)
datatype bit =
	  mk_bit "nat"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:7.8-7.11 *)
inductive wf_bit :: "bit ⇒ bool" where
	  bit_case_0 :
		"((i = 0) ∨ (i = 1)) ⟹
		 wf_bit (mk_bit i)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:8.1-8.50 *)
datatype byte =
	  mk_byte "nat"
	

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:8.1-8.50 *)
function (sequential) proj_byte_0 :: "byte ⇒ (nat)" where
		  "proj_byte_0 (mk_byte v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:8.8-8.12 *)
inductive wf_byte :: "byte ⇒ bool" where
	  byte_case_0 :
		"((i ≥ 0) ∧ (i ≤ 255)) ⟹
		 wf_byte (mk_byte i)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:10.1-11.25 *)
datatype uN =
	  mk_uN "nat"
	

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:10.1-11.25 *)
function (sequential) proj_uN_0 :: "uN ⇒ (nat)" where
		  "proj_uN_0 (mk_uN v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:10.8-10.11 *)
inductive wf_uN :: "N ⇒ uN ⇒ bool" where
	  uN_case_0 :
		"((i ≥ 0) ∧ (i ≤ ((((2 ^ v_N) :: nat) - (1 :: nat)) :: nat))) ⟹
		 wf_uN v_N (mk_uN i)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:12.1-13.50 *)
datatype sN =
	  mk_sN "nat"
	

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:12.1-13.50 *)
function (sequential) proj_sN_0 :: "sN ⇒ (nat)" where
		  "proj_sN_0 (mk_sN v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:12.8-12.11 *)
inductive wf_sN :: "N ⇒ sN ⇒ bool" where
	  sN_case_0 :
		"((((i ≥ (0 - ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat))) ∧ (i ≤ (0 - (1 :: nat)))) ∨ (i = (0 :: nat))) ∨ ((i ≥ ((1 :: nat))) ∧ (i ≤ ((((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat)) - (1 :: nat))))) ⟹
		 wf_sN v_N (mk_sN i)"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:14.1-15.8 *)
type_synonym iN = "uN"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:17.1-17.20 *)
type_synonym u8 = "uN"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:18.1-18.21 *)
type_synonym u16 = "uN"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:19.1-19.21 *)
type_synonym u31 = "uN"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:20.1-20.21 *)
type_synonym u32 = "uN"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:21.1-21.21 *)
type_synonym u64 = "uN"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:22.1-22.21 *)
type_synonym s33 = "sN"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:23.1-23.21 *)
type_synonym i32 = "iN"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:24.1-24.21 *)
type_synonym i64 = "iN"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:25.1-25.23 *)
type_synonym i128 = "iN"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:32.1-32.35 *)
function (sequential) signif :: "N ⇒ (nat option)" where
		  "signif (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some 23)"
		| "signif (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some 52)"
		| "signif x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:36.1-36.34 *)
function (sequential) expon :: "N ⇒ (nat option)" where
		  "expon (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some 8)"
		| "expon (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some 11)"
		| "expon x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:40.1-40.47 *)
function (sequential) fun_M :: "N ⇒ nat" where
		  "fun_M v_N = (the ((signif v_N)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:43.1-43.47 *)
function (sequential) E :: "N ⇒ nat" where
		  "E v_N = (the ((expon v_N)))"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:50.1-50.47 *)
type_synonym exp = "nat"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:51.1-55.84 *)
datatype fNmag =
	  NORM "m" "exp"
	| SUBNORM "m"
	| res_INF
	| NAN "m"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:51.8-51.14 *)
inductive wf_fNmag :: "N ⇒ fNmag ⇒ bool" where
	  fNmag_case_0 :
		"((v_m < (2 ^ (fun_M v_N))) ∧ ((((2 :: nat) - ((2 ^ ((((E v_N) :: nat) - (1 :: nat)) :: nat)) :: nat)) ≤ v_exp) ∧ (v_exp ≤ (((2 ^ ((((E v_N) :: nat) - (1 :: nat)) :: nat)) :: nat) - (1 :: nat))))) ⟹
		 wf_fNmag v_N (NORM v_m v_exp)"
	| fNmag_case_1 :
		"((v_m < (2 ^ (fun_M v_N))) ∧ (((2 :: nat) - ((2 ^ ((((E v_N) :: nat) - (1 :: nat)) :: nat)) :: nat)) = v_exp)) ⟹
		 wf_fNmag v_N (SUBNORM v_m)"
	| fNmag_case_2 :
		"wf_fNmag v_N res_INF"
	| fNmag_case_3 :
		"((1 ≤ v_m) ∧ (v_m < (2 ^ (fun_M v_N)))) ⟹
		 wf_fNmag v_N (NAN v_m)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:46.1-48.35 *)
datatype fN =
	  POS "fNmag"
	| NEG "fNmag"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:46.8-46.11 *)
inductive wf_fN :: "N ⇒ fN ⇒ bool" where
	  fN_case_0 :
		"(wf_fNmag v_N var_0) ⟹
		 wf_fN v_N (POS var_0)"
	| fN_case_1 :
		"(wf_fNmag v_N var_0) ⟹
		 wf_fN v_N (NEG var_0)"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:57.1-57.21 *)
type_synonym f32 = "fN"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:58.1-58.21 *)
type_synonym f64 = "fN"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:60.1-60.39 *)
function (sequential) fzero :: "N ⇒ fN" where
		  "fzero v_N = (POS (SUBNORM 0))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:63.1-63.44 *)
function (sequential) fnat :: "N ⇒ nat ⇒ fN" where
		  "fnat v_N v_n = (POS (NORM v_n (0 :: nat)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:66.1-66.39 *)
function (sequential) fone :: "N ⇒ fN" where
		  "fone v_N = (POS (NORM 1 (0 :: nat)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:69.1-69.21 *)
function (sequential) canon_underscore :: "N ⇒ nat" where
		  "canon_underscore v_N = (2 ^ ((((the ((signif v_N))) :: nat) - (1 :: nat)) :: nat))"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:75.1-76.8 *)
type_synonym vN = "uN"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:78.1-78.23 *)
type_synonym v128 = "vN"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:84.1-84.49 *)
datatype 'X res_list  =
	  mk_list "('X list)"
	

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:84.1-84.49 *)
function (sequential) proj_list_0 :: "('X res_list) ⇒ (('X list))" where
		  "proj_list_0  (mk_list v_X_list_0) = (v_X_list_0)"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:89.1-89.85 *)
datatype res_char =
	  mk_char "nat"
	

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:89.1-89.85 *)
function (sequential) proj_char_0 :: "res_char ⇒ (nat)" where
		  "proj_char_0 (mk_char v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:89.8-89.12 *)
inductive wf_char :: "res_char ⇒ bool" where
	  char_case_0 :
		"(((i ≥ 0) ∧ (i ≤ 55295)) ∨ ((i ≥ 57344) ∧ (i ≤ 1114111))) ⟹
		 wf_char (mk_char i)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/5.1-binary.values.spectec:48.6-48.11 *)
inductive fun_cont :: "byte ⇒ nat ⇒ bool" where
	  fun_cont_case_0 :
		"((128 < (proj_byte_0 b)) ∧ ((proj_byte_0 b) < 192)) ⟹
		 fun_cont b ((((proj_byte_0 b) :: nat) - (128 :: nat)) :: nat)"

(* Mutual Recursion at: ../specification/wasm-3.0/1.1-syntax.values.spectec:91.1-91.25 *)
inductive fun_utf8 :: "(res_char list) ⇒ (byte list) ⇒ bool" where
	  fun_utf8_case_0 :
		"((length var_0_lst) = (length ch_lst)) ⟹
		 list_all2 (λ (var_0 :: (byte list)) (ch :: res_char). (fun_utf8 [ch] var_0)) var_0_lst ch_lst ⟹
		 fun_utf8 ch_lst (concat_underscore  var_0_lst)"
	| fun_utf8_case_1 :
		"(wf_byte (mk_byte (proj_char_0 ch))) ⟹
		 ((proj_char_0 ch) < 128) ⟹
		 ((mk_byte (proj_char_0 ch)) = b) ⟹
		 fun_utf8 [ch] [b]"
	| fun_utf8_case_2 :
		"(fun_cont b_2 var_0) ⟹
		 ((128 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 2048)) ⟹
		 ((proj_char_0 ch) = (((2 ^ 6) * ((((proj_byte_0 b_1) :: nat) - (192 :: nat)) :: nat)) + var_0)) ⟹
		 fun_utf8 [ch] [b_1, b_2]"
	| fun_utf8_case_3 :
		"(fun_cont b_3 var_1) ⟹
		 (fun_cont b_2 var_0) ⟹
		 (((2048 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 55296)) ∨ ((57344 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 65536))) ⟹
		 ((proj_char_0 ch) = ((((2 ^ 12) * ((((proj_byte_0 b_1) :: nat) - (224 :: nat)) :: nat)) + ((2 ^ 6) * var_0)) + var_1)) ⟹
		 fun_utf8 [ch] [b_1, b_2, b_3]"
	| fun_utf8_case_4 :
		"(fun_cont b_4 var_2) ⟹
		 (fun_cont b_3 var_1) ⟹
		 (fun_cont b_2 var_0) ⟹
		 ((65536 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 69632)) ⟹
		 ((proj_char_0 ch) = (((((2 ^ 18) * ((((proj_byte_0 b_1) :: nat) - (240 :: nat)) :: nat)) + ((2 ^ 12) * var_0)) + ((2 ^ 6) * var_1)) + var_2)) ⟹
		 fun_utf8 [ch] [b_1, b_2, b_3, b_4]"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:93.1-93.70 *)
datatype name =
	  mk_name "(res_char list)"
	

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:93.1-93.70 *)
function (sequential) proj_name_0 :: "name ⇒ ((res_char list))" where
		  "proj_name_0 (mk_name v_char_list_0) = (v_char_list_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:93.8-93.12 *)
inductive wf_name :: "name ⇒ bool" where
	  name_case_0 :
		"(fun_utf8 char_lst var_0) ⟹
		 list_all (λ (v_char :: res_char). (wf_char v_char)) char_lst ⟹
		 ((length var_0) < (2 ^ 32)) ⟹
		 wf_name (mk_name char_lst)"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:100.1-100.36 *)
type_synonym idx = "u32"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:101.1-101.44 *)
type_synonym laneidx = "u8"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:103.1-103.45 *)
type_synonym typeidx = "idx"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:104.1-104.49 *)
type_synonym funcidx = "idx"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:105.1-105.49 *)
type_synonym globalidx = "idx"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:106.1-106.47 *)
type_synonym tableidx = "idx"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:107.1-107.46 *)
type_synonym memidx = "idx"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:108.1-108.43 *)
type_synonym tagidx = "idx"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:109.1-109.45 *)
type_synonym elemidx = "idx"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:110.1-110.45 *)
type_synonym dataidx = "idx"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:111.1-111.47 *)
type_synonym labelidx = "idx"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:112.1-112.47 *)
type_synonym localidx = "idx"

(* Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:113.1-113.47 *)
type_synonym fieldidx = "idx"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:115.1-116.79 *)
datatype externidx =
	  FUNC "funcidx"
	| GLOBAL "globalidx"
	| TABLE "tableidx"
	| MEM "memidx"
	| TAG "tagidx"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:115.8-115.17 *)
inductive wf_externidx :: "externidx ⇒ bool" where
	  externidx_case_0 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_externidx (FUNC v_funcidx)"
	| externidx_case_1 :
		"(wf_uN 32 v_globalidx) ⟹
		 wf_externidx (GLOBAL v_globalidx)"
	| externidx_case_2 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_externidx (TABLE v_tableidx)"
	| externidx_case_3 :
		"(wf_uN 32 v_memidx) ⟹
		 wf_externidx (MEM v_memidx)"
	| externidx_case_4 :
		"(wf_uN 32 v_tagidx) ⟹
		 wf_externidx (TAG v_tagidx)"

(* Mutual Recursion at: ../specification/wasm-3.0/1.1-syntax.values.spectec:129.1-129.86 *)
inductive fun_funcsxx :: "(externidx list) ⇒ (typeidx list) ⇒ bool" where
	  fun_funcsxx_case_0 :
		"fun_funcsxx [] []"
	| fun_funcsxx_case_1 :
		"(fun_funcsxx xx_lst var_0) ⟹
		 fun_funcsxx ([(FUNC x)] @ xx_lst) ([x] @ var_0)"
	| fun_funcsxx_case_2 :
		"(fun_funcsxx xx_lst var_0) ⟹
		 fun_funcsxx ([v_externidx] @ xx_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/1.1-syntax.values.spectec:130.1-130.88 *)
inductive fun_globalsxx :: "(externidx list) ⇒ (globalidx list) ⇒ bool" where
	  fun_globalsxx_case_0 :
		"fun_globalsxx [] []"
	| fun_globalsxx_case_1 :
		"(fun_globalsxx xx_lst var_0) ⟹
		 fun_globalsxx ([(GLOBAL x)] @ xx_lst) ([x] @ var_0)"
	| fun_globalsxx_case_2 :
		"(fun_globalsxx xx_lst var_0) ⟹
		 fun_globalsxx ([v_externidx] @ xx_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/1.1-syntax.values.spectec:131.1-131.87 *)
inductive fun_tablesxx :: "(externidx list) ⇒ (tableidx list) ⇒ bool" where
	  fun_tablesxx_case_0 :
		"fun_tablesxx [] []"
	| fun_tablesxx_case_1 :
		"(fun_tablesxx xx_lst var_0) ⟹
		 fun_tablesxx ([(TABLE x)] @ xx_lst) ([x] @ var_0)"
	| fun_tablesxx_case_2 :
		"(fun_tablesxx xx_lst var_0) ⟹
		 fun_tablesxx ([v_externidx] @ xx_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/1.1-syntax.values.spectec:132.1-132.85 *)
inductive fun_memsxx :: "(externidx list) ⇒ (memidx list) ⇒ bool" where
	  fun_memsxx_case_0 :
		"fun_memsxx [] []"
	| fun_memsxx_case_1 :
		"(fun_memsxx xx_lst var_0) ⟹
		 fun_memsxx ([(MEM x)] @ xx_lst) ([x] @ var_0)"
	| fun_memsxx_case_2 :
		"(fun_memsxx xx_lst var_0) ⟹
		 fun_memsxx ([v_externidx] @ xx_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/1.1-syntax.values.spectec:133.1-133.85 *)
inductive fun_tagsxx :: "(externidx list) ⇒ (tagidx list) ⇒ bool" where
	  fun_tagsxx_case_0 :
		"fun_tagsxx [] []"
	| fun_tagsxx_case_1 :
		"(fun_tagsxx xx_lst var_0) ⟹
		 fun_tagsxx ([(TAG x)] @ xx_lst) ([x] @ var_0)"
	| fun_tagsxx_case_2 :
		"(fun_tagsxx xx_lst var_0) ⟹
		 fun_tagsxx ([v_externidx] @ xx_lst) var_0"

(* Record Creation Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:158.1-169.4 *)
record free =
	TYPES :: "(typeidx list)"
	FUNCS :: "(funcidx list)"
	GLOBALS :: "(globalidx list)"
	TABLES :: "(tableidx list)"
	MEMS :: "(memidx list)"
	ELEMS :: "(elemidx list)"
	DATAS :: "(dataidx list)"
	LOCALS :: "(localidx list)"
	LABELS :: "(labelidx list)"
	TAGS :: "(tagidx list)"

definition append_free :: "free ⇒ free ⇒ free" where
	"append_free arg1 arg2 = ⦇
		TYPES = TYPES arg1 @ TYPES arg2,
		FUNCS = FUNCS arg1 @ FUNCS arg2,
		GLOBALS = GLOBALS arg1 @ GLOBALS arg2,
		TABLES = TABLES arg1 @ TABLES arg2,
		MEMS = MEMS arg1 @ MEMS arg2,
		ELEMS = ELEMS arg1 @ ELEMS arg2,
		DATAS = DATAS arg1 @ DATAS arg2,
		LOCALS = LOCALS arg1 @ LOCALS arg2,
		LABELS = LABELS arg1 @ LABELS arg2,
		TAGS = TAGS arg1 @ TAGS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:158.8-158.12 *)
inductive wf_free :: "free ⇒ bool" where
	  free_case_underscore :
		"list_all (λ (var_0 :: typeidx). (wf_uN 32 var_0)) var_0 ⟹
		 list_all (λ (var_1 :: funcidx). (wf_uN 32 var_1)) var_1 ⟹
		 list_all (λ (var_2 :: globalidx). (wf_uN 32 var_2)) var_2 ⟹
		 list_all (λ (var_3 :: tableidx). (wf_uN 32 var_3)) var_3 ⟹
		 list_all (λ (var_4 :: memidx). (wf_uN 32 var_4)) var_4 ⟹
		 list_all (λ (var_5 :: elemidx). (wf_uN 32 var_5)) var_5 ⟹
		 list_all (λ (var_6 :: dataidx). (wf_uN 32 var_6)) var_6 ⟹
		 list_all (λ (var_7 :: localidx). (wf_uN 32 var_7)) var_7 ⟹
		 list_all (λ (var_8 :: labelidx). (wf_uN 32 var_8)) var_8 ⟹
		 list_all (λ (var_9 :: tagidx). (wf_uN 32 var_9)) var_9 ⟹
		 wf_free ⦇ TYPES = var_0, FUNCS = var_1, GLOBALS = var_2, TABLES = var_3, MEMS = var_4, ELEMS = var_5, DATAS = var_6, LOCALS = var_7, LABELS = var_8, TAGS = var_9 ⦈"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:172.1-172.28 *)
function (sequential) free_opt :: "(free option) ⇒ free" where
		  "free_opt None = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
		| "free_opt (Some v_free) = v_free"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/1.1-syntax.values.spectec:173.1-173.29 *)
inductive fun_free_list :: "(free list) ⇒ free ⇒ bool" where
	  fun_free_list_case_0 :
		"fun_free_list [] ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_list_case_1 :
		"(fun_free_list free'_lst var_0) ⟹
		 fun_free_list ([v_free] @ free'_lst) (append_free v_free var_0)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:182.1-182.34 *)
function (sequential) free_typeidx :: "typeidx ⇒ free" where
		  "free_typeidx v_typeidx = ⦇ TYPES = [v_typeidx], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:183.1-183.34 *)
function (sequential) free_funcidx :: "funcidx ⇒ free" where
		  "free_funcidx v_funcidx = ⦇ TYPES = [], FUNCS = [v_funcidx], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:184.1-184.38 *)
function (sequential) free_globalidx :: "globalidx ⇒ free" where
		  "free_globalidx v_globalidx = ⦇ TYPES = [], FUNCS = [], GLOBALS = [v_globalidx], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:185.1-185.36 *)
function (sequential) free_tableidx :: "tableidx ⇒ free" where
		  "free_tableidx v_tableidx = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [v_tableidx], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:186.1-186.32 *)
function (sequential) free_memidx :: "memidx ⇒ free" where
		  "free_memidx v_memidx = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [v_memidx], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:187.1-187.34 *)
function (sequential) free_elemidx :: "elemidx ⇒ free" where
		  "free_elemidx v_elemidx = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [v_elemidx], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:188.1-188.34 *)
function (sequential) free_dataidx :: "dataidx ⇒ free" where
		  "free_dataidx v_dataidx = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [v_dataidx], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:189.1-189.36 *)
function (sequential) free_localidx :: "localidx ⇒ free" where
		  "free_localidx v_localidx = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [v_localidx], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:190.1-190.36 *)
function (sequential) free_labelidx :: "labelidx ⇒ free" where
		  "free_labelidx v_labelidx = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [v_labelidx], TAGS = [] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:192.1-192.32 *)
function (sequential) free_tagidx :: "tagidx ⇒ free" where
		  "free_tagidx v_tagidx = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [v_tagidx] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:191.1-191.38 *)
function (sequential) free_externidx :: "externidx ⇒ free" where
		  "free_externidx (FUNC v_funcidx) = (free_funcidx v_funcidx)"
		| "free_externidx (GLOBAL v_globalidx) = (free_globalidx v_globalidx)"
		| "free_externidx (TABLE v_tableidx) = (free_tableidx v_tableidx)"
		| "free_externidx (MEM v_memidx) = (free_memidx v_memidx)"
		| "free_externidx (TAG v_tagidx) = (free_tagidx v_tagidx)"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:8.1-8.55 *)
datatype null =
	  NULL
	

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:10.1-11.14 *)
datatype addrtype =
	  I32
	| I64

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:13.1-14.26 *)
datatype numtype =
	  numtype_I32
	| numtype_I64
	| F32
	| F64

(* Auxiliary Definition at:  *)
function (sequential) numtype_addrtype :: "addrtype ⇒ numtype" where
		  "numtype_addrtype I32 = numtype_I32"
		| "numtype_addrtype I64 = numtype_I64"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:16.1-17.9 *)
datatype vectype =
	  V128
	

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:19.1-20.22 *)
datatype consttype =
	  consttype_I32
	| consttype_I64
	| consttype_F32
	| consttype_F64
	| consttype_V128

(* Auxiliary Definition at:  *)
function (sequential) consttype_numtype :: "numtype ⇒ consttype" where
		  "consttype_numtype numtype_I32 = consttype_I32"
		| "consttype_numtype numtype_I64 = consttype_I64"
		| "consttype_numtype F32 = consttype_F32"
		| "consttype_numtype F64 = consttype_F64"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:28.1-29.14 *)
datatype absheaptype =
	  ANY
	| EQ
	| I31
	| STRUCT
	| ARRAY
	| NONE
	| absheaptype_FUNC
	| NOFUNC
	| EXN
	| NOEXN
	| EXTERN
	| NOEXTERN
	| BOT

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:109.1-109.54 *)
datatype mut =
	  MUT
	

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:110.1-110.60 *)
datatype final =
	  FINAL
	

(* Mutual Recursion at: ../specification/wasm-3.0/1.2-syntax.types.spectec:37.1-123.22 *)
datatype typeuse =
	  underscore_IDX "typeidx"
	| underscore_DEF "rectype" "n"
	| REC "n"

and

heaptype =
	  heaptype_ANY
	| heaptype_EQ
	| heaptype_I31
	| heaptype_STRUCT
	| heaptype_ARRAY
	| heaptype_NONE
	| heaptype_FUNC
	| heaptype_NOFUNC
	| heaptype_EXN
	| heaptype_NOEXN
	| heaptype_EXTERN
	| heaptype_NOEXTERN
	| heaptype_BOT
	| heaptype__IDX "typeidx"
	| heaptype__DEF "rectype" "n"
	| heaptype_REC "n"

and

valtype =
	  valtype_I32
	| valtype_I64
	| valtype_F32
	| valtype_F64
	| valtype_V128
	| REF "(null option)" "heaptype"
	| valtype_BOT

and

storagetype =
	  storagetype_I32
	| storagetype_I64
	| storagetype_F32
	| storagetype_F64
	| storagetype_V128
	| storagetype_REF "(null option)" "heaptype"
	| storagetype_BOT
	| I8
	| I16

and

fieldtype =
	  mk_fieldtype "(mut option)" "storagetype"
	

and

comptype =
	  comptype_STRUCT "(fieldtype res_list)"
	| comptype_ARRAY "fieldtype"
	| comptype_FUNC "(valtype res_list)" "(valtype res_list)"

and

subtype =
	  SUB "(final option)" "(typeuse list)" "comptype"
	

and

rectype =
	  rectype_REC "(subtype res_list)"
	

(* Type Alias Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:102.1-103.16 *)
type_synonym resulttype = "(valtype res_list)"

(* Auxiliary Definition at:  *)
function (sequential) heaptype_absheaptype :: "absheaptype ⇒ heaptype" where
		  "heaptype_absheaptype ANY = heaptype_ANY"
		| "heaptype_absheaptype EQ = heaptype_EQ"
		| "heaptype_absheaptype I31 = heaptype_I31"
		| "heaptype_absheaptype STRUCT = heaptype_STRUCT"
		| "heaptype_absheaptype ARRAY = heaptype_ARRAY"
		| "heaptype_absheaptype NONE = heaptype_NONE"
		| "heaptype_absheaptype absheaptype_FUNC = heaptype_FUNC"
		| "heaptype_absheaptype NOFUNC = heaptype_NOFUNC"
		| "heaptype_absheaptype EXN = heaptype_EXN"
		| "heaptype_absheaptype NOEXN = heaptype_NOEXN"
		| "heaptype_absheaptype EXTERN = heaptype_EXTERN"
		| "heaptype_absheaptype NOEXTERN = heaptype_NOEXTERN"
		| "heaptype_absheaptype BOT = heaptype_BOT"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) valtype_addrtype :: "addrtype ⇒ valtype" where
		  "valtype_addrtype I32 = valtype_I32"
		| "valtype_addrtype I64 = valtype_I64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) storagetype_numtype :: "numtype ⇒ storagetype" where
		  "storagetype_numtype numtype_I32 = storagetype_I32"
		| "storagetype_numtype numtype_I64 = storagetype_I64"
		| "storagetype_numtype F32 = storagetype_F32"
		| "storagetype_numtype F64 = storagetype_F64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) valtype_numtype :: "numtype ⇒ valtype" where
		  "valtype_numtype numtype_I32 = valtype_I32"
		| "valtype_numtype numtype_I64 = valtype_I64"
		| "valtype_numtype F32 = valtype_F32"
		| "valtype_numtype F64 = valtype_F64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) heaptype_typeuse :: "typeuse ⇒ heaptype" where
		  "heaptype_typeuse (underscore_IDX x0) = (heaptype__IDX x0)"
		| "heaptype_typeuse (underscore_DEF x0 x1) = (heaptype__DEF x0 x1)"
		| "heaptype_typeuse (REC x0) = (heaptype_REC x0)"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) storagetype_valtype :: "valtype ⇒ storagetype" where
		  "storagetype_valtype valtype_I32 = storagetype_I32"
		| "storagetype_valtype valtype_I64 = storagetype_I64"
		| "storagetype_valtype valtype_F32 = storagetype_F32"
		| "storagetype_valtype valtype_F64 = storagetype_F64"
		| "storagetype_valtype valtype_V128 = storagetype_V128"
		| "storagetype_valtype (REF x0 x1) = (storagetype_REF x0 x1)"
		| "storagetype_valtype valtype_BOT = storagetype_BOT"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) storagetype_vectype :: "vectype ⇒ storagetype" where
		  "storagetype_vectype V128 = storagetype_V128"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) valtype_vectype :: "vectype ⇒ valtype" where
		  "valtype_vectype V128 = valtype_V128"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/1.2-syntax.types.spectec:37.1-123.22 *)
inductive wf_typeuse :: "typeuse ⇒ bool"
and wf_heaptype :: "heaptype ⇒ bool"
and wf_valtype :: "valtype ⇒ bool"
and wf_storagetype :: "storagetype ⇒ bool"
and wf_fieldtype :: "fieldtype ⇒ bool"
and wf_comptype :: "comptype ⇒ bool"
and wf_subtype :: "subtype ⇒ bool" where
	  typeuse_case_0 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_typeuse (underscore_IDX v_typeidx)"
	| typeuse_case_1 :
		"wf_typeuse (underscore_DEF v_rectype v_n)"
	| typeuse_case_2 :
		"wf_typeuse (REC v_n)"
	| heaptype_case_0 :
		"wf_heaptype heaptype_ANY"
	| heaptype_case_1 :
		"wf_heaptype heaptype_EQ"
	| heaptype_case_2 :
		"wf_heaptype heaptype_I31"
	| heaptype_case_3 :
		"wf_heaptype heaptype_STRUCT"
	| heaptype_case_4 :
		"wf_heaptype heaptype_ARRAY"
	| heaptype_case_5 :
		"wf_heaptype heaptype_NONE"
	| heaptype_case_6 :
		"wf_heaptype heaptype_FUNC"
	| heaptype_case_7 :
		"wf_heaptype heaptype_NOFUNC"
	| heaptype_case_8 :
		"wf_heaptype heaptype_EXN"
	| heaptype_case_9 :
		"wf_heaptype heaptype_NOEXN"
	| heaptype_case_10 :
		"wf_heaptype heaptype_EXTERN"
	| heaptype_case_11 :
		"wf_heaptype heaptype_NOEXTERN"
	| heaptype_case_12 :
		"wf_heaptype heaptype_BOT"
	| heaptype_case_13 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_heaptype (heaptype__IDX v_typeidx)"
	| heaptype_case_14 :
		"wf_heaptype (heaptype__DEF v_rectype v_n)"
	| heaptype_case_15 :
		"wf_heaptype (heaptype_REC v_n)"
	| valtype_case_0 :
		"wf_valtype valtype_I32"
	| valtype_case_1 :
		"wf_valtype valtype_I64"
	| valtype_case_2 :
		"wf_valtype valtype_F32"
	| valtype_case_3 :
		"wf_valtype valtype_F64"
	| valtype_case_4 :
		"wf_valtype valtype_V128"
	| valtype_case_5 :
		"(wf_heaptype v_heaptype) ⟹
		 wf_valtype (REF null_opt v_heaptype)"
	| valtype_case_6 :
		"wf_valtype valtype_BOT"
	| storagetype_case_0 :
		"wf_storagetype storagetype_I32"
	| storagetype_case_1 :
		"wf_storagetype storagetype_I64"
	| storagetype_case_2 :
		"wf_storagetype storagetype_F32"
	| storagetype_case_3 :
		"wf_storagetype storagetype_F64"
	| storagetype_case_4 :
		"wf_storagetype storagetype_V128"
	| storagetype_case_5 :
		"(wf_heaptype v_heaptype) ⟹
		 wf_storagetype (storagetype_REF null_opt v_heaptype)"
	| storagetype_case_6 :
		"wf_storagetype storagetype_BOT"
	| storagetype_case_7 :
		"wf_storagetype I8"
	| storagetype_case_8 :
		"wf_storagetype I16"
	| fieldtype_case_0 :
		"(wf_storagetype v_storagetype) ⟹
		 wf_fieldtype (mk_fieldtype mut_opt v_storagetype)"
	| comptype_case_0 :
		"wf_comptype (comptype_STRUCT var_0)"
	| comptype_case_1 :
		"(wf_fieldtype v_fieldtype) ⟹
		 wf_comptype (comptype_ARRAY v_fieldtype)"
	| comptype_case_2 :
		"wf_comptype (comptype_FUNC v_resulttype resulttype_0)"
	| subtype_case_0 :
		"list_all (λ (v_typeuse :: typeuse). (wf_typeuse v_typeuse)) typeuse_lst ⟹
		 (wf_comptype v_comptype) ⟹
		 wf_subtype (SUB final_opt typeuse_lst v_comptype)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:32.1-33.34 *)
datatype deftype =
	  deftype__DEF "rectype" "n"
	

(* Auxiliary Definition at:  *)
function (sequential) heaptype_deftype :: "deftype ⇒ heaptype" where
		  "heaptype_deftype (deftype__DEF x0 x1) = (heaptype__DEF x0 x1)"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) typeuse_deftype :: "deftype ⇒ typeuse" where
		  "typeuse_deftype (deftype__DEF x0 x1) = (underscore_DEF x0 x1)"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:40.1-41.42 *)
datatype typevar =
	  typevar__IDX "typeidx"
	| typevar_REC "n"

(* Auxiliary Definition at:  *)
function (sequential) typeuse_typevar :: "typevar ⇒ typeuse" where
		  "typeuse_typevar (typevar__IDX x0) = (underscore_IDX x0)"
		| "typeuse_typevar (typevar_REC x0) = (REC x0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:40.8-40.15 *)
inductive wf_typevar :: "typevar ⇒ bool" where
	  typevar_case_0 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_typevar (typevar__IDX v_typeidx)"
	| typevar_case_1 :
		"wf_typevar (typevar_REC v_n)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:46.1-47.23 *)
datatype reftype =
	  reftype_REF "(null option)" "heaptype"
	

(* Auxiliary Definition at:  *)
function (sequential) storagetype_reftype :: "reftype ⇒ storagetype" where
		  "storagetype_reftype (reftype_REF x0 x1) = (storagetype_REF x0 x1)"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) valtype_reftype :: "reftype ⇒ valtype" where
		  "valtype_reftype (reftype_REF x0 x1) = (REF x0 x1)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:46.8-46.15 *)
inductive wf_reftype :: "reftype ⇒ bool" where
	  reftype_case_0 :
		"(wf_heaptype v_heaptype) ⟹
		 wf_reftype (reftype_REF null_opt v_heaptype)"

(* Type Alias Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:55.1-55.55 *)
type_synonym Inn = "addrtype"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:56.1-56.56 *)
datatype Fnn =
	  Fnn_F32
	| Fnn_F64

(* Auxiliary Definition at:  *)
function (sequential) numtype_Fnn :: "Fnn ⇒ numtype" where
		  "numtype_Fnn Fnn_F32 = F32"
		| "numtype_Fnn Fnn_F64 = F64"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:57.1-57.54 *)
type_synonym Vnn = "vectype"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:58.1-58.42 *)
datatype Cnn =
	  Cnn_I32
	| Cnn_I64
	| Cnn_F32
	| Cnn_F64
	| Cnn_V128

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:61.1-61.43 *)
definition ANYREF :: "reftype" where
	"ANYREF = (reftype_REF (Some NULL) heaptype_ANY)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:62.1-62.42 *)
definition EQREF :: "reftype" where
	"EQREF = (reftype_REF (Some NULL) heaptype_EQ)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:63.1-63.43 *)
definition I31REF :: "reftype" where
	"I31REF = (reftype_REF (Some NULL) heaptype_I31)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:64.1-64.46 *)
definition STRUCTREF :: "reftype" where
	"STRUCTREF = (reftype_REF (Some NULL) heaptype_STRUCT)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:65.1-65.45 *)
definition ARRAYREF :: "reftype" where
	"ARRAYREF = (reftype_REF (Some NULL) heaptype_ARRAY)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:66.1-66.44 *)
definition FUNCREF :: "reftype" where
	"FUNCREF = (reftype_REF (Some NULL) heaptype_FUNC)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:67.1-67.43 *)
definition EXNREF :: "reftype" where
	"EXNREF = (reftype_REF (Some NULL) heaptype_EXN)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:68.1-68.46 *)
definition EXTERNREF :: "reftype" where
	"EXTERNREF = (reftype_REF (Some NULL) heaptype_EXTERN)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:69.1-69.44 *)
definition NULLREF :: "reftype" where
	"NULLREF = (reftype_REF (Some NULL) heaptype_NONE)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:70.1-70.50 *)
definition NULLFUNCREF :: "reftype" where
	"NULLFUNCREF = (reftype_REF (Some NULL) heaptype_NOFUNC)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:71.1-71.49 *)
definition NULLEXNREF :: "reftype" where
	"NULLEXNREF = (reftype_REF (Some NULL) heaptype_NOEXN)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:72.1-72.54 *)
definition NULLEXTERNREF :: "reftype" where
	"NULLEXTERNREF = (reftype_REF (Some NULL) heaptype_NOEXTERN)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:90.1-90.52 *)
datatype packtype =
	  packtype_I8
	| packtype_I16

(* Auxiliary Definition at:  *)
function (sequential) storagetype_packtype :: "packtype ⇒ storagetype" where
		  "storagetype_packtype packtype_I8 = I8"
		| "storagetype_packtype packtype_I16 = I16"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:91.1-91.60 *)
datatype lanetype =
	  lanetype_I32
	| lanetype_I64
	| lanetype_F32
	| lanetype_F64
	| lanetype_I8
	| lanetype_I16

(* Auxiliary Definition at:  *)
function (sequential) lanetype_Fnn :: "Fnn ⇒ lanetype" where
		  "lanetype_Fnn Fnn_F32 = lanetype_F32"
		| "lanetype_Fnn Fnn_F64 = lanetype_F64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) lanetype_addrtype :: "addrtype ⇒ lanetype" where
		  "lanetype_addrtype I32 = lanetype_I32"
		| "lanetype_addrtype I64 = lanetype_I64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) lanetype_numtype :: "numtype ⇒ lanetype" where
		  "lanetype_numtype numtype_I32 = lanetype_I32"
		| "lanetype_numtype numtype_I64 = lanetype_I64"
		| "lanetype_numtype F32 = lanetype_F32"
		| "lanetype_numtype F64 = lanetype_F64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) lanetype_packtype :: "packtype ⇒ lanetype" where
		  "lanetype_packtype packtype_I8 = lanetype_I8"
		| "lanetype_packtype packtype_I16 = lanetype_I16"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:95.1-95.55 *)
type_synonym Pnn = "packtype"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:96.1-96.56 *)
datatype Jnn =
	  Jnn_I32
	| Jnn_I64
	| Jnn_I8
	| Jnn_I16

(* Auxiliary Definition at:  *)
function (sequential) lanetype_Jnn :: "Jnn ⇒ lanetype" where
		  "lanetype_Jnn Jnn_I32 = lanetype_I32"
		| "lanetype_Jnn Jnn_I64 = lanetype_I64"
		| "lanetype_Jnn Jnn_I8 = lanetype_I8"
		| "lanetype_Jnn Jnn_I16 = lanetype_I16"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) Jnn_addrtype :: "addrtype ⇒ Jnn" where
		  "Jnn_addrtype I32 = Jnn_I32"
		| "Jnn_addrtype I64 = Jnn_I64"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:97.1-97.55 *)
type_synonym Lnn = "lanetype"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:128.1-128.74 *)
datatype limits =
	  mk_limits "u64" "(u64 option)"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:128.8-128.14 *)
inductive wf_limits :: "limits ⇒ bool" where
	  limits_case_0 :
		"(wf_uN 64 v_u64) ⟹
		 wf_limits (mk_limits v_u64 u64_opt)"

(* Type Alias Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:130.1-130.47 *)
type_synonym tagtype = "typeuse"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:131.1-131.58 *)
datatype globaltype =
	  mk_globaltype "(mut option)" "valtype"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:131.8-131.18 *)
inductive wf_globaltype :: "globaltype ⇒ bool" where
	  globaltype_case_0 :
		"(wf_valtype v_valtype) ⟹
		 wf_globaltype (mk_globaltype mut_opt v_valtype)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:132.1-132.63 *)
datatype memtype =
	  PAGE "addrtype" "limits"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:132.8-132.15 *)
inductive wf_memtype :: "memtype ⇒ bool" where
	  memtype_case_0 :
		"(wf_limits v_limits) ⟹
		 wf_memtype (PAGE v_addrtype v_limits)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:133.1-133.67 *)
datatype tabletype =
	  mk_tabletype "addrtype" "limits" "reftype"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:133.8-133.17 *)
inductive wf_tabletype :: "tabletype ⇒ bool" where
	  tabletype_case_0 :
		"(wf_limits v_limits) ⟹
		 (wf_reftype v_reftype) ⟹
		 wf_tabletype (mk_tabletype v_addrtype v_limits v_reftype)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:134.1-134.64 *)
datatype res_datatype =
	  OK
	

(* Type Alias Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:135.1-135.52 *)
type_synonym elemtype = "reftype"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:137.1-138.83 *)
datatype externtype =
	  externtype_TAG "tagtype"
	| externtype_GLOBAL "globaltype"
	| externtype_MEM "memtype"
	| externtype_TABLE "tabletype"
	| externtype_FUNC "typeuse"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:137.8-137.18 *)
inductive wf_externtype :: "externtype ⇒ bool" where
	  externtype_case_0 :
		"(wf_typeuse v_tagtype) ⟹
		 wf_externtype (externtype_TAG v_tagtype)"
	| externtype_case_1 :
		"(wf_globaltype v_globaltype) ⟹
		 wf_externtype (externtype_GLOBAL v_globaltype)"
	| externtype_case_2 :
		"(wf_memtype v_memtype) ⟹
		 wf_externtype (externtype_MEM v_memtype)"
	| externtype_case_3 :
		"(wf_tabletype v_tabletype) ⟹
		 wf_externtype (externtype_TABLE v_tabletype)"
	| externtype_case_4 :
		"(wf_typeuse v_typeuse) ⟹
		 wf_externtype (externtype_FUNC v_typeuse)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:140.1-141.47 *)
datatype moduletype =
	  mk_moduletype "(externtype list)" "(externtype list)"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:140.8-140.18 *)
inductive wf_moduletype :: "moduletype ⇒ bool" where
	  moduletype_case_0 :
		"list_all (λ (v_externtype :: externtype). (wf_externtype v_externtype)) externtype_lst ⟹
		 list_all (λ (externtype_lst_0 :: externtype). (wf_externtype externtype_lst_0)) externtype_lst_0 ⟹
		 wf_moduletype (mk_moduletype externtype_lst externtype_lst_0)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:179.1-179.65 *)
function (sequential) IN :: "N ⇒ (Inn option)" where
		  "IN (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some I32)"
		| "IN (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some I64)"
		| "IN x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:183.1-183.65 *)
function (sequential) FN :: "N ⇒ (Fnn option)" where
		  "FN (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some Fnn_F32)"
		| "FN (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some Fnn_F64)"
		| "FN x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:187.1-187.65 *)
function (sequential) JN :: "N ⇒ (Jnn option)" where
		  "JN (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) = (Some Jnn_I8)"
		| "JN (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))) = (Some Jnn_I16)"
		| "JN (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some Jnn_I32)"
		| "JN (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some Jnn_I64)"
		| "JN x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:196.1-196.46 *)
function (sequential) size :: "numtype ⇒ nat" where
		  "size numtype_I32 = 32"
		| "size numtype_I64 = 64"
		| "size F32 = 32"
		| "size F64 = 64"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:197.1-197.46 *)
function (sequential) vsize :: "vectype ⇒ nat" where
		  "vsize V128 = 128"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:198.1-198.46 *)
function (sequential) psize :: "packtype ⇒ nat" where
		  "psize packtype_I8 = 8"
		| "psize packtype_I16 = 16"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:199.1-199.46 *)
function (sequential) lsize :: "lanetype ⇒ nat" where
		  "lsize lanetype_I32 = (size numtype_I32)"
		| "lsize lanetype_I64 = (size numtype_I64)"
		| "lsize lanetype_F32 = (size F32)"
		| "lsize lanetype_F64 = (size F64)"
		| "lsize lanetype_I8 = (psize packtype_I8)"
		| "lsize lanetype_I16 = (psize packtype_I16)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:200.1-200.60 *)
function (sequential) zsize :: "storagetype ⇒ (nat option)" where
		  "zsize storagetype_I32 = (Some (size numtype_I32))"
		| "zsize storagetype_I64 = (Some (size numtype_I64))"
		| "zsize storagetype_F32 = (Some (size F32))"
		| "zsize storagetype_F64 = (Some (size F64))"
		| "zsize storagetype_V128 = (Some (vsize V128))"
		| "zsize I8 = (Some (psize packtype_I8))"
		| "zsize I16 = (Some (psize packtype_I16))"
		| "zsize x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:201.1-201.71 *)
function (sequential) isize :: "Inn ⇒ nat" where
		  "isize v_Inn = (size (numtype_addrtype v_Inn))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:202.1-202.71 *)
function (sequential) jsize :: "Jnn ⇒ nat" where
		  "jsize v_Jnn = (lsize (lanetype_Jnn v_Jnn))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:203.1-203.71 *)
function (sequential) fsize :: "Fnn ⇒ nat" where
		  "fsize v_Fnn = (size (numtype_Fnn v_Fnn))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:226.1-226.40 *)
function (sequential) inv_isize :: "nat ⇒ (Inn option)" where
		  "inv_isize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some I32)"
		| "inv_isize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some I64)"
		| "inv_isize x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:227.1-227.40 *)
function (sequential) inv_jsize :: "nat ⇒ (Jnn option)" where
		  "inv_jsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) = (Some Jnn_I8)"
		| "inv_jsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))) = (Some Jnn_I16)"
		| "inv_jsize v_n = (map_option (λ (iter_val_1 :: Inn). (Jnn_addrtype iter_val_1)) (inv_isize v_n))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:228.1-228.40 *)
function (sequential) inv_fsize :: "nat ⇒ (Fnn option)" where
		  "inv_fsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some Fnn_F32)"
		| "inv_fsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some Fnn_F64)"
		| "inv_fsize x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:239.1-239.63 *)
function (sequential) sizenn :: "numtype ⇒ nat" where
		  "sizenn nt = (size nt)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:240.1-240.63 *)
function (sequential) sizenn1 :: "numtype ⇒ nat" where
		  "sizenn1 nt = (size nt)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:241.1-241.63 *)
function (sequential) sizenn2 :: "numtype ⇒ nat" where
		  "sizenn2 nt = (size nt)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:246.1-246.63 *)
function (sequential) vsizenn :: "vectype ⇒ nat" where
		  "vsizenn vt = (vsize vt)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:249.1-249.63 *)
function (sequential) psizenn :: "packtype ⇒ nat" where
		  "psizenn pt = (psize pt)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:252.1-252.63 *)
function (sequential) lsizenn :: "lanetype ⇒ nat" where
		  "lsizenn lt = (lsize lt)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:253.1-253.63 *)
function (sequential) lsizenn1 :: "lanetype ⇒ nat" where
		  "lsizenn1 lt = (lsize lt)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:254.1-254.63 *)
function (sequential) lsizenn2 :: "lanetype ⇒ nat" where
		  "lsizenn2 lt = (lsize lt)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:259.1-259.83 *)
function (sequential) jsizenn :: "Jnn ⇒ nat" where
		  "jsizenn v_Jnn = (lsize (lanetype_Jnn v_Jnn))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:262.1-262.42 *)
function (sequential) inv_jsizenn :: "nat ⇒ (Jnn option)" where
		  "inv_jsizenn v_n = (inv_jsize v_n)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:268.1-268.56 *)
function (sequential) lunpack :: "lanetype ⇒ numtype" where
		  "lunpack lanetype_I32 = numtype_I32"
		| "lunpack lanetype_I64 = numtype_I64"
		| "lunpack lanetype_F32 = F32"
		| "lunpack lanetype_F64 = F64"
		| "lunpack lanetype_I8 = numtype_I32"
		| "lunpack lanetype_I16 = numtype_I32"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:272.1-272.35 *)
function (sequential) unpack :: "storagetype ⇒ valtype" where
		  "unpack storagetype_BOT = valtype_BOT"
		| "unpack (storagetype_REF null_opt v_heaptype) = (REF null_opt v_heaptype)"
		| "unpack storagetype_V128 = valtype_V128"
		| "unpack storagetype_F64 = valtype_F64"
		| "unpack storagetype_F32 = valtype_F32"
		| "unpack storagetype_I64 = valtype_I64"
		| "unpack storagetype_I32 = valtype_I32"
		| "unpack I8 = valtype_I32"
		| "unpack I16 = valtype_I32"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:276.1-276.73 *)
function (sequential) nunpack :: "storagetype ⇒ (numtype option)" where
		  "nunpack storagetype_I32 = (Some numtype_I32)"
		| "nunpack storagetype_I64 = (Some numtype_I64)"
		| "nunpack storagetype_F32 = (Some F32)"
		| "nunpack storagetype_F64 = (Some F64)"
		| "nunpack I8 = (Some numtype_I32)"
		| "nunpack I16 = (Some numtype_I32)"
		| "nunpack x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:280.1-280.73 *)
function (sequential) vunpack :: "storagetype ⇒ (vectype option)" where
		  "vunpack storagetype_V128 = (Some V128)"
		| "vunpack x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:283.1-283.74 *)
function (sequential) cunpack :: "storagetype ⇒ (consttype option)" where
		  "cunpack storagetype_I32 = (Some consttype_I32)"
		| "cunpack storagetype_I64 = (Some consttype_I64)"
		| "cunpack storagetype_F32 = (Some consttype_F32)"
		| "cunpack storagetype_F64 = (Some consttype_F64)"
		| "cunpack storagetype_V128 = (Some consttype_V128)"
		| "cunpack I8 = (Some consttype_I32)"
		| "cunpack I16 = (Some consttype_I32)"
		| "cunpack x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:291.1-291.90 *)
function (sequential) minat :: "addrtype ⇒ addrtype ⇒ addrtype" where
		  "minat at_1 at_2 = (if ((size (numtype_addrtype at_1)) ≤ (size (numtype_addrtype at_2))) then at_1 else at_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:295.1-295.82 *)
function (sequential) diffrt :: "reftype ⇒ reftype ⇒ reftype" where
		  "diffrt (reftype_REF null_1_opt ht_1) (reftype_REF (Some NULL) ht_2) = (reftype_REF None ht_1)"
		| "diffrt (reftype_REF null_1_opt ht_1) (reftype_REF None ht_2) = (reftype_REF null_1_opt ht_1)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:300.1-300.63 *)
function (sequential) as_deftype :: "typeuse ⇒ (deftype option)" where
		  "as_deftype (underscore_DEF v_rectype v_n) = (Some (deftype__DEF v_rectype v_n))"
		| "as_deftype x0 = None"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/1.2-syntax.types.spectec:308.1-308.87 *)
inductive fun_tagsxt :: "(externtype list) ⇒ (tagtype list) ⇒ bool" where
	  fun_tagsxt_case_0 :
		"fun_tagsxt [] []"
	| fun_tagsxt_case_1 :
		"(fun_tagsxt xt_lst var_0) ⟹
		 fun_tagsxt ([(externtype_TAG jt)] @ xt_lst) ([jt] @ var_0)"
	| fun_tagsxt_case_2 :
		"(fun_tagsxt xt_lst var_0) ⟹
		 fun_tagsxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/1.2-syntax.types.spectec:309.1-309.90 *)
inductive fun_globalsxt :: "(externtype list) ⇒ (globaltype list) ⇒ bool" where
	  fun_globalsxt_case_0 :
		"fun_globalsxt [] []"
	| fun_globalsxt_case_1 :
		"(fun_globalsxt xt_lst var_0) ⟹
		 fun_globalsxt ([(externtype_GLOBAL gt)] @ xt_lst) ([gt] @ var_0)"
	| fun_globalsxt_case_2 :
		"(fun_globalsxt xt_lst var_0) ⟹
		 fun_globalsxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/1.2-syntax.types.spectec:310.1-310.87 *)
inductive fun_memsxt :: "(externtype list) ⇒ (memtype list) ⇒ bool" where
	  fun_memsxt_case_0 :
		"fun_memsxt [] []"
	| fun_memsxt_case_1 :
		"(fun_memsxt xt_lst var_0) ⟹
		 fun_memsxt ([(externtype_MEM mt)] @ xt_lst) ([mt] @ var_0)"
	| fun_memsxt_case_2 :
		"(fun_memsxt xt_lst var_0) ⟹
		 fun_memsxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/1.2-syntax.types.spectec:311.1-311.89 *)
inductive fun_tablesxt :: "(externtype list) ⇒ (tabletype list) ⇒ bool" where
	  fun_tablesxt_case_0 :
		"fun_tablesxt [] []"
	| fun_tablesxt_case_1 :
		"(fun_tablesxt xt_lst var_0) ⟹
		 fun_tablesxt ([(externtype_TABLE tt)] @ xt_lst) ([tt] @ var_0)"
	| fun_tablesxt_case_2 :
		"(fun_tablesxt xt_lst var_0) ⟹
		 fun_tablesxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/1.2-syntax.types.spectec:312.1-312.88 *)
inductive fun_funcsxt :: "(externtype list) ⇒ (deftype list) ⇒ bool" where
	  fun_funcsxt_case_0 :
		"fun_funcsxt [] []"
	| fun_funcsxt_case_1 :
		"(fun_funcsxt xt_lst var_0) ⟹
		 fun_funcsxt ([(externtype_FUNC (underscore_DEF v_rectype v_n))] @ xt_lst) ([(deftype__DEF v_rectype v_n)] @ var_0)"
	| fun_funcsxt_case_2 :
		"(fun_funcsxt xt_lst var_0) ⟹
		 fun_funcsxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/1.2-syntax.types.spectec:337.1-337.126 *)
inductive fun_subst_typevar :: "typevar ⇒ (typevar list) ⇒ (typeuse list) ⇒ (typeuse option) ⇒ bool" where
	  fun_subst_typevar_case_0 :
		"fun_subst_typevar tv [] [] (Some (typeuse_typevar tv))"
	| fun_subst_typevar_case_1 :
		"(fun_subst_typevar tv tv'_lst tu'_lst var_0) ⟹
		 fun_subst_typevar tv ([tv_1] @ tv'_lst) ([tu_1] @ tu'_lst) (map_option (λ (iter_val_2 :: typeuse). (if (tv = tv_1) then tu_1 else iter_val_2)) var_0)"
	| fun_subst_typevar_case_2 :
		"True ⟹
		 fun_subst_typevar x0 x1 x2 None"

(* Mutual Recursion at: ../specification/wasm-3.0/1.2-syntax.types.spectec:401.1-401.73 *)
inductive fun_minus_recs :: "(typevar list) ⇒ (typeuse list) ⇒ (((typevar list) * (typeuse list)) option) ⇒ bool" where
	  fun_minus_recs_case_0 :
		"fun_minus_recs [] [] (Some ([], []))"
	| fun_minus_recs_case_1 :
		"(fun_minus_recs tv_lst tu_lst var_0) ⟹
		 fun_minus_recs ([(typevar_REC v_n)] @ tv_lst) ([tu_1] @ tu_lst) var_0"
	| fun_minus_recs_case_2 :
		"(fun_minus_recs tv_lst tu_lst var_0) ⟹
		 list_all (λ (iter :: typevar). (wf_typevar iter)) (fst (the (var_0))) ⟹
		 list_all (λ (iter :: typeuse). (wf_typeuse iter)) (snd (the (var_0))) ⟹
		 (var_0 ≠ None) ⟹
		 ((tv'_lst, tu'_lst) = (the (var_0))) ⟹
		 fun_minus_recs ([(typevar__IDX x)] @ tv_lst) ([tu_1] @ tu_lst) (Some (([(typevar__IDX x)] @ tv'_lst), ([tu_1] @ tu'_lst)))"
	| fun_minus_recs_case_3 :
		"True ⟹
		 fun_minus_recs x0 x1 None"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:347.1-347.112 *)
function (sequential) subst_packtype :: "packtype ⇒ (typevar list) ⇒ (typeuse list) ⇒ packtype" where
		  "subst_packtype pt tv_lst tu_lst = pt"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:341.1-341.112 *)
function (sequential) subst_numtype :: "numtype ⇒ (typevar list) ⇒ (typeuse list) ⇒ numtype" where
		  "subst_numtype nt tv_lst tu_lst = nt"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:342.1-342.112 *)
function (sequential) subst_vectype :: "vectype ⇒ (typevar list) ⇒ (typeuse list) ⇒ vectype" where
		  "subst_vectype vt tv_lst tu_lst = vt"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/1.2-syntax.types.spectec:338.1-354.112 *)
inductive fun_subst_typeuse :: "typeuse ⇒ (typevar list) ⇒ (typeuse list) ⇒ typeuse ⇒ bool"
and fun_subst_heaptype :: "heaptype ⇒ (typevar list) ⇒ (typeuse list) ⇒ heaptype ⇒ bool"
and fun_subst_reftype :: "reftype ⇒ (typevar list) ⇒ (typeuse list) ⇒ reftype ⇒ bool"
and fun_subst_valtype :: "valtype ⇒ (typevar list) ⇒ (typeuse list) ⇒ valtype ⇒ bool"
and fun_subst_storagetype :: "storagetype ⇒ (typevar list) ⇒ (typeuse list) ⇒ storagetype ⇒ bool"
and fun_subst_fieldtype :: "fieldtype ⇒ (typevar list) ⇒ (typeuse list) ⇒ fieldtype ⇒ bool"
and fun_subst_comptype :: "comptype ⇒ (typevar list) ⇒ (typeuse list) ⇒ comptype ⇒ bool"
and fun_subst_subtype :: "subtype ⇒ (typevar list) ⇒ (typeuse list) ⇒ subtype ⇒ bool"
and fun_subst_rectype :: "rectype ⇒ (typevar list) ⇒ (typeuse list) ⇒ rectype ⇒ bool"
and fun_subst_deftype :: "deftype ⇒ (typevar list) ⇒ (typeuse list) ⇒ deftype ⇒ bool" where
	  fun_subst_typeuse_case_0 :
		"(var_0 ≠ None) ⟹
		 (fun_subst_typevar (typevar_REC v_n) tv_lst tu_lst var_0) ⟹
		 fun_subst_typeuse (REC v_n) tv_lst tu_lst (the (var_0))"
	| fun_subst_typeuse_case_1 :
		"(var_0 ≠ None) ⟹
		 (fun_subst_typevar (typevar__IDX v_typeidx) tv_lst tu_lst var_0) ⟹
		 fun_subst_typeuse (underscore_IDX v_typeidx) tv_lst tu_lst (the (var_0))"
	| fun_subst_typeuse_case_2 :
		"(fun_subst_deftype (deftype__DEF v_rectype v_n) tv_lst tu_lst var_0) ⟹
		 fun_subst_typeuse (underscore_DEF v_rectype v_n) tv_lst tu_lst (typeuse_deftype var_0)"
	| fun_subst_heaptype_case_0 :
		"(var_0 ≠ None) ⟹
		 (fun_subst_typevar (typevar_REC v_n) tv_lst tu_lst var_0) ⟹
		 fun_subst_heaptype (heaptype_REC v_n) tv_lst tu_lst (heaptype_typeuse (the (var_0)))"
	| fun_subst_heaptype_case_1 :
		"(var_0 ≠ None) ⟹
		 (fun_subst_typevar (typevar__IDX v_typeidx) tv_lst tu_lst var_0) ⟹
		 fun_subst_heaptype (heaptype__IDX v_typeidx) tv_lst tu_lst (heaptype_typeuse (the (var_0)))"
	| fun_subst_heaptype_case_2 :
		"(fun_subst_deftype (deftype__DEF v_rectype v_n) tv_lst tu_lst var_0) ⟹
		 fun_subst_heaptype (heaptype__DEF v_rectype v_n) tv_lst tu_lst (heaptype_deftype var_0)"
	| fun_subst_heaptype_case_3 :
		"fun_subst_heaptype ht tv_lst tu_lst ht"
	| fun_subst_reftype_case_0 :
		"(fun_subst_heaptype ht tv_lst tu_lst var_0) ⟹
		 fun_subst_reftype (reftype_REF null_opt ht) tv_lst tu_lst (reftype_REF null_opt var_0)"
	| fun_subst_valtype_case_0 :
		"fun_subst_valtype valtype_I32 tv_lst tu_lst (valtype_numtype (subst_numtype numtype_I32 tv_lst tu_lst))"
	| fun_subst_valtype_case_1 :
		"fun_subst_valtype valtype_I64 tv_lst tu_lst (valtype_numtype (subst_numtype numtype_I64 tv_lst tu_lst))"
	| fun_subst_valtype_case_2 :
		"fun_subst_valtype valtype_F32 tv_lst tu_lst (valtype_numtype (subst_numtype F32 tv_lst tu_lst))"
	| fun_subst_valtype_case_3 :
		"fun_subst_valtype valtype_F64 tv_lst tu_lst (valtype_numtype (subst_numtype F64 tv_lst tu_lst))"
	| fun_subst_valtype_case_4 :
		"fun_subst_valtype valtype_V128 tv_lst tu_lst (valtype_vectype (subst_vectype V128 tv_lst tu_lst))"
	| fun_subst_valtype_case_5 :
		"(fun_subst_reftype (reftype_REF null_opt v_heaptype) tv_lst tu_lst var_0) ⟹
		 fun_subst_valtype (REF null_opt v_heaptype) tv_lst tu_lst (valtype_reftype var_0)"
	| fun_subst_valtype_case_6 :
		"fun_subst_valtype valtype_BOT tv_lst tu_lst valtype_BOT"
	| fun_subst_storagetype_case_0 :
		"(fun_subst_valtype valtype_BOT tv_lst tu_lst var_0) ⟹
		 fun_subst_storagetype storagetype_BOT tv_lst tu_lst (storagetype_valtype var_0)"
	| fun_subst_storagetype_case_1 :
		"(fun_subst_valtype (REF null_opt v_heaptype) tv_lst tu_lst var_0) ⟹
		 fun_subst_storagetype (storagetype_REF null_opt v_heaptype) tv_lst tu_lst (storagetype_valtype var_0)"
	| fun_subst_storagetype_case_2 :
		"(fun_subst_valtype valtype_V128 tv_lst tu_lst var_0) ⟹
		 fun_subst_storagetype storagetype_V128 tv_lst tu_lst (storagetype_valtype var_0)"
	| fun_subst_storagetype_case_3 :
		"(fun_subst_valtype valtype_F64 tv_lst tu_lst var_0) ⟹
		 fun_subst_storagetype storagetype_F64 tv_lst tu_lst (storagetype_valtype var_0)"
	| fun_subst_storagetype_case_4 :
		"(fun_subst_valtype valtype_F32 tv_lst tu_lst var_0) ⟹
		 fun_subst_storagetype storagetype_F32 tv_lst tu_lst (storagetype_valtype var_0)"
	| fun_subst_storagetype_case_5 :
		"(fun_subst_valtype valtype_I64 tv_lst tu_lst var_0) ⟹
		 fun_subst_storagetype storagetype_I64 tv_lst tu_lst (storagetype_valtype var_0)"
	| fun_subst_storagetype_case_6 :
		"(fun_subst_valtype valtype_I32 tv_lst tu_lst var_0) ⟹
		 fun_subst_storagetype storagetype_I32 tv_lst tu_lst (storagetype_valtype var_0)"
	| fun_subst_storagetype_case_7 :
		"fun_subst_storagetype I8 tv_lst tu_lst (storagetype_packtype (subst_packtype packtype_I8 tv_lst tu_lst))"
	| fun_subst_storagetype_case_8 :
		"fun_subst_storagetype I16 tv_lst tu_lst (storagetype_packtype (subst_packtype packtype_I16 tv_lst tu_lst))"
	| fun_subst_fieldtype_case_0 :
		"(fun_subst_storagetype zt tv_lst tu_lst var_0) ⟹
		 fun_subst_fieldtype (mk_fieldtype mut_opt zt) tv_lst tu_lst (mk_fieldtype mut_opt var_0)"
	| fun_subst_comptype_case_0 :
		"((length var_0_lst) = (length ft_lst)) ⟹
		 list_all2 (λ (var_0 :: fieldtype) (ft :: fieldtype). (fun_subst_fieldtype ft tv_lst tu_lst var_0)) var_0_lst ft_lst ⟹
		 fun_subst_comptype (comptype_STRUCT (mk_list ft_lst)) tv_lst tu_lst (comptype_STRUCT (mk_list var_0_lst))"
	| fun_subst_comptype_case_1 :
		"(fun_subst_fieldtype ft tv_lst tu_lst var_0) ⟹
		 fun_subst_comptype (comptype_ARRAY ft) tv_lst tu_lst (comptype_ARRAY var_0)"
	| fun_subst_comptype_case_2 :
		"((length var_1_lst) = (length t_2_lst)) ⟹
		 list_all2 (λ (var_1 :: valtype) (t_2 :: valtype). (fun_subst_valtype t_2 tv_lst tu_lst var_1)) var_1_lst t_2_lst ⟹
		 ((length var_0_lst) = (length t_1_lst)) ⟹
		 list_all2 (λ (var_0 :: valtype) (t_1 :: valtype). (fun_subst_valtype t_1 tv_lst tu_lst var_0)) var_0_lst t_1_lst ⟹
		 fun_subst_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst)) tv_lst tu_lst (comptype_FUNC (mk_list var_0_lst) (mk_list var_1_lst))"
	| fun_subst_subtype_case_0 :
		"(fun_subst_comptype ct tv_lst tu_lst var_1) ⟹
		 ((length var_0_lst) = (length tu'_lst)) ⟹
		 list_all2 (λ (var_0 :: typeuse) (tu' :: typeuse). (fun_subst_typeuse tu' tv_lst tu_lst var_0)) var_0_lst tu'_lst ⟹
		 fun_subst_subtype (SUB final_opt tu'_lst ct) tv_lst tu_lst (SUB final_opt var_0_lst var_1)"
	| fun_subst_rectype_case_0 :
		"(fun_minus_recs tv_lst tu_lst var_1) ⟹
		 ((length var_0_lst) = (length st_lst)) ⟹
		 list_all2 (λ (var_0 :: subtype) (st :: subtype). (fun_subst_subtype st tv'_lst tu'_lst var_0)) var_0_lst st_lst ⟹
		 list_all (λ (iter :: typevar). (wf_typevar iter)) (fst (the (var_1))) ⟹
		 list_all (λ (iter :: typeuse). (wf_typeuse iter)) (snd (the (var_1))) ⟹
		 (var_1 ≠ None) ⟹
		 ((tv'_lst, tu'_lst) = (the (var_1))) ⟹
		 fun_subst_rectype (rectype_REC (mk_list st_lst)) tv_lst tu_lst (rectype_REC (mk_list var_0_lst))"
	| fun_subst_deftype_case_0 :
		"(fun_subst_rectype qt tv_lst tu_lst var_0) ⟹
		 fun_subst_deftype (deftype__DEF qt i) tv_lst tu_lst (deftype__DEF var_0 i)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:340.1-340.112 *)
function (sequential) subst_addrtype :: "addrtype ⇒ (typevar list) ⇒ (typeuse list) ⇒ addrtype" where
		  "subst_addrtype at tv_lst tu_lst = at"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:356.6-356.20 *)
inductive fun_subst_tagtype :: "tagtype ⇒ (typevar list) ⇒ (typeuse list) ⇒ tagtype ⇒ bool" where
	  fun_subst_tagtype_case_0 :
		"(fun_subst_typeuse tu' tv_lst tu_lst var_0) ⟹
		 fun_subst_tagtype tu' tv_lst tu_lst var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:357.6-357.23 *)
inductive fun_subst_globaltype :: "globaltype ⇒ (typevar list) ⇒ (typeuse list) ⇒ globaltype ⇒ bool" where
	  fun_subst_globaltype_case_0 :
		"(fun_subst_valtype t tv_lst tu_lst var_0) ⟹
		 fun_subst_globaltype (mk_globaltype mut_opt t) tv_lst tu_lst (mk_globaltype mut_opt var_0)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:358.1-358.112 *)
function (sequential) subst_memtype :: "memtype ⇒ (typevar list) ⇒ (typeuse list) ⇒ memtype" where
		  "subst_memtype (PAGE at lim) tv_lst tu_lst = (PAGE at lim)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:359.6-359.22 *)
inductive fun_subst_tabletype :: "tabletype ⇒ (typevar list) ⇒ (typeuse list) ⇒ tabletype ⇒ bool" where
	  fun_subst_tabletype_case_0 :
		"(fun_subst_reftype rt tv_lst tu_lst var_0) ⟹
		 fun_subst_tabletype (mk_tabletype at lim rt) tv_lst tu_lst (mk_tabletype at lim var_0)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:361.6-361.23 *)
inductive fun_subst_externtype :: "externtype ⇒ (typevar list) ⇒ (typeuse list) ⇒ externtype ⇒ bool" where
	  fun_subst_externtype_case_0 :
		"(fun_subst_tagtype jt tv_lst tu_lst var_0) ⟹
		 fun_subst_externtype (externtype_TAG jt) tv_lst tu_lst (externtype_TAG var_0)"
	| fun_subst_externtype_case_1 :
		"(fun_subst_globaltype gt tv_lst tu_lst var_0) ⟹
		 fun_subst_externtype (externtype_GLOBAL gt) tv_lst tu_lst (externtype_GLOBAL var_0)"
	| fun_subst_externtype_case_2 :
		"(fun_subst_tabletype tt tv_lst tu_lst var_0) ⟹
		 fun_subst_externtype (externtype_TABLE tt) tv_lst tu_lst (externtype_TABLE var_0)"
	| fun_subst_externtype_case_3 :
		"fun_subst_externtype (externtype_MEM mt) tv_lst tu_lst (externtype_MEM (subst_memtype mt tv_lst tu_lst))"
	| fun_subst_externtype_case_4 :
		"(fun_subst_deftype (deftype__DEF v_rectype v_n) tv_lst tu_lst var_0) ⟹
		 fun_subst_externtype (externtype_FUNC (underscore_DEF v_rectype v_n)) tv_lst tu_lst (externtype_FUNC (typeuse_deftype var_0))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:362.6-362.23 *)
inductive fun_subst_moduletype :: "moduletype ⇒ (typevar list) ⇒ (typeuse list) ⇒ moduletype ⇒ bool" where
	  fun_subst_moduletype_case_0 :
		"((length var_1_lst) = (length xt_2_lst)) ⟹
		 list_all2 (λ (var_1 :: externtype) (xt_2 :: externtype). (fun_subst_externtype xt_2 tv_lst tu_lst var_1)) var_1_lst xt_2_lst ⟹
		 ((length var_0_lst) = (length xt_1_lst)) ⟹
		 list_all2 (λ (var_0 :: externtype) (xt_1 :: externtype). (fun_subst_externtype xt_1 tv_lst tu_lst var_0)) var_0_lst xt_1_lst ⟹
		 fun_subst_moduletype (mk_moduletype xt_1_lst xt_2_lst) tv_lst tu_lst (mk_moduletype var_0_lst var_1_lst)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:431.6-431.24 *)
inductive fun_subst_all_valtype :: "valtype ⇒ (typeuse list) ⇒ valtype ⇒ bool" where
	  fun_subst_all_valtype_case_0 :
		"(fun_subst_valtype t (mkseq (λ i. (typevar__IDX (mk_uN i))) v_n) tu_lst var_0) ⟹
		 (v_n = (length tu_lst)) ⟹
		 fun_subst_all_valtype t tu_lst var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:432.6-432.24 *)
inductive fun_subst_all_reftype :: "reftype ⇒ (typeuse list) ⇒ reftype ⇒ bool" where
	  fun_subst_all_reftype_case_0 :
		"(fun_subst_reftype rt (mkseq (λ i. (typevar__IDX (mk_uN i))) v_n) tu_lst var_0) ⟹
		 (v_n = (length tu_lst)) ⟹
		 fun_subst_all_reftype rt tu_lst var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:433.6-433.24 *)
inductive fun_subst_all_deftype :: "deftype ⇒ (typeuse list) ⇒ deftype ⇒ bool" where
	  fun_subst_all_deftype_case_0 :
		"(fun_subst_deftype dt (mkseq (λ i. (typevar__IDX (mk_uN i))) v_n) tu_lst var_0) ⟹
		 (v_n = (length tu_lst)) ⟹
		 fun_subst_all_deftype dt tu_lst var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:434.6-434.24 *)
inductive fun_subst_all_tagtype :: "tagtype ⇒ (typeuse list) ⇒ tagtype ⇒ bool" where
	  fun_subst_all_tagtype_case_0 :
		"(fun_subst_tagtype jt (mkseq (λ i. (typevar__IDX (mk_uN i))) v_n) tu_lst var_0) ⟹
		 (v_n = (length tu_lst)) ⟹
		 fun_subst_all_tagtype jt tu_lst var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:435.6-435.27 *)
inductive fun_subst_all_globaltype :: "globaltype ⇒ (typeuse list) ⇒ globaltype ⇒ bool" where
	  fun_subst_all_globaltype_case_0 :
		"(fun_subst_globaltype gt (mkseq (λ i. (typevar__IDX (mk_uN i))) v_n) tu_lst var_0) ⟹
		 (v_n = (length tu_lst)) ⟹
		 fun_subst_all_globaltype gt tu_lst var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:436.6-436.24 *)
inductive fun_subst_all_memtype :: "memtype ⇒ (typeuse list) ⇒ memtype ⇒ bool" where
	  fun_subst_all_memtype_case_0 :
		"(v_n = (length tu_lst)) ⟹
		 fun_subst_all_memtype mt tu_lst (subst_memtype mt (mkseq (λ i. (typevar__IDX (mk_uN i))) v_n) tu_lst)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:437.6-437.26 *)
inductive fun_subst_all_tabletype :: "tabletype ⇒ (typeuse list) ⇒ tabletype ⇒ bool" where
	  fun_subst_all_tabletype_case_0 :
		"(fun_subst_tabletype tt (mkseq (λ i. (typevar__IDX (mk_uN i))) v_n) tu_lst var_0) ⟹
		 (v_n = (length tu_lst)) ⟹
		 fun_subst_all_tabletype tt tu_lst var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:438.6-438.27 *)
inductive fun_subst_all_externtype :: "externtype ⇒ (typeuse list) ⇒ externtype ⇒ bool" where
	  fun_subst_all_externtype_case_0 :
		"(fun_subst_externtype xt (mkseq (λ i. (typevar__IDX (mk_uN i))) v_n) tu_lst var_0) ⟹
		 (v_n = (length tu_lst)) ⟹
		 fun_subst_all_externtype xt tu_lst var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:439.6-439.27 *)
inductive fun_subst_all_moduletype :: "moduletype ⇒ (typeuse list) ⇒ moduletype ⇒ bool" where
	  fun_subst_all_moduletype_case_0 :
		"(fun_subst_moduletype mmt (mkseq (λ i. (typevar__IDX (mk_uN i))) v_n) tu_lst var_0) ⟹
		 (v_n = (length tu_lst)) ⟹
		 fun_subst_all_moduletype mmt tu_lst var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/1.2-syntax.types.spectec:451.1-451.97 *)
inductive fun_subst_all_deftypes :: "(deftype list) ⇒ (typeuse list) ⇒ (deftype list) ⇒ bool" where
	  fun_subst_all_deftypes_case_0 :
		"fun_subst_all_deftypes [] tu_lst []"
	| fun_subst_all_deftypes_case_1 :
		"(fun_subst_all_deftypes dt_lst tu_lst var_1) ⟹
		 (fun_subst_all_deftype dt_1 tu_lst var_0) ⟹
		 fun_subst_all_deftypes ([dt_1] @ dt_lst) tu_lst ([var_0] @ var_1)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:458.6-458.13 *)
inductive fun_rollrt :: "typeidx ⇒ rectype ⇒ rectype ⇒ bool" where
	  fun_rollrt_case_0 :
		"list_all2 (λ (var_0 :: subtype) (v_subtype :: subtype). (fun_subst_subtype v_subtype (mkseq (λ i. (typevar__IDX (mk_uN ((proj_uN_0 x) + i)))) v_n) (mkseq (λ i. (REC i)) v_n) var_0)) var_0_lst subtype_lst ⟹
		 (v_rectype = (rectype_REC (mk_list subtype_lst))) ⟹
		 fun_rollrt x v_rectype (rectype_REC (mk_list var_0_lst))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:459.6-459.15 *)
inductive fun_unrollrt :: "rectype ⇒ rectype ⇒ bool" where
	  fun_unrollrt_case_0 :
		"list_all2 (λ (var_0 :: subtype) (v_subtype :: subtype). (fun_subst_subtype v_subtype (mkseq (λ i. (typevar_REC i)) v_n) (mkseq (λ i. (underscore_DEF v_rectype i)) v_n) var_0)) var_0_lst subtype_lst ⟹
		 (v_rectype = (rectype_REC (mk_list subtype_lst))) ⟹
		 fun_unrollrt v_rectype (rectype_REC (mk_list var_0_lst))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:460.6-460.13 *)
inductive fun_rolldt :: "typeidx ⇒ rectype ⇒ (deftype list) ⇒ bool" where
	  fun_rolldt_case_0 :
		"(fun_rollrt x v_rectype var_0) ⟹
		 (var_0 = (rectype_REC (mk_list subtype_lst))) ⟹
		 fun_rolldt x v_rectype (mkseq (λ i. (deftype__DEF (rectype_REC (mk_list subtype_lst)) i)) v_n)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:461.6-461.15 *)
inductive fun_unrolldt :: "deftype ⇒ subtype ⇒ bool" where
	  fun_unrolldt_case_0 :
		"(i < (length subtype_lst)) ⟹
		 (fun_unrollrt v_rectype var_0) ⟹
		 (var_0 = (rectype_REC (mk_list subtype_lst))) ⟹
		 fun_unrolldt (deftype__DEF v_rectype i) (subtype_lst ! i)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:462.6-462.15 *)
inductive fun_expanddt :: "deftype ⇒ comptype ⇒ bool" where
	  fun_expanddt_case_0 :
		"(fun_unrolldt v_deftype var_0) ⟹
		 (wf_subtype var_0) ⟹
		 (wf_subtype (SUB final_opt typeuse_lst v_comptype)) ⟹
		 (var_0 = (SUB final_opt typeuse_lst v_comptype)) ⟹
		 fun_expanddt v_deftype v_comptype"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:477.1-477.36 *)
function (sequential) free_addrtype :: "addrtype ⇒ free" where
		  "free_addrtype v_addrtype = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:478.1-478.34 *)
function (sequential) free_numtype :: "numtype ⇒ free" where
		  "free_numtype v_numtype = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:479.1-479.36 *)
function (sequential) free_packtype :: "packtype ⇒ free" where
		  "free_packtype v_packtype = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:480.1-480.36 *)
function (sequential) free_lanetype :: "lanetype ⇒ free" where
		  "free_lanetype lanetype_I32 = (free_numtype numtype_I32)"
		| "free_lanetype lanetype_I64 = (free_numtype numtype_I64)"
		| "free_lanetype lanetype_F32 = (free_numtype F32)"
		| "free_lanetype lanetype_F64 = (free_numtype F64)"
		| "free_lanetype lanetype_I8 = (free_packtype packtype_I8)"
		| "free_lanetype lanetype_I16 = (free_packtype packtype_I16)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:481.1-481.34 *)
function (sequential) free_vectype :: "vectype ⇒ free" where
		  "free_vectype v_vectype = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:482.1-482.38 *)
function (sequential) free_consttype :: "consttype ⇒ free" where
		  "free_consttype consttype_I32 = (free_numtype numtype_I32)"
		| "free_consttype consttype_I64 = (free_numtype numtype_I64)"
		| "free_consttype consttype_F32 = (free_numtype F32)"
		| "free_consttype consttype_F64 = (free_numtype F64)"
		| "free_consttype consttype_V128 = (free_vectype V128)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:483.1-483.42 *)
function (sequential) free_absheaptype :: "absheaptype ⇒ free" where
		  "free_absheaptype v_absheaptype = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:486.1-486.34 *)
function (sequential) free_typevar :: "typevar ⇒ free" where
		  "free_typevar (typevar__IDX v_typeidx) = (free_typeidx v_typeidx)"
		| "free_typevar (typevar_REC v_n) = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/1.2-syntax.types.spectec:484.1-523.34 *)
inductive fun_free_heaptype :: "heaptype ⇒ free ⇒ bool"
and fun_free_reftype :: "reftype ⇒ free ⇒ bool"
and fun_free_typeuse :: "typeuse ⇒ free ⇒ bool"
and fun_free_valtype :: "valtype ⇒ free ⇒ bool"
and fun_free_resulttype :: "resulttype ⇒ free ⇒ bool"
and fun_free_storagetype :: "storagetype ⇒ free ⇒ bool"
and fun_free_fieldtype :: "fieldtype ⇒ free ⇒ bool"
and fun_free_comptype :: "comptype ⇒ free ⇒ bool"
and fun_free_subtype :: "subtype ⇒ free ⇒ bool"
and fun_free_rectype :: "rectype ⇒ free ⇒ bool"
and fun_free_deftype :: "deftype ⇒ free ⇒ bool" where
	  fun_free_heaptype_case_0 :
		"fun_free_heaptype heaptype_ANY (free_absheaptype ANY)"
	| fun_free_heaptype_case_1 :
		"fun_free_heaptype heaptype_EQ (free_absheaptype EQ)"
	| fun_free_heaptype_case_2 :
		"fun_free_heaptype heaptype_I31 (free_absheaptype I31)"
	| fun_free_heaptype_case_3 :
		"fun_free_heaptype heaptype_STRUCT (free_absheaptype STRUCT)"
	| fun_free_heaptype_case_4 :
		"fun_free_heaptype heaptype_ARRAY (free_absheaptype ARRAY)"
	| fun_free_heaptype_case_5 :
		"fun_free_heaptype heaptype_NONE (free_absheaptype NONE)"
	| fun_free_heaptype_case_6 :
		"fun_free_heaptype heaptype_FUNC (free_absheaptype absheaptype_FUNC)"
	| fun_free_heaptype_case_7 :
		"fun_free_heaptype heaptype_NOFUNC (free_absheaptype NOFUNC)"
	| fun_free_heaptype_case_8 :
		"fun_free_heaptype heaptype_EXN (free_absheaptype EXN)"
	| fun_free_heaptype_case_9 :
		"fun_free_heaptype heaptype_NOEXN (free_absheaptype NOEXN)"
	| fun_free_heaptype_case_10 :
		"fun_free_heaptype heaptype_EXTERN (free_absheaptype EXTERN)"
	| fun_free_heaptype_case_11 :
		"fun_free_heaptype heaptype_NOEXTERN (free_absheaptype NOEXTERN)"
	| fun_free_heaptype_case_12 :
		"fun_free_heaptype heaptype_BOT (free_absheaptype BOT)"
	| fun_free_heaptype_case_13 :
		"(fun_free_typeuse (REC n_0) var_0) ⟹
		 fun_free_heaptype (heaptype_REC n_0) var_0"
	| fun_free_heaptype_case_14 :
		"(fun_free_typeuse (underscore_DEF v_rectype v_n) var_0) ⟹
		 fun_free_heaptype (heaptype__DEF v_rectype v_n) var_0"
	| fun_free_heaptype_case_15 :
		"(fun_free_typeuse (underscore_IDX v_typeidx) var_0) ⟹
		 fun_free_heaptype (heaptype__IDX v_typeidx) var_0"
	| fun_free_reftype_case_0 :
		"(fun_free_heaptype v_heaptype var_0) ⟹
		 fun_free_reftype (reftype_REF null_opt v_heaptype) var_0"
	| fun_free_typeuse_case_0 :
		"fun_free_typeuse (REC v_n) (free_typevar (typevar_REC v_n))"
	| fun_free_typeuse_case_1 :
		"fun_free_typeuse (underscore_IDX v_typeidx) (free_typevar (typevar__IDX v_typeidx))"
	| fun_free_typeuse_case_2 :
		"(fun_free_deftype (deftype__DEF v_rectype v_n) var_0) ⟹
		 fun_free_typeuse (underscore_DEF v_rectype v_n) var_0"
	| fun_free_valtype_case_0 :
		"fun_free_valtype valtype_I32 (free_numtype numtype_I32)"
	| fun_free_valtype_case_1 :
		"fun_free_valtype valtype_I64 (free_numtype numtype_I64)"
	| fun_free_valtype_case_2 :
		"fun_free_valtype valtype_F32 (free_numtype F32)"
	| fun_free_valtype_case_3 :
		"fun_free_valtype valtype_F64 (free_numtype F64)"
	| fun_free_valtype_case_4 :
		"fun_free_valtype valtype_V128 (free_vectype V128)"
	| fun_free_valtype_case_5 :
		"(fun_free_reftype (reftype_REF null_opt v_heaptype) var_0) ⟹
		 fun_free_valtype (REF null_opt v_heaptype) var_0"
	| fun_free_valtype_case_6 :
		"fun_free_valtype valtype_BOT ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_resulttype_case_0 :
		"((length var_1_lst) = (length valtype_lst)) ⟹
		 list_all2 (λ (var_1 :: free) (v_valtype :: valtype). (fun_free_valtype v_valtype var_1)) var_1_lst valtype_lst ⟹
		 (fun_free_list var_1_lst var_0) ⟹
		 fun_free_resulttype (mk_list valtype_lst) var_0"
	| fun_free_storagetype_case_0 :
		"(fun_free_valtype valtype_BOT var_0) ⟹
		 fun_free_storagetype storagetype_BOT var_0"
	| fun_free_storagetype_case_1 :
		"(fun_free_valtype (REF null_opt v_heaptype) var_0) ⟹
		 fun_free_storagetype (storagetype_REF null_opt v_heaptype) var_0"
	| fun_free_storagetype_case_2 :
		"(fun_free_valtype valtype_V128 var_0) ⟹
		 fun_free_storagetype storagetype_V128 var_0"
	| fun_free_storagetype_case_3 :
		"(fun_free_valtype valtype_F64 var_0) ⟹
		 fun_free_storagetype storagetype_F64 var_0"
	| fun_free_storagetype_case_4 :
		"(fun_free_valtype valtype_F32 var_0) ⟹
		 fun_free_storagetype storagetype_F32 var_0"
	| fun_free_storagetype_case_5 :
		"(fun_free_valtype valtype_I64 var_0) ⟹
		 fun_free_storagetype storagetype_I64 var_0"
	| fun_free_storagetype_case_6 :
		"(fun_free_valtype valtype_I32 var_0) ⟹
		 fun_free_storagetype storagetype_I32 var_0"
	| fun_free_storagetype_case_7 :
		"fun_free_storagetype I8 (free_packtype packtype_I8)"
	| fun_free_storagetype_case_8 :
		"fun_free_storagetype I16 (free_packtype packtype_I16)"
	| fun_free_fieldtype_case_0 :
		"(fun_free_storagetype v_storagetype var_0) ⟹
		 fun_free_fieldtype (mk_fieldtype mut_opt v_storagetype) var_0"
	| fun_free_comptype_case_0 :
		"((length var_1_lst) = (length fieldtype_lst)) ⟹
		 list_all2 (λ (var_1 :: free) (v_fieldtype :: fieldtype). (fun_free_fieldtype v_fieldtype var_1)) var_1_lst fieldtype_lst ⟹
		 (fun_free_list var_1_lst var_0) ⟹
		 fun_free_comptype (comptype_STRUCT (mk_list fieldtype_lst)) var_0"
	| fun_free_comptype_case_1 :
		"(fun_free_fieldtype v_fieldtype var_0) ⟹
		 fun_free_comptype (comptype_ARRAY v_fieldtype) var_0"
	| fun_free_comptype_case_2 :
		"(fun_free_resulttype resulttype_2 var_1) ⟹
		 (fun_free_resulttype resulttype_1 var_0) ⟹
		 fun_free_comptype (comptype_FUNC resulttype_1 resulttype_2) (append_free var_0 var_1)"
	| fun_free_subtype_case_0 :
		"(fun_free_comptype v_comptype var_2) ⟹
		 ((length var_1_lst) = (length typeuse_lst)) ⟹
		 list_all2 (λ (var_1 :: free) (v_typeuse :: typeuse). (fun_free_typeuse v_typeuse var_1)) var_1_lst typeuse_lst ⟹
		 (fun_free_list var_1_lst var_0) ⟹
		 fun_free_subtype (SUB final_opt typeuse_lst v_comptype) (append_free var_0 var_2)"
	| fun_free_rectype_case_0 :
		"((length var_1_lst) = (length subtype_lst)) ⟹
		 list_all2 (λ (var_1 :: free) (v_subtype :: subtype). (fun_free_subtype v_subtype var_1)) var_1_lst subtype_lst ⟹
		 (fun_free_list var_1_lst var_0) ⟹
		 fun_free_rectype (rectype_REC (mk_list subtype_lst)) var_0"
	| fun_free_deftype_case_0 :
		"(fun_free_rectype v_rectype var_0) ⟹
		 fun_free_deftype (deftype__DEF v_rectype v_n) var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:497.6-497.19 *)
inductive fun_free_tagtype :: "tagtype ⇒ free ⇒ bool" where
	  fun_free_tagtype_case_0 :
		"(fun_free_deftype (deftype__DEF v_rectype v_n) var_0) ⟹
		 fun_free_tagtype (underscore_DEF v_rectype v_n) var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:498.6-498.22 *)
inductive fun_free_globaltype :: "globaltype ⇒ free ⇒ bool" where
	  fun_free_globaltype_case_0 :
		"(fun_free_valtype v_valtype var_0) ⟹
		 fun_free_globaltype (mk_globaltype mut_opt v_valtype) var_0"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:499.1-499.34 *)
function (sequential) free_memtype :: "memtype ⇒ free" where
		  "free_memtype (PAGE v_addrtype v_limits) = (free_addrtype v_addrtype)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:500.6-500.21 *)
inductive fun_free_tabletype :: "tabletype ⇒ free ⇒ bool" where
	  fun_free_tabletype_case_0 :
		"(fun_free_reftype v_reftype var_0) ⟹
		 fun_free_tabletype (mk_tabletype v_addrtype v_limits v_reftype) (append_free (free_addrtype v_addrtype) var_0)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:501.1-501.36 *)
function (sequential) free_datatype :: "res_datatype ⇒ free" where
		  "free_datatype OK = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:502.6-502.20 *)
inductive fun_free_elemtype :: "elemtype ⇒ free ⇒ bool" where
	  fun_free_elemtype_case_0 :
		"(fun_free_reftype v_reftype var_0) ⟹
		 fun_free_elemtype v_reftype var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:503.6-503.22 *)
inductive fun_free_externtype :: "externtype ⇒ free ⇒ bool" where
	  fun_free_externtype_case_0 :
		"(fun_free_tagtype v_tagtype var_0) ⟹
		 fun_free_externtype (externtype_TAG v_tagtype) var_0"
	| fun_free_externtype_case_1 :
		"(fun_free_globaltype v_globaltype var_0) ⟹
		 fun_free_externtype (externtype_GLOBAL v_globaltype) var_0"
	| fun_free_externtype_case_2 :
		"fun_free_externtype (externtype_MEM v_memtype) (free_memtype v_memtype)"
	| fun_free_externtype_case_3 :
		"(fun_free_tabletype v_tabletype var_0) ⟹
		 fun_free_externtype (externtype_TABLE v_tabletype) var_0"
	| fun_free_externtype_case_4 :
		"(fun_free_typeuse v_typeuse var_0) ⟹
		 fun_free_externtype (externtype_FUNC v_typeuse) var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:504.6-504.22 *)
inductive fun_free_moduletype :: "moduletype ⇒ free ⇒ bool" where
	  fun_free_moduletype_case_0 :
		"((length var_3_lst) = (length externtype_2_lst)) ⟹
		 list_all2 (λ (var_3 :: free) (externtype_2 :: externtype). (fun_free_externtype externtype_2 var_3)) var_3_lst externtype_2_lst ⟹
		 (fun_free_list var_3_lst var_2) ⟹
		 ((length var_1_lst) = (length externtype_1_lst)) ⟹
		 list_all2 (λ (var_1 :: free) (externtype_1 :: externtype). (fun_free_externtype externtype_1 var_1)) var_1_lst externtype_1_lst ⟹
		 (fun_free_list var_1_lst var_0) ⟹
		 fun_free_moduletype (mk_moduletype externtype_1_lst externtype_2_lst) (append_free var_0 var_2)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:7.1-7.21 *)
datatype num_underscore =
	  mk_num__0 "Inn" "iN"
	| mk_num__1 "Fnn" "fN"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:7.8-7.13 *)
inductive wf_num_underscore :: "numtype ⇒ num_underscore ⇒ bool" where
	  num__case_0 :
		"(wf_uN (size (numtype_addrtype v_Inn)) var_x) ⟹
		 (v_numtype = (numtype_addrtype v_Inn)) ⟹
		 wf_num_underscore v_numtype (mk_num__0 v_Inn var_x)"
	| num__case_1 :
		"(wf_fN (sizenn (numtype_Fnn v_Fnn)) var_x) ⟹
		 (v_numtype = (numtype_Fnn v_Fnn)) ⟹
		 wf_num_underscore v_numtype (mk_num__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:7.1-7.21 *)
function (sequential) proj_num__0 :: "num_underscore ⇒ (iN option)" where
		  "proj_num__0 (mk_num__0 v_Inn var_x) = (Some var_x)"
		| "proj_num__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:7.1-7.21 *)
function (sequential) proj_num__1 :: "num_underscore ⇒ (fN option)" where
		  "proj_num__1 (mk_num__1 v_Fnn var_x) = (Some var_x)"
		| "proj_num__1 var_x = None"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:11.1-11.38 *)
type_synonym pack_underscore = "iN"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.1-13.23 *)
datatype lane_underscore =
	  mk_lane__0 "numtype" "num_underscore"
	| mk_lane__1 "packtype" "pack_underscore"
	| mk_lane__2 "Jnn" "iN"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.8-13.14 *)
inductive wf_lane_underscore :: "lanetype ⇒ lane_underscore ⇒ bool" where
	  lane__case_0 :
		"(wf_num_underscore v_numtype var_x) ⟹
		 (v_lanetype = (lanetype_numtype v_numtype)) ⟹
		 wf_lane_underscore v_lanetype (mk_lane__0 v_numtype var_x)"
	| lane__case_1 :
		"(wf_uN (psize v_packtype) var_x) ⟹
		 (v_lanetype = (lanetype_packtype v_packtype)) ⟹
		 wf_lane_underscore v_lanetype (mk_lane__1 v_packtype var_x)"
	| lane__case_2 :
		"(wf_uN (lsize (lanetype_Jnn v_Jnn)) var_x) ⟹
		 (v_lanetype = (lanetype_Jnn v_Jnn)) ⟹
		 wf_lane_underscore v_lanetype (mk_lane__2 v_Jnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.1-13.23 *)
function (sequential) proj_lane__0 :: "lane_underscore ⇒ (num_underscore option)" where
		  "proj_lane__0 (mk_lane__0 v_numtype var_x) = (Some var_x)"
		| "proj_lane__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.1-13.23 *)
function (sequential) proj_lane__1 :: "lane_underscore ⇒ (pack_underscore option)" where
		  "proj_lane__1 (mk_lane__1 v_packtype var_x) = (Some var_x)"
		| "proj_lane__1 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.1-13.23 *)
function (sequential) proj_lane__2 :: "lane_underscore ⇒ (iN option)" where
		  "proj_lane__2 (mk_lane__2 v_Jnn var_x) = (Some var_x)"
		| "proj_lane__2 var_x = None"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:18.1-18.35 *)
type_synonym vec_underscore = "vN"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.1-20.25 *)
datatype lit_underscore =
	  mk_lit__0 "numtype" "num_underscore"
	| mk_lit__1 "vectype" "vec_underscore"
	| mk_lit__2 "packtype" "pack_underscore"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.8-20.13 *)
inductive wf_lit_underscore :: "storagetype ⇒ lit_underscore ⇒ bool" where
	  lit__case_0 :
		"(wf_num_underscore v_numtype var_x) ⟹
		 (v_storagetype = (storagetype_numtype v_numtype)) ⟹
		 wf_lit_underscore v_storagetype (mk_lit__0 v_numtype var_x)"
	| lit__case_1 :
		"(wf_uN (vsize v_vectype) var_x) ⟹
		 (v_storagetype = (storagetype_vectype v_vectype)) ⟹
		 wf_lit_underscore v_storagetype (mk_lit__1 v_vectype var_x)"
	| lit__case_2 :
		"(wf_uN (psize v_packtype) var_x) ⟹
		 (v_storagetype = (storagetype_packtype v_packtype)) ⟹
		 wf_lit_underscore v_storagetype (mk_lit__2 v_packtype var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.1-20.25 *)
function (sequential) proj_lit__0 :: "lit_underscore ⇒ (num_underscore option)" where
		  "proj_lit__0 (mk_lit__0 v_numtype var_x) = (Some var_x)"
		| "proj_lit__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.1-20.25 *)
function (sequential) proj_lit__1 :: "lit_underscore ⇒ (vec_underscore option)" where
		  "proj_lit__1 (mk_lit__1 v_vectype var_x) = (Some var_x)"
		| "proj_lit__1 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.1-20.25 *)
function (sequential) proj_lit__2 :: "lit_underscore ⇒ (pack_underscore option)" where
		  "proj_lit__2 (mk_lit__2 v_packtype var_x) = (Some var_x)"
		| "proj_lit__2 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:28.1-28.56 *)
datatype sz =
	  mk_sz "nat"
	

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:28.1-28.56 *)
function (sequential) proj_sz_0 :: "sz ⇒ (nat)" where
		  "proj_sz_0 (mk_sz v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:28.8-28.10 *)
inductive wf_sz :: "sz ⇒ bool" where
	  sz_case_0 :
		"((((i = 8) ∨ (i = 16)) ∨ (i = 32)) ∨ (i = 64)) ⟹
		 wf_sz (mk_sz i)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:29.1-29.42 *)
datatype sx =
	  U
	| S

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.1-31.22 *)
datatype unop_Inn =
	  CLZ
	| CTZ
	| POPCNT
	| EXTEND "sz"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.8-31.14 *)
inductive wf_unop_Inn :: "Inn ⇒ unop_Inn ⇒ bool" where
	  unop_Inn_case_0 :
		"wf_unop_Inn v_Inn CLZ"
	| unop_Inn_case_1 :
		"wf_unop_Inn v_Inn CTZ"
	| unop_Inn_case_2 :
		"wf_unop_Inn v_Inn POPCNT"
	| unop_Inn_case_3 :
		"(wf_sz v_sz) ⟹
		 ((proj_sz_0 v_sz) < (sizenn (numtype_addrtype v_Inn))) ⟹
		 wf_unop_Inn v_Inn (EXTEND v_sz)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.1-31.22 *)
datatype unop_Fnn =
	  ABS
	| unop_Fnn_NEG
	| SQRT
	| CEIL
	| FLOOR
	| TRUNC
	| NEAREST

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.1-31.22 *)
datatype unop_underscore =
	  mk_unop__0 "Inn" "unop_Inn"
	| mk_unop__1 "Fnn" "unop_Fnn"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.8-31.14 *)
inductive wf_unop_underscore :: "numtype ⇒ unop_underscore ⇒ bool" where
	  unop__case_0 :
		"(wf_unop_Inn v_Inn var_x) ⟹
		 (v_numtype = (numtype_addrtype v_Inn)) ⟹
		 wf_unop_underscore v_numtype (mk_unop__0 v_Inn var_x)"
	| unop__case_1 :
		"(v_numtype = (numtype_Fnn v_Fnn)) ⟹
		 wf_unop_underscore v_numtype (mk_unop__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.1-31.22 *)
function (sequential) proj_unop__0 :: "unop_underscore ⇒ (unop_Inn option)" where
		  "proj_unop__0 (mk_unop__0 v_Inn var_x) = (Some var_x)"
		| "proj_unop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.1-31.22 *)
function (sequential) proj_unop__1 :: "unop_underscore ⇒ (unop_Fnn option)" where
		  "proj_unop__1 (mk_unop__1 v_Fnn var_x) = (Some var_x)"
		| "proj_unop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.1-35.23 *)
datatype binop_Inn =
	  ADD
	| binop_Inn_SUB
	| MUL
	| DIV "sx"
	| REM "sx"
	| AND
	| OR
	| XOR
	| SHL
	| SHR "sx"
	| ROTL
	| ROTR

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.1-35.23 *)
datatype binop_Fnn =
	  binop_Fnn_ADD
	| binop_Fnn_SUB
	| binop_Fnn_MUL
	| binop_Fnn_DIV
	| res_MIN
	| res_MAX
	| COPYSIGN

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.1-35.23 *)
datatype binop_underscore =
	  mk_binop__0 "Inn" "binop_Inn"
	| mk_binop__1 "Fnn" "binop_Fnn"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.8-35.15 *)
inductive wf_binop_underscore :: "numtype ⇒ binop_underscore ⇒ bool" where
	  binop__case_0 :
		"(v_numtype = (numtype_addrtype v_Inn)) ⟹
		 wf_binop_underscore v_numtype (mk_binop__0 v_Inn var_x)"
	| binop__case_1 :
		"(v_numtype = (numtype_Fnn v_Fnn)) ⟹
		 wf_binop_underscore v_numtype (mk_binop__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.1-35.23 *)
function (sequential) proj_binop__0 :: "binop_underscore ⇒ (binop_Inn option)" where
		  "proj_binop__0 (mk_binop__0 v_Inn var_x) = (Some var_x)"
		| "proj_binop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.1-35.23 *)
function (sequential) proj_binop__1 :: "binop_underscore ⇒ (binop_Fnn option)" where
		  "proj_binop__1 (mk_binop__1 v_Fnn var_x) = (Some var_x)"
		| "proj_binop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:42.1-42.24 *)
datatype testop_Inn =
	  EQZ
	

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:42.1-42.24 *)
datatype testop_underscore =
	  mk_testop__0 "Inn" "testop_Inn"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:42.8-42.16 *)
inductive wf_testop_underscore :: "numtype ⇒ testop_underscore ⇒ bool" where
	  testop__case_0 :
		"(v_numtype = (numtype_addrtype v_Inn)) ⟹
		 wf_testop_underscore v_numtype (mk_testop__0 v_Inn var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:42.1-42.24 *)
function (sequential) proj_testop__0 :: "testop_underscore ⇒ testop_Inn" where
		  "proj_testop__0 (mk_testop__0 v_Inn var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.1-46.23 *)
datatype relop_Inn =
	  relop_Inn_EQ
	| NE
	| LT "sx"
	| GT "sx"
	| LE "sx"
	| GE "sx"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.1-46.23 *)
datatype relop_Fnn =
	  relop_Fnn_EQ
	| relop_Fnn_NE
	| relop_Fnn_LT
	| relop_Fnn_GT
	| relop_Fnn_LE
	| relop_Fnn_GE

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.1-46.23 *)
datatype relop_underscore =
	  mk_relop__0 "Inn" "relop_Inn"
	| mk_relop__1 "Fnn" "relop_Fnn"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.8-46.15 *)
inductive wf_relop_underscore :: "numtype ⇒ relop_underscore ⇒ bool" where
	  relop__case_0 :
		"(v_numtype = (numtype_addrtype v_Inn)) ⟹
		 wf_relop_underscore v_numtype (mk_relop__0 v_Inn var_x)"
	| relop__case_1 :
		"(v_numtype = (numtype_Fnn v_Fnn)) ⟹
		 wf_relop_underscore v_numtype (mk_relop__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.1-46.23 *)
function (sequential) proj_relop__0 :: "relop_underscore ⇒ (relop_Inn option)" where
		  "proj_relop__0 (mk_relop__0 v_Inn var_x) = (Some var_x)"
		| "proj_relop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.1-46.23 *)
function (sequential) proj_relop__1 :: "relop_underscore ⇒ (relop_Fnn option)" where
		  "proj_relop__1 (mk_relop__1 v_Fnn var_x) = (Some var_x)"
		| "proj_relop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 *)
datatype cvtop__Inn_1_Inn_2 =
	  cvtop__Inn_1_Inn_2_EXTEND "sx"
	| WRAP

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.8-55.16 *)
inductive wf_cvtop__Inn_1_Inn_2 :: "Inn ⇒ Inn ⇒ cvtop__Inn_1_Inn_2 ⇒ bool" where
	  cvtop__Inn_1_Inn_2_case_0 :
		"((sizenn1 (numtype_addrtype Inn_1)) < (sizenn2 (numtype_addrtype Inn_2))) ⟹
		 wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 (cvtop__Inn_1_Inn_2_EXTEND v_sx)"
	| cvtop__Inn_1_Inn_2_case_1 :
		"((sizenn1 (numtype_addrtype Inn_1)) > (sizenn2 (numtype_addrtype Inn_2))) ⟹
		 wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 WRAP"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 *)
datatype cvtop__Inn_1_Fnn_2 =
	  CONVERT "sx"
	| REINTERPRET

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.8-55.16 *)
inductive wf_cvtop__Inn_1_Fnn_2 :: "Inn ⇒ Fnn ⇒ cvtop__Inn_1_Fnn_2 ⇒ bool" where
	  cvtop__Inn_1_Fnn_2_case_0 :
		"wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 (CONVERT v_sx)"
	| cvtop__Inn_1_Fnn_2_case_1 :
		"((sizenn1 (numtype_addrtype Inn_1)) = (sizenn2 (numtype_Fnn Fnn_2))) ⟹
		 wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 REINTERPRET"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 *)
datatype cvtop__Fnn_1_Inn_2 =
	  cvtop__Fnn_1_Inn_2_TRUNC "sx"
	| TRUNC_SAT "sx"
	| cvtop__Fnn_1_Inn_2_REINTERPRET

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.8-55.16 *)
inductive wf_cvtop__Fnn_1_Inn_2 :: "Fnn ⇒ Inn ⇒ cvtop__Fnn_1_Inn_2 ⇒ bool" where
	  cvtop__Fnn_1_Inn_2_case_0 :
		"wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 (cvtop__Fnn_1_Inn_2_TRUNC v_sx)"
	| cvtop__Fnn_1_Inn_2_case_1 :
		"wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 (TRUNC_SAT v_sx)"
	| cvtop__Fnn_1_Inn_2_case_2 :
		"((sizenn1 (numtype_Fnn Fnn_1)) = (sizenn2 (numtype_addrtype Inn_2))) ⟹
		 wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 cvtop__Fnn_1_Inn_2_REINTERPRET"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 *)
datatype cvtop__Fnn_1_Fnn_2 =
	  PROMOTE
	| DEMOTE

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.8-55.16 *)
inductive wf_cvtop__Fnn_1_Fnn_2 :: "Fnn ⇒ Fnn ⇒ cvtop__Fnn_1_Fnn_2 ⇒ bool" where
	  cvtop__Fnn_1_Fnn_2_case_0 :
		"((sizenn1 (numtype_Fnn Fnn_1)) < (sizenn2 (numtype_Fnn Fnn_2))) ⟹
		 wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 PROMOTE"
	| cvtop__Fnn_1_Fnn_2_case_1 :
		"((sizenn1 (numtype_Fnn Fnn_1)) > (sizenn2 (numtype_Fnn Fnn_2))) ⟹
		 wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 DEMOTE"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 *)
datatype cvtop__underscore =
	  mk_cvtop___0 "Inn" "Inn" "cvtop__Inn_1_Inn_2"
	| mk_cvtop___1 "Inn" "Fnn" "cvtop__Inn_1_Fnn_2"
	| mk_cvtop___2 "Fnn" "Inn" "cvtop__Fnn_1_Inn_2"
	| mk_cvtop___3 "Fnn" "Fnn" "cvtop__Fnn_1_Fnn_2"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.8-55.16 *)
inductive wf_cvtop__underscore :: "numtype ⇒ numtype ⇒ cvtop__underscore ⇒ bool" where
	  cvtop___case_0 :
		"(wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 var_x) ⟹
		 (numtype_1 = (numtype_addrtype Inn_1)) ⟹
		 (numtype_2 = (numtype_addrtype Inn_2)) ⟹
		 wf_cvtop__underscore numtype_1 numtype_2 (mk_cvtop___0 Inn_1 Inn_2 var_x)"
	| cvtop___case_1 :
		"(wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 var_x) ⟹
		 (numtype_1 = (numtype_addrtype Inn_1)) ⟹
		 (numtype_2 = (numtype_Fnn Fnn_2)) ⟹
		 wf_cvtop__underscore numtype_1 numtype_2 (mk_cvtop___1 Inn_1 Fnn_2 var_x)"
	| cvtop___case_2 :
		"(wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 var_x) ⟹
		 (numtype_1 = (numtype_Fnn Fnn_1)) ⟹
		 (numtype_2 = (numtype_addrtype Inn_2)) ⟹
		 wf_cvtop__underscore numtype_1 numtype_2 (mk_cvtop___2 Fnn_1 Inn_2 var_x)"
	| cvtop___case_3 :
		"(wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 var_x) ⟹
		 (numtype_1 = (numtype_Fnn Fnn_1)) ⟹
		 (numtype_2 = (numtype_Fnn Fnn_2)) ⟹
		 wf_cvtop__underscore numtype_1 numtype_2 (mk_cvtop___3 Fnn_1 Fnn_2 var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 *)
function (sequential) proj_cvtop___0 :: "cvtop__underscore ⇒ (cvtop__Inn_1_Inn_2 option)" where
		  "proj_cvtop___0 (mk_cvtop___0 Inn_1 Inn_2 var_x) = (Some var_x)"
		| "proj_cvtop___0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 *)
function (sequential) proj_cvtop___1 :: "cvtop__underscore ⇒ (cvtop__Inn_1_Fnn_2 option)" where
		  "proj_cvtop___1 (mk_cvtop___1 Inn_1 Fnn_2 var_x) = (Some var_x)"
		| "proj_cvtop___1 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 *)
function (sequential) proj_cvtop___2 :: "cvtop__underscore ⇒ (cvtop__Fnn_1_Inn_2 option)" where
		  "proj_cvtop___2 (mk_cvtop___2 Fnn_1 Inn_2 var_x) = (Some var_x)"
		| "proj_cvtop___2 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 *)
function (sequential) proj_cvtop___3 :: "cvtop__underscore ⇒ (cvtop__Fnn_1_Fnn_2 option)" where
		  "proj_cvtop___3 (mk_cvtop___3 Fnn_1 Fnn_2 var_x) = (Some var_x)"
		| "proj_cvtop___3 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:73.1-73.60 *)
datatype dim =
	  mk_dim "nat"
	

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:73.1-73.60 *)
function (sequential) proj_dim_0 :: "dim ⇒ (nat)" where
		  "proj_dim_0 (mk_dim v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:73.8-73.11 *)
inductive wf_dim :: "dim ⇒ bool" where
	  dim_case_0 :
		"(((((i = 1) ∨ (i = 2)) ∨ (i = 4)) ∨ (i = 8)) ∨ (i = 16)) ⟹
		 wf_dim (mk_dim i)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:74.1-75.40 *)
datatype shape =
	  X "lanetype" "dim"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:74.8-74.13 *)
inductive wf_shape :: "shape ⇒ bool" where
	  shape_case_0 :
		"(wf_dim v_dim) ⟹
		 (((lsize v_lanetype) * (proj_dim_0 v_dim)) = 128) ⟹
		 wf_shape (X v_lanetype v_dim)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:78.1-78.43 *)
function (sequential) fun_dim :: "shape ⇒ dim" where
		  "fun_dim (X v_Lnn (mk_dim v_N)) = (mk_dim v_N)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:81.1-81.58 *)
function (sequential) fun_lanetype :: "shape ⇒ lanetype" where
		  "fun_lanetype (X v_Lnn (mk_dim v_N)) = v_Lnn"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:84.1-84.57 *)
function (sequential) unpackshape :: "shape ⇒ numtype" where
		  "unpackshape (X v_Lnn (mk_dim v_N)) = (lunpack v_Lnn)"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:88.1-88.78 *)
datatype ishape =
	  mk_ishape "shape"
	

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:88.1-88.78 *)
function (sequential) proj_ishape_0 :: "ishape ⇒ (shape)" where
		  "proj_ishape_0 (mk_ishape v_shape_0) = (v_shape_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:88.8-88.14 *)
inductive wf_ishape :: "ishape ⇒ bool" where
	  ishape_case_0 :
		"(wf_shape v_shape) ⟹
		 ((fun_lanetype v_shape) = (lanetype_Jnn v_Jnn)) ⟹
		 wf_ishape (mk_ishape v_shape)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:89.1-89.77 *)
datatype bshape =
	  mk_bshape "shape"
	

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:89.1-89.77 *)
function (sequential) proj_bshape_0 :: "bshape ⇒ (shape)" where
		  "proj_bshape_0 (mk_bshape v_shape_0) = (v_shape_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:89.8-89.14 *)
inductive wf_bshape :: "bshape ⇒ bool" where
	  bshape_case_0 :
		"(wf_shape v_shape) ⟹
		 ((fun_lanetype v_shape) = lanetype_I8) ⟹
		 wf_bshape (mk_bshape v_shape)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:94.1-94.19 *)
datatype zero =
	  ZERO
	

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:95.1-95.25 *)
datatype half =
	  LOW
	| HIGH

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:97.1-97.41 *)
datatype vvunop =
	  NOT
	

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:98.1-98.62 *)
datatype vvbinop =
	  vvbinop_AND
	| ANDNOT
	| vvbinop_OR
	| vvbinop_XOR

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:99.1-99.49 *)
datatype vvternop =
	  BITSELECT
	

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:100.1-100.48 *)
datatype vvtestop =
	  ANY_TRUE
	

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.1-102.42 *)
datatype vunop_Jnn_M =
	  vunop_Jnn_M_ABS
	| vunop_Jnn_M_NEG
	| vunop_Jnn_M_POPCNT

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.8-102.15 *)
inductive wf_vunop_Jnn_M :: "Jnn ⇒ M ⇒ vunop_Jnn_M ⇒ bool" where
	  vunop_Jnn_M_case_0 :
		"wf_vunop_Jnn_M v_Jnn v_M vunop_Jnn_M_ABS"
	| vunop_Jnn_M_case_1 :
		"wf_vunop_Jnn_M v_Jnn v_M vunop_Jnn_M_NEG"
	| vunop_Jnn_M_case_2 :
		"((lsizenn (lanetype_Jnn v_Jnn)) = 8) ⟹
		 wf_vunop_Jnn_M v_Jnn v_M vunop_Jnn_M_POPCNT"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.1-102.42 *)
datatype vunop_Fnn_M =
	  vunop_Fnn_M_ABS
	| vunop_Fnn_M_NEG
	| vunop_Fnn_M_SQRT
	| vunop_Fnn_M_CEIL
	| vunop_Fnn_M_FLOOR
	| vunop_Fnn_M_TRUNC
	| vunop_Fnn_M_NEAREST

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.1-102.42 *)
datatype vunop_underscore =
	  mk_vunop__0 "Jnn" "M" "vunop_Jnn_M"
	| mk_vunop__1 "Fnn" "M" "vunop_Fnn_M"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.8-102.15 *)
inductive wf_vunop_underscore :: "shape ⇒ vunop_underscore ⇒ bool" where
	  vunop__case_0 :
		"(wf_vunop_Jnn_M v_Jnn v_M var_x) ⟹
		 (v_shape = (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) ⟹
		 wf_vunop_underscore v_shape (mk_vunop__0 v_Jnn v_M var_x)"
	| vunop__case_1 :
		"(v_shape = (X (lanetype_Fnn v_Fnn) (mk_dim v_M))) ⟹
		 wf_vunop_underscore v_shape (mk_vunop__1 v_Fnn v_M var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.1-102.42 *)
function (sequential) proj_vunop__0 :: "vunop_underscore ⇒ (vunop_Jnn_M option)" where
		  "proj_vunop__0 (mk_vunop__0 v_Jnn v_M var_x) = (Some var_x)"
		| "proj_vunop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.1-102.42 *)
function (sequential) proj_vunop__1 :: "vunop_underscore ⇒ (vunop_Fnn_M option)" where
		  "proj_vunop__1 (mk_vunop__1 v_Fnn v_M var_x) = (Some var_x)"
		| "proj_vunop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:108.1-108.43 *)
datatype vbinop_Jnn_M =
	  vbinop_Jnn_M_ADD
	| vbinop_Jnn_M_SUB
	| ADD_SAT "sx"
	| SUB_SAT "sx"
	| vbinop_Jnn_M_MUL
	| AVGRU
	| Q15MULR_SATS
	| RELAXED_Q15MULRS
	| vbinop_Jnn_M_MIN "sx"
	| vbinop_Jnn_M_MAX "sx"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:108.8-108.16 *)
inductive wf_vbinop_Jnn_M :: "Jnn ⇒ M ⇒ vbinop_Jnn_M ⇒ bool" where
	  vbinop_Jnn_M_case_0 :
		"wf_vbinop_Jnn_M v_Jnn v_M vbinop_Jnn_M_ADD"
	| vbinop_Jnn_M_case_1 :
		"wf_vbinop_Jnn_M v_Jnn v_M vbinop_Jnn_M_SUB"
	| vbinop_Jnn_M_case_2 :
		"((lsizenn (lanetype_Jnn v_Jnn)) ≤ 16) ⟹
		 wf_vbinop_Jnn_M v_Jnn v_M (ADD_SAT v_sx)"
	| vbinop_Jnn_M_case_3 :
		"((lsizenn (lanetype_Jnn v_Jnn)) ≤ 16) ⟹
		 wf_vbinop_Jnn_M v_Jnn v_M (SUB_SAT v_sx)"
	| vbinop_Jnn_M_case_4 :
		"((lsizenn (lanetype_Jnn v_Jnn)) ≥ 16) ⟹
		 wf_vbinop_Jnn_M v_Jnn v_M vbinop_Jnn_M_MUL"
	| vbinop_Jnn_M_case_5 :
		"((lsizenn (lanetype_Jnn v_Jnn)) ≤ 16) ⟹
		 wf_vbinop_Jnn_M v_Jnn v_M AVGRU"
	| vbinop_Jnn_M_case_6 :
		"((lsizenn (lanetype_Jnn v_Jnn)) = 16) ⟹
		 wf_vbinop_Jnn_M v_Jnn v_M Q15MULR_SATS"
	| vbinop_Jnn_M_case_7 :
		"((lsizenn (lanetype_Jnn v_Jnn)) = 16) ⟹
		 wf_vbinop_Jnn_M v_Jnn v_M RELAXED_Q15MULRS"
	| vbinop_Jnn_M_case_8 :
		"((lsizenn (lanetype_Jnn v_Jnn)) ≤ 32) ⟹
		 wf_vbinop_Jnn_M v_Jnn v_M (vbinop_Jnn_M_MIN v_sx)"
	| vbinop_Jnn_M_case_9 :
		"((lsizenn (lanetype_Jnn v_Jnn)) ≤ 32) ⟹
		 wf_vbinop_Jnn_M v_Jnn v_M (vbinop_Jnn_M_MAX v_sx)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:108.1-108.43 *)
datatype vbinop_Fnn_M =
	  vbinop_Fnn_M_ADD
	| vbinop_Fnn_M_SUB
	| vbinop_Fnn_M_MUL
	| vbinop_Fnn_M_DIV
	| vbinop_Fnn_M_MIN
	| vbinop_Fnn_M_MAX
	| PMIN
	| PMAX
	| RELAXED_MIN
	| RELAXED_MAX

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:108.1-108.43 *)
datatype vbinop_underscore =
	  mk_vbinop__0 "Jnn" "M" "vbinop_Jnn_M"
	| mk_vbinop__1 "Fnn" "M" "vbinop_Fnn_M"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:108.8-108.16 *)
inductive wf_vbinop_underscore :: "shape ⇒ vbinop_underscore ⇒ bool" where
	  vbinop__case_0 :
		"(wf_vbinop_Jnn_M v_Jnn v_M var_x) ⟹
		 (v_shape = (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) ⟹
		 wf_vbinop_underscore v_shape (mk_vbinop__0 v_Jnn v_M var_x)"
	| vbinop__case_1 :
		"(v_shape = (X (lanetype_Fnn v_Fnn) (mk_dim v_M))) ⟹
		 wf_vbinop_underscore v_shape (mk_vbinop__1 v_Fnn v_M var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:108.1-108.43 *)
function (sequential) proj_vbinop__0 :: "vbinop_underscore ⇒ (vbinop_Jnn_M option)" where
		  "proj_vbinop__0 (mk_vbinop__0 v_Jnn v_M var_x) = (Some var_x)"
		| "proj_vbinop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:108.1-108.43 *)
function (sequential) proj_vbinop__1 :: "vbinop_underscore ⇒ (vbinop_Fnn_M option)" where
		  "proj_vbinop__1 (mk_vbinop__1 v_Fnn v_M var_x) = (Some var_x)"
		| "proj_vbinop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:124.1-124.44 *)
datatype vternop_Jnn_M =
	  RELAXED_LANESELECT
	

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:124.1-124.44 *)
datatype vternop_Fnn_M =
	  RELAXED_MADD
	| RELAXED_NMADD

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:124.1-124.44 *)
datatype vternop_underscore =
	  mk_vternop__0 "Jnn" "M" "vternop_Jnn_M"
	| mk_vternop__1 "Fnn" "M" "vternop_Fnn_M"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:124.8-124.17 *)
inductive wf_vternop_underscore :: "shape ⇒ vternop_underscore ⇒ bool" where
	  vternop__case_0 :
		"(v_shape = (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) ⟹
		 wf_vternop_underscore v_shape (mk_vternop__0 v_Jnn v_M var_x)"
	| vternop__case_1 :
		"(v_shape = (X (lanetype_Fnn v_Fnn) (mk_dim v_M))) ⟹
		 wf_vternop_underscore v_shape (mk_vternop__1 v_Fnn v_M var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:124.1-124.44 *)
function (sequential) proj_vternop__0 :: "vternop_underscore ⇒ (vternop_Jnn_M option)" where
		  "proj_vternop__0 (mk_vternop__0 v_Jnn v_M var_x) = (Some var_x)"
		| "proj_vternop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:124.1-124.44 *)
function (sequential) proj_vternop__1 :: "vternop_underscore ⇒ (vternop_Fnn_M option)" where
		  "proj_vternop__1 (mk_vternop__1 v_Fnn v_M var_x) = (Some var_x)"
		| "proj_vternop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:128.1-128.44 *)
datatype vtestop_Jnn_M =
	  ALL_TRUE
	

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:128.1-128.44 *)
datatype vtestop_underscore =
	  mk_vtestop__0 "Jnn" "M" "vtestop_Jnn_M"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:128.8-128.17 *)
inductive wf_vtestop_underscore :: "shape ⇒ vtestop_underscore ⇒ bool" where
	  vtestop__case_0 :
		"(v_shape = (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) ⟹
		 wf_vtestop_underscore v_shape (mk_vtestop__0 v_Jnn v_M var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:128.1-128.44 *)
function (sequential) proj_vtestop__0 :: "vtestop_underscore ⇒ vtestop_Jnn_M" where
		  "proj_vtestop__0 (mk_vtestop__0 v_Jnn v_M var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:132.1-132.43 *)
datatype vrelop_Jnn_M =
	  vrelop_Jnn_M_EQ
	| vrelop_Jnn_M_NE
	| vrelop_Jnn_M_LT "sx"
	| vrelop_Jnn_M_GT "sx"
	| vrelop_Jnn_M_LE "sx"
	| vrelop_Jnn_M_GE "sx"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:132.8-132.16 *)
inductive wf_vrelop_Jnn_M :: "Jnn ⇒ M ⇒ vrelop_Jnn_M ⇒ bool" where
	  vrelop_Jnn_M_case_0 :
		"wf_vrelop_Jnn_M v_Jnn v_M vrelop_Jnn_M_EQ"
	| vrelop_Jnn_M_case_1 :
		"wf_vrelop_Jnn_M v_Jnn v_M vrelop_Jnn_M_NE"
	| vrelop_Jnn_M_case_2 :
		"(((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = S)) ⟹
		 wf_vrelop_Jnn_M v_Jnn v_M (vrelop_Jnn_M_LT v_sx)"
	| vrelop_Jnn_M_case_3 :
		"(((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = S)) ⟹
		 wf_vrelop_Jnn_M v_Jnn v_M (vrelop_Jnn_M_GT v_sx)"
	| vrelop_Jnn_M_case_4 :
		"(((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = S)) ⟹
		 wf_vrelop_Jnn_M v_Jnn v_M (vrelop_Jnn_M_LE v_sx)"
	| vrelop_Jnn_M_case_5 :
		"(((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = S)) ⟹
		 wf_vrelop_Jnn_M v_Jnn v_M (vrelop_Jnn_M_GE v_sx)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:132.1-132.43 *)
datatype vrelop_Fnn_M =
	  vrelop_Fnn_M_EQ
	| vrelop_Fnn_M_NE
	| vrelop_Fnn_M_LT
	| vrelop_Fnn_M_GT
	| vrelop_Fnn_M_LE
	| vrelop_Fnn_M_GE

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:132.1-132.43 *)
datatype vrelop_underscore =
	  mk_vrelop__0 "Jnn" "M" "vrelop_Jnn_M"
	| mk_vrelop__1 "Fnn" "M" "vrelop_Fnn_M"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:132.8-132.16 *)
inductive wf_vrelop_underscore :: "shape ⇒ vrelop_underscore ⇒ bool" where
	  vrelop__case_0 :
		"(wf_vrelop_Jnn_M v_Jnn v_M var_x) ⟹
		 (v_shape = (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) ⟹
		 wf_vrelop_underscore v_shape (mk_vrelop__0 v_Jnn v_M var_x)"
	| vrelop__case_1 :
		"(v_shape = (X (lanetype_Fnn v_Fnn) (mk_dim v_M))) ⟹
		 wf_vrelop_underscore v_shape (mk_vrelop__1 v_Fnn v_M var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:132.1-132.43 *)
function (sequential) proj_vrelop__0 :: "vrelop_underscore ⇒ (vrelop_Jnn_M option)" where
		  "proj_vrelop__0 (mk_vrelop__0 v_Jnn v_M var_x) = (Some var_x)"
		| "proj_vrelop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:132.1-132.43 *)
function (sequential) proj_vrelop__1 :: "vrelop_underscore ⇒ (vrelop_Fnn_M option)" where
		  "proj_vrelop__1 (mk_vrelop__1 v_Fnn v_M var_x) = (Some var_x)"
		| "proj_vrelop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:140.1-140.46 *)
datatype vshiftop_Jnn_M =
	  vshiftop_Jnn_M_SHL
	| vshiftop_Jnn_M_SHR "sx"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:140.1-140.46 *)
datatype vshiftop_underscore =
	  mk_vshiftop__0 "Jnn" "M" "vshiftop_Jnn_M"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:140.8-140.18 *)
inductive wf_vshiftop_underscore :: "ishape ⇒ vshiftop_underscore ⇒ bool" where
	  vshiftop__case_0 :
		"(v_ishape = (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 wf_vshiftop_underscore v_ishape (mk_vshiftop__0 v_Jnn v_M var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:140.1-140.46 *)
function (sequential) proj_vshiftop__0 :: "vshiftop_underscore ⇒ vshiftop_Jnn_M" where
		  "proj_vshiftop__0 (mk_vshiftop__0 v_Jnn v_M var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:143.1-143.47 *)
datatype vswizzlop_M =
	  SWIZZLE
	| RELAXED_SWIZZLE

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:143.1-143.47 *)
datatype vswizzlop_underscore =
	  mk_vswizzlop__0 "M" "vswizzlop_M"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:143.8-143.19 *)
inductive wf_vswizzlop_underscore :: "bshape ⇒ vswizzlop_underscore ⇒ bool" where
	  vswizzlop__case_0 :
		"(v_bshape = (mk_bshape (X lanetype_I8 (mk_dim v_M)))) ⟹
		 wf_vswizzlop_underscore v_bshape (mk_vswizzlop__0 v_M var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:143.1-143.47 *)
function (sequential) proj_vswizzlop__0 :: "vswizzlop_underscore ⇒ vswizzlop_M" where
		  "proj_vswizzlop__0 (mk_vswizzlop__0 v_M var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:146.1-146.59 *)
datatype vextunop__Jnn_1_M_1_Jnn_2_M_2 =
	  EXTADD_PAIRWISE "sx"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:146.8-146.19 *)
inductive wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 :: "Jnn ⇒ M ⇒ Jnn ⇒ M ⇒ vextunop__Jnn_1_M_1_Jnn_2_M_2 ⇒ bool" where
	  vextunop__Jnn_1_M_1_Jnn_2_M_2_case_0 :
		"((16 ≤ (2 * (lsizenn1 (lanetype_Jnn Jnn_1)))) ∧ (((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) ∧ ((lsizenn2 (lanetype_Jnn Jnn_2)) ≤ 32))) ⟹
		 wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 (EXTADD_PAIRWISE v_sx)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:146.1-146.59 *)
datatype vextunop__underscore =
	  mk_vextunop___0 "Jnn" "M" "Jnn" "M" "vextunop__Jnn_1_M_1_Jnn_2_M_2"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:146.8-146.19 *)
inductive wf_vextunop__underscore :: "ishape ⇒ ishape ⇒ vextunop__underscore ⇒ bool" where
	  vextunop___case_0 :
		"(wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 var_x) ⟹
		 (ishape_1 = (mk_ishape (X (lanetype_Jnn Jnn_1) (mk_dim M_1)))) ⟹
		 (ishape_2 = (mk_ishape (X (lanetype_Jnn Jnn_2) (mk_dim M_2)))) ⟹
		 wf_vextunop__underscore ishape_1 ishape_2 (mk_vextunop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:146.1-146.59 *)
function (sequential) proj_vextunop___0 :: "vextunop__underscore ⇒ vextunop__Jnn_1_M_1_Jnn_2_M_2" where
		  "proj_vextunop___0 (mk_vextunop___0 Jnn_1 M_1 Jnn_2 M_2 var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:151.1-151.60 *)
datatype vextbinop__Jnn_1_M_1_Jnn_2_M_2 =
	  EXTMUL "half" "sx"
	| DOTS
	| RELAXED_DOTS

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:151.8-151.20 *)
inductive wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 :: "Jnn ⇒ M ⇒ Jnn ⇒ M ⇒ vextbinop__Jnn_1_M_1_Jnn_2_M_2 ⇒ bool" where
	  vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_0 :
		"(((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) ∧ ((lsizenn2 (lanetype_Jnn Jnn_2)) ≥ 16)) ⟹
		 wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 (EXTMUL v_half v_sx)"
	| vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_1 :
		"(((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) ∧ ((lsizenn2 (lanetype_Jnn Jnn_2)) = 32)) ⟹
		 wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 DOTS"
	| vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_2 :
		"(((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) ∧ ((lsizenn2 (lanetype_Jnn Jnn_2)) = 16)) ⟹
		 wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 RELAXED_DOTS"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:151.1-151.60 *)
datatype vextbinop__underscore =
	  mk_vextbinop___0 "Jnn" "M" "Jnn" "M" "vextbinop__Jnn_1_M_1_Jnn_2_M_2"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:151.8-151.20 *)
inductive wf_vextbinop__underscore :: "ishape ⇒ ishape ⇒ vextbinop__underscore ⇒ bool" where
	  vextbinop___case_0 :
		"(wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 var_x) ⟹
		 (ishape_1 = (mk_ishape (X (lanetype_Jnn Jnn_1) (mk_dim M_1)))) ⟹
		 (ishape_2 = (mk_ishape (X (lanetype_Jnn Jnn_2) (mk_dim M_2)))) ⟹
		 wf_vextbinop__underscore ishape_1 ishape_2 (mk_vextbinop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:151.1-151.60 *)
function (sequential) proj_vextbinop___0 :: "vextbinop__underscore ⇒ vextbinop__Jnn_1_M_1_Jnn_2_M_2" where
		  "proj_vextbinop___0 (mk_vextbinop___0 Jnn_1 M_1 Jnn_2 M_2 var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:160.1-160.61 *)
datatype vextternop__Jnn_1_M_1_Jnn_2_M_2 =
	  RELAXED_DOT_ADDS
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:160.8-160.21 *)
inductive wf_vextternop__Jnn_1_M_1_Jnn_2_M_2 :: "Jnn ⇒ M ⇒ Jnn ⇒ M ⇒ vextternop__Jnn_1_M_1_Jnn_2_M_2 ⇒ bool" where
	  vextternop__Jnn_1_M_1_Jnn_2_M_2_case_0 :
		"(((4 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) ∧ ((lsizenn2 (lanetype_Jnn Jnn_2)) = 32)) ⟹
		 wf_vextternop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 RELAXED_DOT_ADDS"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:160.1-160.61 *)
datatype vextternop__underscore =
	  mk_vextternop___0 "Jnn" "M" "Jnn" "M" "vextternop__Jnn_1_M_1_Jnn_2_M_2"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:160.8-160.21 *)
inductive wf_vextternop__underscore :: "ishape ⇒ ishape ⇒ vextternop__underscore ⇒ bool" where
	  vextternop___case_0 :
		"(wf_vextternop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 var_x) ⟹
		 (ishape_1 = (mk_ishape (X (lanetype_Jnn Jnn_1) (mk_dim M_1)))) ⟹
		 (ishape_2 = (mk_ishape (X (lanetype_Jnn Jnn_2) (mk_dim M_2)))) ⟹
		 wf_vextternop__underscore ishape_1 ishape_2 (mk_vextternop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:160.1-160.61 *)
function (sequential) proj_vextternop___0 :: "vextternop__underscore ⇒ vextternop__Jnn_1_M_1_Jnn_2_M_2" where
		  "proj_vextternop___0 (mk_vextternop___0 Jnn_1 M_1 Jnn_2 M_2 var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.1-165.55 *)
datatype vcvtop__Jnn_1_M_1_Jnn_2_M_2 =
	  vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND "half" "sx"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.8-165.17 *)
inductive wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 :: "Jnn ⇒ M ⇒ Jnn ⇒ M ⇒ vcvtop__Jnn_1_M_1_Jnn_2_M_2 ⇒ bool" where
	  vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0 :
		"((lsizenn2 (lanetype_Jnn Jnn_2)) = (2 * (lsizenn1 (lanetype_Jnn Jnn_1)))) ⟹
		 wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.1-165.55 *)
datatype vcvtop__Jnn_1_M_1_Fnn_2_M_2 =
	  vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT "(half option)" "sx"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.8-165.17 *)
inductive wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 :: "Jnn ⇒ M ⇒ Fnn ⇒ M ⇒ vcvtop__Jnn_1_M_1_Fnn_2_M_2 ⇒ bool" where
	  vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0 :
		"(((((sizenn2 (numtype_Fnn Fnn_2)) = (lsizenn1 (lanetype_Jnn Jnn_1))) ∧ ((lsizenn1 (lanetype_Jnn Jnn_1)) = 32)) ∧ (half_opt = None)) ∨ (((sizenn2 (numtype_Fnn Fnn_2)) = (2 * (lsizenn1 (lanetype_Jnn Jnn_1)))) ∧ (half_opt = (Some LOW)))) ⟹
		 wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 Jnn_1 M_1 Fnn_2 M_2 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.1-165.55 *)
datatype vcvtop__Fnn_1_M_1_Jnn_2_M_2 =
	  vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT "sx" "(zero option)"
	| RELAXED_TRUNC "sx" "(zero option)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.8-165.17 *)
inductive wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 :: "Fnn ⇒ M ⇒ Jnn ⇒ M ⇒ vcvtop__Fnn_1_M_1_Jnn_2_M_2 ⇒ bool" where
	  vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0 :
		"(((((sizenn1 (numtype_Fnn Fnn_1)) = (lsizenn2 (lanetype_Jnn Jnn_2))) ∧ ((lsizenn2 (lanetype_Jnn Jnn_2)) = 32)) ∧ (zero_opt = None)) ∨ (((sizenn1 (numtype_Fnn Fnn_1)) = (2 * (lsizenn2 (lanetype_Jnn Jnn_2)))) ∧ (zero_opt = (Some ZERO)))) ⟹
		 wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 Fnn_1 M_1 Jnn_2 M_2 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)"
	| vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_1 :
		"(((((sizenn1 (numtype_Fnn Fnn_1)) = (lsizenn2 (lanetype_Jnn Jnn_2))) ∧ ((lsizenn2 (lanetype_Jnn Jnn_2)) = 32)) ∧ (zero_opt = None)) ∨ (((sizenn1 (numtype_Fnn Fnn_1)) = (2 * (lsizenn2 (lanetype_Jnn Jnn_2)))) ∧ (zero_opt = (Some ZERO)))) ⟹
		 wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 Fnn_1 M_1 Jnn_2 M_2 (RELAXED_TRUNC v_sx zero_opt)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.1-165.55 *)
datatype vcvtop__Fnn_1_M_1_Fnn_2_M_2 =
	  vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE "zero"
	| PROMOTELOW

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.8-165.17 *)
inductive wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 :: "Fnn ⇒ M ⇒ Fnn ⇒ M ⇒ vcvtop__Fnn_1_M_1_Fnn_2_M_2 ⇒ bool" where
	  vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 :
		"((sizenn1 (numtype_Fnn Fnn_1)) = (2 * (sizenn2 (numtype_Fnn Fnn_2)))) ⟹
		 wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 Fnn_1 M_1 Fnn_2 M_2 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE v_zero)"
	| vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 :
		"((2 * (sizenn1 (numtype_Fnn Fnn_1))) = (sizenn2 (numtype_Fnn Fnn_2))) ⟹
		 wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 Fnn_1 M_1 Fnn_2 M_2 PROMOTELOW"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.1-165.55 *)
datatype vcvtop__underscore =
	  mk_vcvtop___0 "Jnn" "M" "Jnn" "M" "vcvtop__Jnn_1_M_1_Jnn_2_M_2"
	| mk_vcvtop___1 "Jnn" "M" "Fnn" "M" "vcvtop__Jnn_1_M_1_Fnn_2_M_2"
	| mk_vcvtop___2 "Fnn" "M" "Jnn" "M" "vcvtop__Fnn_1_M_1_Jnn_2_M_2"
	| mk_vcvtop___3 "Fnn" "M" "Fnn" "M" "vcvtop__Fnn_1_M_1_Fnn_2_M_2"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.8-165.17 *)
inductive wf_vcvtop__underscore :: "shape ⇒ shape ⇒ vcvtop__underscore ⇒ bool" where
	  vcvtop___case_0 :
		"(wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 var_x) ⟹
		 (shape_1 = (X (lanetype_Jnn Jnn_1) (mk_dim M_1))) ⟹
		 (shape_2 = (X (lanetype_Jnn Jnn_2) (mk_dim M_2))) ⟹
		 wf_vcvtop__underscore shape_1 shape_2 (mk_vcvtop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)"
	| vcvtop___case_1 :
		"(wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 Jnn_1 M_1 Fnn_2 M_2 var_x) ⟹
		 (shape_1 = (X (lanetype_Jnn Jnn_1) (mk_dim M_1))) ⟹
		 (shape_2 = (X (lanetype_Fnn Fnn_2) (mk_dim M_2))) ⟹
		 wf_vcvtop__underscore shape_1 shape_2 (mk_vcvtop___1 Jnn_1 M_1 Fnn_2 M_2 var_x)"
	| vcvtop___case_2 :
		"(wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 Fnn_1 M_1 Jnn_2 M_2 var_x) ⟹
		 (shape_1 = (X (lanetype_Fnn Fnn_1) (mk_dim M_1))) ⟹
		 (shape_2 = (X (lanetype_Jnn Jnn_2) (mk_dim M_2))) ⟹
		 wf_vcvtop__underscore shape_1 shape_2 (mk_vcvtop___2 Fnn_1 M_1 Jnn_2 M_2 var_x)"
	| vcvtop___case_3 :
		"(wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 Fnn_1 M_1 Fnn_2 M_2 var_x) ⟹
		 (shape_1 = (X (lanetype_Fnn Fnn_1) (mk_dim M_1))) ⟹
		 (shape_2 = (X (lanetype_Fnn Fnn_2) (mk_dim M_2))) ⟹
		 wf_vcvtop__underscore shape_1 shape_2 (mk_vcvtop___3 Fnn_1 M_1 Fnn_2 M_2 var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.1-165.55 *)
function (sequential) proj_vcvtop___0 :: "vcvtop__underscore ⇒ (vcvtop__Jnn_1_M_1_Jnn_2_M_2 option)" where
		  "proj_vcvtop___0 (mk_vcvtop___0 Jnn_1 M_1 Jnn_2 M_2 var_x) = (Some var_x)"
		| "proj_vcvtop___0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.1-165.55 *)
function (sequential) proj_vcvtop___1 :: "vcvtop__underscore ⇒ (vcvtop__Jnn_1_M_1_Fnn_2_M_2 option)" where
		  "proj_vcvtop___1 (mk_vcvtop___1 Jnn_1 M_1 Fnn_2 M_2 var_x) = (Some var_x)"
		| "proj_vcvtop___1 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.1-165.55 *)
function (sequential) proj_vcvtop___2 :: "vcvtop__underscore ⇒ (vcvtop__Fnn_1_M_1_Jnn_2_M_2 option)" where
		  "proj_vcvtop___2 (mk_vcvtop___2 Fnn_1 M_1 Jnn_2 M_2 var_x) = (Some var_x)"
		| "proj_vcvtop___2 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.1-165.55 *)
function (sequential) proj_vcvtop___3 :: "vcvtop__underscore ⇒ (vcvtop__Fnn_1_M_1_Fnn_2_M_2 option)" where
		  "proj_vcvtop___3 (mk_vcvtop___3 Fnn_1 M_1 Fnn_2 M_2 var_x) = (Some var_x)"
		| "proj_vcvtop___3 var_x = None"
	by pat_completeness auto

(* Record Creation Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:189.1-189.69 *)
record memarg =
	ALIGN :: "u32"
	OFFSET :: "u64"

definition append_memarg :: "memarg ⇒ memarg ⇒ memarg" where
	"append_memarg arg1 arg2 = ⦇
		ALIGN = ALIGN arg1,
		OFFSET = OFFSET arg1
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:189.8-189.14 *)
inductive wf_memarg :: "memarg ⇒ bool" where
	  memarg_case_underscore :
		"(wf_uN 32 var_0) ⟹
		 (wf_uN 64 var_1) ⟹
		 wf_memarg ⦇ ALIGN = var_0, OFFSET = var_1 ⦈"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:193.1-193.24 *)
datatype loadop_Inn =
	  mk_loadop_Inn "sz" "sx"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:193.8-193.16 *)
inductive wf_loadop_Inn :: "Inn ⇒ loadop_Inn ⇒ bool" where
	  loadop_Inn_case_0 :
		"(wf_sz v_sz) ⟹
		 ((proj_sz_0 v_sz) < (sizenn (numtype_addrtype v_Inn))) ⟹
		 wf_loadop_Inn v_Inn (mk_loadop_Inn v_sz v_sx)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:193.1-193.24 *)
datatype loadop_underscore =
	  mk_loadop__0 "Inn" "loadop_Inn"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:193.8-193.16 *)
inductive wf_loadop_underscore :: "numtype ⇒ loadop_underscore ⇒ bool" where
	  loadop__case_0 :
		"(wf_loadop_Inn v_Inn var_x) ⟹
		 (v_numtype = (numtype_addrtype v_Inn)) ⟹
		 wf_loadop_underscore v_numtype (mk_loadop__0 v_Inn var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:193.1-193.24 *)
function (sequential) proj_loadop__0 :: "loadop_underscore ⇒ loadop_Inn" where
		  "proj_loadop__0 (mk_loadop__0 v_Inn var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:196.1-196.25 *)
datatype storeop_Inn =
	  mk_storeop_Inn "sz"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:196.8-196.17 *)
inductive wf_storeop_Inn :: "Inn ⇒ storeop_Inn ⇒ bool" where
	  storeop_Inn_case_0 :
		"(wf_sz v_sz) ⟹
		 ((proj_sz_0 v_sz) < (sizenn (numtype_addrtype v_Inn))) ⟹
		 wf_storeop_Inn v_Inn (mk_storeop_Inn v_sz)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:196.1-196.25 *)
datatype storeop_underscore =
	  mk_storeop__0 "Inn" "storeop_Inn"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:196.8-196.17 *)
inductive wf_storeop_underscore :: "numtype ⇒ storeop_underscore ⇒ bool" where
	  storeop__case_0 :
		"(wf_storeop_Inn v_Inn var_x) ⟹
		 (v_numtype = (numtype_addrtype v_Inn)) ⟹
		 wf_storeop_underscore v_numtype (mk_storeop__0 v_Inn var_x)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:196.1-196.25 *)
function (sequential) proj_storeop__0 :: "storeop_underscore ⇒ storeop_Inn" where
		  "proj_storeop__0 (mk_storeop__0 v_Inn var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:199.1-202.59 *)
datatype vloadop_underscore =
	  SHAPEX_underscore "sz" "M" "sx"
	| SPLAT "sz"
	| vloadop__ZERO "sz"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:199.8-199.17 *)
inductive wf_vloadop_underscore :: "vectype ⇒ vloadop_underscore ⇒ bool" where
	  vloadop__case_0 :
		"(wf_sz v_sz) ⟹
		 ((((proj_sz_0 v_sz) * v_M) :: nat) = (((vsize v_vectype) :: nat) div (2 :: nat))) ⟹
		 wf_vloadop_underscore v_vectype (SHAPEX_underscore v_sz v_M v_sx)"
	| vloadop__case_1 :
		"(wf_sz v_sz) ⟹
		 wf_vloadop_underscore v_vectype (SPLAT v_sz)"
	| vloadop__case_2 :
		"(wf_sz v_sz) ⟹
		 ((proj_sz_0 v_sz) ≥ 32) ⟹
		 wf_vloadop_underscore v_vectype (vloadop__ZERO v_sz)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:207.1-209.17 *)
datatype blocktype =
	  underscore_RESULT "(valtype option)"
	| blocktype__IDX "typeidx"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:207.8-207.17 *)
inductive wf_blocktype :: "blocktype ⇒ bool" where
	  blocktype_case_0 :
		"list_all (λ (v_valtype :: valtype). (wf_valtype v_valtype)) (option_to_list valtype_opt) ⟹
		 wf_blocktype (underscore_RESULT valtype_opt)"
	| blocktype_case_1 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_blocktype (blocktype__IDX v_typeidx)"

(* Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:7.1-7.39 *)
type_synonym addr = "nat"

(* Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:16.1-16.51 *)
type_synonym arrayaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:17.1-17.53 *)
type_synonym exnaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:12.1-12.53 *)
type_synonym funcaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:18.1-18.49 *)
type_synonym hostaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:15.1-15.56 *)
type_synonym structaddr = "addr"

(* Mutual Recursion at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:35.1-42.23 *)
datatype addrref =
	  REF_I31_NUM "u31"
	| REF_STRUCT_ADDR "structaddr"
	| REF_ARRAY_ADDR "arrayaddr"
	| REF_FUNC_ADDR "funcaddr"
	| REF_EXN_ADDR "exnaddr"
	| REF_HOST_ADDR "hostaddr"
	| REF_EXTERN "addrref"

(* Mutual Recursion at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:35.1-42.23 *)
inductive wf_addrref :: "addrref ⇒ bool" where
	  addrref_case_0 :
		"(wf_uN 31 v_u31) ⟹
		 wf_addrref (REF_I31_NUM v_u31)"
	| addrref_case_1 :
		"wf_addrref (REF_STRUCT_ADDR v_structaddr)"
	| addrref_case_2 :
		"wf_addrref (REF_ARRAY_ADDR v_arrayaddr)"
	| addrref_case_3 :
		"wf_addrref (REF_FUNC_ADDR v_funcaddr)"
	| addrref_case_4 :
		"wf_addrref (REF_EXN_ADDR v_exnaddr)"
	| addrref_case_5 :
		"wf_addrref (REF_HOST_ADDR v_hostaddr)"
	| addrref_case_6 :
		"wf_addrref (REF_EXTERN v_addrref)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:257.1-261.27 *)
datatype catch =
	  CATCH "tagidx" "labelidx"
	| CATCH_REF "tagidx" "labelidx"
	| CATCH_ALL "labelidx"
	| CATCH_ALL_REF "labelidx"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:257.8-257.13 *)
inductive wf_catch :: "catch ⇒ bool" where
	  catch_case_0 :
		"(wf_uN 32 v_tagidx) ⟹
		 (wf_uN 32 v_labelidx) ⟹
		 wf_catch (CATCH v_tagidx v_labelidx)"
	| catch_case_1 :
		"(wf_uN 32 v_tagidx) ⟹
		 (wf_uN 32 v_labelidx) ⟹
		 wf_catch (CATCH_REF v_tagidx v_labelidx)"
	| catch_case_2 :
		"(wf_uN 32 v_labelidx) ⟹
		 wf_catch (CATCH_ALL v_labelidx)"
	| catch_case_3 :
		"(wf_uN 32 v_labelidx) ⟹
		 wf_catch (CATCH_ALL_REF v_labelidx)"

(* Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:13.1-13.49 *)
type_synonym dataaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:14.1-14.49 *)
type_synonym elemaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:9.1-9.53 *)
type_synonym globaladdr = "addr"

(* Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:10.1-10.50 *)
type_synonym memaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:11.1-11.51 *)
type_synonym tableaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:8.1-8.47 *)
type_synonym tagaddr = "addr"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:20.1-21.84 *)
datatype externaddr =
	  externaddr_TAG "tagaddr"
	| externaddr_GLOBAL "globaladdr"
	| externaddr_MEM "memaddr"
	| externaddr_TABLE "tableaddr"
	| externaddr_FUNC "funcaddr"

(* Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:84.1-85.33 *)
record exportinst =
	NAME :: "name"
	ADDR :: "externaddr"

definition append_exportinst :: "exportinst ⇒ exportinst ⇒ exportinst" where
	"append_exportinst arg1 arg2 = ⦇
		NAME = NAME arg1,
		ADDR = ADDR arg1
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:84.8-84.18 *)
inductive wf_exportinst :: "exportinst ⇒ bool" where
	  exportinst_case_underscore :
		"(wf_name var_0) ⟹
		 wf_exportinst ⦇ NAME = var_0, ADDR = var_1 ⦈"

(* Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:104.1-113.26 *)
record moduleinst =
	moduleinst_TYPES :: "(deftype list)"
	moduleinst_TAGS :: "(tagaddr list)"
	moduleinst_GLOBALS :: "(globaladdr list)"
	moduleinst_MEMS :: "(memaddr list)"
	moduleinst_TABLES :: "(tableaddr list)"
	moduleinst_FUNCS :: "(funcaddr list)"
	moduleinst_DATAS :: "(dataaddr list)"
	moduleinst_ELEMS :: "(elemaddr list)"
	EXPORTS :: "(exportinst list)"

definition append_moduleinst :: "moduleinst ⇒ moduleinst ⇒ moduleinst" where
	"append_moduleinst arg1 arg2 = ⦇
		moduleinst_TYPES = moduleinst_TYPES arg1 @ moduleinst_TYPES arg2,
		moduleinst_TAGS = moduleinst_TAGS arg1 @ moduleinst_TAGS arg2,
		moduleinst_GLOBALS = moduleinst_GLOBALS arg1 @ moduleinst_GLOBALS arg2,
		moduleinst_MEMS = moduleinst_MEMS arg1 @ moduleinst_MEMS arg2,
		moduleinst_TABLES = moduleinst_TABLES arg1 @ moduleinst_TABLES arg2,
		moduleinst_FUNCS = moduleinst_FUNCS arg1 @ moduleinst_FUNCS arg2,
		moduleinst_DATAS = moduleinst_DATAS arg1 @ moduleinst_DATAS arg2,
		moduleinst_ELEMS = moduleinst_ELEMS arg1 @ moduleinst_ELEMS arg2,
		EXPORTS = EXPORTS arg1 @ EXPORTS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:104.8-104.18 *)
inductive wf_moduleinst :: "moduleinst ⇒ bool" where
	  moduleinst_case_underscore :
		"list_all (λ (var_8 :: exportinst). (wf_exportinst var_8)) var_8 ⟹
		 wf_moduleinst ⦇ moduleinst_TYPES = var_0, moduleinst_TAGS = var_1, moduleinst_GLOBALS = var_2, moduleinst_MEMS = var_3, moduleinst_TABLES = var_4, moduleinst_FUNCS = var_5, moduleinst_DATAS = var_6, moduleinst_ELEMS = var_7, EXPORTS = var_8 ⦈"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:48.1-49.20 *)
datatype val =
	  res_CONST "numtype" "num_underscore"
	| VCONST "vectype" "vec_underscore"
	| val_REF_I31_NUM "u31"
	| val_REF_STRUCT_ADDR "structaddr"
	| val_REF_ARRAY_ADDR "arrayaddr"
	| val_REF_FUNC_ADDR "funcaddr"
	| val_REF_EXN_ADDR "exnaddr"
	| val_REF_HOST_ADDR "hostaddr"
	| val_REF_EXTERN "addrref"
	| REF_NULL "heaptype"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:48.8-48.11 *)
inductive wf_val :: "val ⇒ bool" where
	  val_case_0 :
		"(wf_num_underscore v_numtype var_0) ⟹
		 wf_val (res_CONST v_numtype var_0)"
	| val_case_1 :
		"(wf_uN (vsize v_vectype) var_0) ⟹
		 wf_val (VCONST v_vectype var_0)"
	| val_case_2 :
		"(wf_uN 31 v_u31) ⟹
		 wf_val (val_REF_I31_NUM v_u31)"
	| val_case_3 :
		"wf_val (val_REF_STRUCT_ADDR v_structaddr)"
	| val_case_4 :
		"wf_val (val_REF_ARRAY_ADDR v_arrayaddr)"
	| val_case_5 :
		"wf_val (val_REF_FUNC_ADDR v_funcaddr)"
	| val_case_6 :
		"wf_val (val_REF_EXN_ADDR v_exnaddr)"
	| val_case_7 :
		"wf_val (val_REF_HOST_ADDR v_hostaddr)"
	| val_case_8 :
		"(wf_addrref v_addrref) ⟹
		 wf_val (val_REF_EXTERN v_addrref)"
	| val_case_9 :
		"(wf_heaptype v_heaptype) ⟹
		 wf_val (REF_NULL v_heaptype)"

(* Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:130.1-131.40 *)
record frame =
	frame_LOCALS :: "((val option) list)"
	MODULE :: "moduleinst"

definition append_frame :: "frame ⇒ frame ⇒ frame" where
	"append_frame arg1 arg2 = ⦇
		frame_LOCALS = frame_LOCALS arg1 @ frame_LOCALS arg2,
		MODULE = append_moduleinst (MODULE arg1) (MODULE arg2)
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:130.8-130.13 *)
inductive wf_frame :: "frame ⇒ bool" where
	  frame_case_underscore :
		"list_all (λ (var_0 :: (val option)). list_all (λ (var_0 :: val). (wf_val var_0)) (option_to_list var_0)) var_0 ⟹
		 (wf_moduleinst var_1) ⟹
		 wf_frame ⦇ frame_LOCALS = var_0, MODULE = var_1 ⦈"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:136.1-142.9 *)
datatype instr_st8 =
	  VEXTRACT_LANE "shape" "(sx option)" "laneidx"
	| VSPLAT "shape"
	| VCVTOP "shape" "shape" "vcvtop__underscore"
	| VNARROW "ishape" "ishape" "sx"
	| VEXTTERNOP "ishape" "ishape" "vextternop__underscore"
	| VEXTBINOP "ishape" "ishape" "vextbinop__underscore"
	| VEXTUNOP "ishape" "ishape" "vextunop__underscore"
	| VSHUFFLE "bshape" "(laneidx list)"
	| VSWIZZLOP "bshape" "vswizzlop_underscore"
	| VBITMASK "ishape"
	| VSHIFTOP "ishape" "vshiftop_underscore"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:136.1-142.9 *)
datatype instr_st7 =
	  VRELOP "shape" "vrelop_underscore"
	| VTESTOP "shape" "vtestop_underscore"
	| VTERNOP "shape" "vternop_underscore"
	| VBINOP "shape" "vbinop_underscore"
	| VUNOP "shape" "vunop_underscore"
	| VVTESTOP "vectype" "vvtestop"
	| VVTERNOP "vectype" "vvternop"
	| VVBINOP "vectype" "vvbinop"
	| VVUNOP "vectype" "vvunop"
	| instr_st7_VCONST "vectype" "vec_underscore"
	| CVTOP "numtype" "numtype" "cvtop__underscore"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:136.1-142.9 *)
datatype instr_st6 =
	  RELOP "numtype" "relop_underscore"
	| TESTOP "numtype" "testop_underscore"
	| BINOP "numtype" "binop_underscore"
	| UNOP "numtype" "unop_underscore"
	| instr_st6_CONST "numtype" "num_underscore"
	| ANY_CONVERT_EXTERN
	| EXTERN_CONVERT_ANY
	| ARRAY_INIT_ELEM "typeidx" "elemidx"
	| ARRAY_INIT_DATA "typeidx" "dataidx"
	| ARRAY_COPY "typeidx" "typeidx"
	| ARRAY_FILL "typeidx"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:136.1-142.9 *)
datatype instr_st5 =
	  ARRAY_LEN
	| ARRAY_SET "typeidx"
	| ARRAY_GET "(sx option)" "typeidx"
	| ARRAY_NEW_ELEM "typeidx" "elemidx"
	| ARRAY_NEW_DATA "typeidx" "dataidx"
	| ARRAY_NEW_FIXED "typeidx" "u32"
	| ARRAY_NEW_DEFAULT "typeidx"
	| ARRAY_NEW "typeidx"
	| STRUCT_SET "typeidx" "u32"
	| STRUCT_GET "(sx option)" "typeidx" "u32"
	| STRUCT_NEW_DEFAULT "typeidx"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:136.1-142.9 *)
datatype instr_st4 =
	  STRUCT_NEW "typeidx"
	| I31_GET "sx"
	| REF_I31
	| REF_FUNC "funcidx"
	| REF_CAST "reftype"
	| REF_TEST "reftype"
	| REF_EQ
	| REF_AS_NON_NULL
	| REF_IS_NULL
	| instr_st4_REF_NULL "heaptype"
	| DATA_DROP "dataidx"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:136.1-142.9 *)
datatype instr_st3 =
	  MEMORY_INIT "memidx" "dataidx"
	| MEMORY_COPY "memidx" "memidx"
	| MEMORY_FILL "memidx"
	| MEMORY_GROW "memidx"
	| MEMORY_SIZE "memidx"
	| VSTORE_LANE "vectype" "sz" "memidx" "memarg" "laneidx"
	| VSTORE "vectype" "memidx" "memarg"
	| VLOAD_LANE "vectype" "sz" "memidx" "memarg" "laneidx"
	| VLOAD "vectype" "(vloadop_underscore option)" "memidx" "memarg"
	| STORE "numtype" "(storeop_underscore option)" "memidx" "memarg"
	| LOAD "numtype" "(loadop_underscore option)" "memidx" "memarg"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:136.1-142.9 *)
datatype instr_st2 =
	  ELEM_DROP "elemidx"
	| TABLE_INIT "tableidx" "elemidx"
	| TABLE_COPY "tableidx" "tableidx"
	| TABLE_FILL "tableidx"
	| TABLE_GROW "tableidx"
	| TABLE_SIZE "tableidx"
	| TABLE_SET "tableidx"
	| TABLE_GET "tableidx"
	| GLOBAL_SET "globalidx"
	| GLOBAL_GET "globalidx"
	| LOCAL_TEE "localidx"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:136.1-142.9 *)
datatype instr_st1 =
	  LOCAL_SET "localidx"
	| LOCAL_GET "localidx"
	| THROW_REF
	| THROW "tagidx"
	| RETURN_CALL_INDIRECT "tableidx" "typeuse"
	| RETURN_CALL_REF "typeuse"
	| RETURN_CALL "funcidx"
	| RETURN
	| CALL_INDIRECT "tableidx" "typeuse"
	| CALL_REF "typeuse"
	| CALL "funcidx"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:136.1-142.9 *)
datatype instr_st0 =
	  BR_ON_CAST_FAIL "labelidx" "reftype" "reftype"
	| BR_ON_CAST "labelidx" "reftype" "reftype"
	| BR_ON_NON_NULL "labelidx"
	| BR_ON_NULL "labelidx"
	| BR_TABLE "(labelidx list)" "labelidx"
	| BR_IF "labelidx"
	| BR "labelidx"
	| SELECT "((valtype list) option)"
	| DROP
	| UNREACHABLE
	| NOP

(* Mutual Recursion at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:136.1-142.9 *)
datatype instr =
	  instr_sc0 "instr_st0"
	| instr_sc1 "instr_st1"
	| instr_sc2 "instr_st2"
	| instr_sc3 "instr_st3"
	| instr_sc4 "instr_st4"
	| instr_sc5 "instr_st5"
	| instr_sc6 "instr_st6"
	| instr_sc7 "instr_st7"
	| instr_sc8 "instr_st8"
	| instr_sc9 "instr_st9"
	| instr_sc10 "instr_st10"

and

instr_st9 =
	  LOOP "blocktype" "(instr list)"
	| BLOCK "blocktype" "(instr list)"
	| TRAP
	| instr_st9_REF_EXTERN "addrref"
	| instr_st9_REF_HOST_ADDR "hostaddr"
	| instr_st9_REF_EXN_ADDR "exnaddr"
	| instr_st9_REF_FUNC_ADDR "funcaddr"
	| instr_st9_REF_ARRAY_ADDR "arrayaddr"
	| instr_st9_REF_STRUCT_ADDR "structaddr"
	| instr_st9_REF_I31_NUM "u31"
	| VREPLACE_LANE "shape" "laneidx"

and

instr_st10 =
	  HANDLER_underscore "n" "(catch list)" "(instr list)"
	| FRAME_underscore "n" "frame" "(instr list)"
	| LABEL_underscore "n" "(instr list)" "(instr list)"
	| TRY_TABLE "blocktype" "(catch res_list)" "(instr list)"
	| IFELSE "blocktype" "(instr list)" "(instr list)"

(* Auxiliary Definition at:  *)
function (sequential) instr_addrref :: "addrref ⇒ instr" where
		  "instr_addrref (REF_I31_NUM x0) = (instr_sc9 (instr_st9_REF_I31_NUM x0))"
		| "instr_addrref (REF_STRUCT_ADDR x0) = (instr_sc9 (instr_st9_REF_STRUCT_ADDR x0))"
		| "instr_addrref (REF_ARRAY_ADDR x0) = (instr_sc9 (instr_st9_REF_ARRAY_ADDR x0))"
		| "instr_addrref (REF_FUNC_ADDR x0) = (instr_sc9 (instr_st9_REF_FUNC_ADDR x0))"
		| "instr_addrref (REF_EXN_ADDR x0) = (instr_sc9 (instr_st9_REF_EXN_ADDR x0))"
		| "instr_addrref (REF_HOST_ADDR x0) = (instr_sc9 (instr_st9_REF_HOST_ADDR x0))"
		| "instr_addrref (REF_EXTERN x0) = (instr_sc9 (instr_st9_REF_EXTERN x0))"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) instr_val :: "val ⇒ instr" where
		  "instr_val (res_CONST x0 x1) = (instr_sc6 (instr_st6_CONST x0 x1))"
		| "instr_val (VCONST x0 x1) = (instr_sc7 (instr_st7_VCONST x0 x1))"
		| "instr_val (val_REF_I31_NUM x0) = (instr_sc9 (instr_st9_REF_I31_NUM x0))"
		| "instr_val (val_REF_STRUCT_ADDR x0) = (instr_sc9 (instr_st9_REF_STRUCT_ADDR x0))"
		| "instr_val (val_REF_ARRAY_ADDR x0) = (instr_sc9 (instr_st9_REF_ARRAY_ADDR x0))"
		| "instr_val (val_REF_FUNC_ADDR x0) = (instr_sc9 (instr_st9_REF_FUNC_ADDR x0))"
		| "instr_val (val_REF_EXN_ADDR x0) = (instr_sc9 (instr_st9_REF_EXN_ADDR x0))"
		| "instr_val (val_REF_HOST_ADDR x0) = (instr_sc9 (instr_st9_REF_HOST_ADDR x0))"
		| "instr_val (val_REF_EXTERN x0) = (instr_sc9 (instr_st9_REF_EXTERN x0))"
		| "instr_val (REF_NULL x0) = (instr_sc4 (instr_st4_REF_NULL x0))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:136.1-142.9 *)
inductive wf_instr :: "instr ⇒ bool" where
	  instr_case_0 :
		"wf_instr (instr_sc0 NOP)"
	| instr_case_1 :
		"wf_instr (instr_sc0 UNREACHABLE)"
	| instr_case_2 :
		"wf_instr (instr_sc0 DROP)"
	| instr_case_3 :
		"list_all (λ (valtype_lst :: (valtype list)). list_all (λ (v_valtype :: valtype). (wf_valtype v_valtype)) valtype_lst) (option_to_list valtype_lst_opt) ⟹
		 wf_instr (instr_sc0 (SELECT valtype_lst_opt))"
	| instr_case_4 :
		"(wf_blocktype v_blocktype) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_instr (instr_sc9 (BLOCK v_blocktype instr_lst))"
	| instr_case_5 :
		"(wf_blocktype v_blocktype) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_instr (instr_sc9 (LOOP v_blocktype instr_lst))"
	| instr_case_6 :
		"(wf_blocktype v_blocktype) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 list_all (λ (instr_lst_0 :: instr). (wf_instr instr_lst_0)) instr_lst_0 ⟹
		 wf_instr (instr_sc10 (IFELSE v_blocktype instr_lst instr_lst_0))"
	| instr_case_7 :
		"(wf_uN 32 v_labelidx) ⟹
		 wf_instr (instr_sc0 (BR v_labelidx))"
	| instr_case_8 :
		"(wf_uN 32 v_labelidx) ⟹
		 wf_instr (instr_sc0 (BR_IF v_labelidx))"
	| instr_case_9 :
		"list_all (λ (v_labelidx :: labelidx). (wf_uN 32 v_labelidx)) labelidx_lst ⟹
		 (wf_uN 32 v_labelidx) ⟹
		 wf_instr (instr_sc0 (BR_TABLE labelidx_lst v_labelidx))"
	| instr_case_10 :
		"(wf_uN 32 v_labelidx) ⟹
		 wf_instr (instr_sc0 (BR_ON_NULL v_labelidx))"
	| instr_case_11 :
		"(wf_uN 32 v_labelidx) ⟹
		 wf_instr (instr_sc0 (BR_ON_NON_NULL v_labelidx))"
	| instr_case_12 :
		"(wf_uN 32 v_labelidx) ⟹
		 (wf_reftype v_reftype) ⟹
		 (wf_reftype reftype_0) ⟹
		 wf_instr (instr_sc0 (BR_ON_CAST v_labelidx v_reftype reftype_0))"
	| instr_case_13 :
		"(wf_uN 32 v_labelidx) ⟹
		 (wf_reftype v_reftype) ⟹
		 (wf_reftype reftype_0) ⟹
		 wf_instr (instr_sc0 (BR_ON_CAST_FAIL v_labelidx v_reftype reftype_0))"
	| instr_case_14 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_instr (instr_sc1 (CALL v_funcidx))"
	| instr_case_15 :
		"(wf_typeuse v_typeuse) ⟹
		 wf_instr (instr_sc1 (CALL_REF v_typeuse))"
	| instr_case_16 :
		"(wf_uN 32 v_tableidx) ⟹
		 (wf_typeuse v_typeuse) ⟹
		 wf_instr (instr_sc1 (CALL_INDIRECT v_tableidx v_typeuse))"
	| instr_case_17 :
		"wf_instr (instr_sc1 RETURN)"
	| instr_case_18 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_instr (instr_sc1 (RETURN_CALL v_funcidx))"
	| instr_case_19 :
		"(wf_typeuse v_typeuse) ⟹
		 wf_instr (instr_sc1 (RETURN_CALL_REF v_typeuse))"
	| instr_case_20 :
		"(wf_uN 32 v_tableidx) ⟹
		 (wf_typeuse v_typeuse) ⟹
		 wf_instr (instr_sc1 (RETURN_CALL_INDIRECT v_tableidx v_typeuse))"
	| instr_case_21 :
		"(wf_uN 32 v_tagidx) ⟹
		 wf_instr (instr_sc1 (THROW v_tagidx))"
	| instr_case_22 :
		"wf_instr (instr_sc1 THROW_REF)"
	| instr_case_23 :
		"(wf_blocktype v_blocktype) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_instr (instr_sc10 (TRY_TABLE v_blocktype var_0 instr_lst))"
	| instr_case_24 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_instr (instr_sc1 (LOCAL_GET v_localidx))"
	| instr_case_25 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_instr (instr_sc1 (LOCAL_SET v_localidx))"
	| instr_case_26 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_instr (instr_sc2 (LOCAL_TEE v_localidx))"
	| instr_case_27 :
		"(wf_uN 32 v_globalidx) ⟹
		 wf_instr (instr_sc2 (GLOBAL_GET v_globalidx))"
	| instr_case_28 :
		"(wf_uN 32 v_globalidx) ⟹
		 wf_instr (instr_sc2 (GLOBAL_SET v_globalidx))"
	| instr_case_29 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_instr (instr_sc2 (TABLE_GET v_tableidx))"
	| instr_case_30 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_instr (instr_sc2 (TABLE_SET v_tableidx))"
	| instr_case_31 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_instr (instr_sc2 (TABLE_SIZE v_tableidx))"
	| instr_case_32 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_instr (instr_sc2 (TABLE_GROW v_tableidx))"
	| instr_case_33 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_instr (instr_sc2 (TABLE_FILL v_tableidx))"
	| instr_case_34 :
		"(wf_uN 32 v_tableidx) ⟹
		 (wf_uN 32 tableidx_0) ⟹
		 wf_instr (instr_sc2 (TABLE_COPY v_tableidx tableidx_0))"
	| instr_case_35 :
		"(wf_uN 32 v_tableidx) ⟹
		 (wf_uN 32 v_elemidx) ⟹
		 wf_instr (instr_sc2 (TABLE_INIT v_tableidx v_elemidx))"
	| instr_case_36 :
		"(wf_uN 32 v_elemidx) ⟹
		 wf_instr (instr_sc2 (ELEM_DROP v_elemidx))"
	| instr_case_37 :
		"list_all (λ (var_0 :: loadop_underscore). (wf_loadop_underscore v_numtype var_0)) (option_to_list var_0) ⟹
		 (wf_uN 32 v_memidx) ⟹
		 (wf_memarg v_memarg) ⟹
		 wf_instr (instr_sc3 (LOAD v_numtype var_0 v_memidx v_memarg))"
	| instr_case_38 :
		"list_all (λ (var_0 :: storeop_underscore). (wf_storeop_underscore v_numtype var_0)) (option_to_list var_0) ⟹
		 (wf_uN 32 v_memidx) ⟹
		 (wf_memarg v_memarg) ⟹
		 wf_instr (instr_sc3 (STORE v_numtype var_0 v_memidx v_memarg))"
	| instr_case_39 :
		"list_all (λ (var_0 :: vloadop_underscore). (wf_vloadop_underscore v_vectype var_0)) (option_to_list var_0) ⟹
		 (wf_uN 32 v_memidx) ⟹
		 (wf_memarg v_memarg) ⟹
		 wf_instr (instr_sc3 (VLOAD v_vectype var_0 v_memidx v_memarg))"
	| instr_case_40 :
		"(wf_sz v_sz) ⟹
		 (wf_uN 32 v_memidx) ⟹
		 (wf_memarg v_memarg) ⟹
		 (wf_uN 8 v_laneidx) ⟹
		 wf_instr (instr_sc3 (VLOAD_LANE v_vectype v_sz v_memidx v_memarg v_laneidx))"
	| instr_case_41 :
		"(wf_uN 32 v_memidx) ⟹
		 (wf_memarg v_memarg) ⟹
		 wf_instr (instr_sc3 (VSTORE v_vectype v_memidx v_memarg))"
	| instr_case_42 :
		"(wf_sz v_sz) ⟹
		 (wf_uN 32 v_memidx) ⟹
		 (wf_memarg v_memarg) ⟹
		 (wf_uN 8 v_laneidx) ⟹
		 wf_instr (instr_sc3 (VSTORE_LANE v_vectype v_sz v_memidx v_memarg v_laneidx))"
	| instr_case_43 :
		"(wf_uN 32 v_memidx) ⟹
		 wf_instr (instr_sc3 (MEMORY_SIZE v_memidx))"
	| instr_case_44 :
		"(wf_uN 32 v_memidx) ⟹
		 wf_instr (instr_sc3 (MEMORY_GROW v_memidx))"
	| instr_case_45 :
		"(wf_uN 32 v_memidx) ⟹
		 wf_instr (instr_sc3 (MEMORY_FILL v_memidx))"
	| instr_case_46 :
		"(wf_uN 32 v_memidx) ⟹
		 (wf_uN 32 memidx_0) ⟹
		 wf_instr (instr_sc3 (MEMORY_COPY v_memidx memidx_0))"
	| instr_case_47 :
		"(wf_uN 32 v_memidx) ⟹
		 (wf_uN 32 v_dataidx) ⟹
		 wf_instr (instr_sc3 (MEMORY_INIT v_memidx v_dataidx))"
	| instr_case_48 :
		"(wf_uN 32 v_dataidx) ⟹
		 wf_instr (instr_sc4 (DATA_DROP v_dataidx))"
	| instr_case_49 :
		"(wf_heaptype v_heaptype) ⟹
		 wf_instr (instr_sc4 (instr_st4_REF_NULL v_heaptype))"
	| instr_case_50 :
		"wf_instr (instr_sc4 REF_IS_NULL)"
	| instr_case_51 :
		"wf_instr (instr_sc4 REF_AS_NON_NULL)"
	| instr_case_52 :
		"wf_instr (instr_sc4 REF_EQ)"
	| instr_case_53 :
		"(wf_reftype v_reftype) ⟹
		 wf_instr (instr_sc4 (REF_TEST v_reftype))"
	| instr_case_54 :
		"(wf_reftype v_reftype) ⟹
		 wf_instr (instr_sc4 (REF_CAST v_reftype))"
	| instr_case_55 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_instr (instr_sc4 (REF_FUNC v_funcidx))"
	| instr_case_56 :
		"wf_instr (instr_sc4 REF_I31)"
	| instr_case_57 :
		"wf_instr (instr_sc4 (I31_GET v_sx))"
	| instr_case_58 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_instr (instr_sc4 (STRUCT_NEW v_typeidx))"
	| instr_case_59 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_instr (instr_sc5 (STRUCT_NEW_DEFAULT v_typeidx))"
	| instr_case_60 :
		"(wf_uN 32 v_typeidx) ⟹
		 (wf_uN 32 v_u32) ⟹
		 wf_instr (instr_sc5 (STRUCT_GET sx_opt v_typeidx v_u32))"
	| instr_case_61 :
		"(wf_uN 32 v_typeidx) ⟹
		 (wf_uN 32 v_u32) ⟹
		 wf_instr (instr_sc5 (STRUCT_SET v_typeidx v_u32))"
	| instr_case_62 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_instr (instr_sc5 (ARRAY_NEW v_typeidx))"
	| instr_case_63 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_instr (instr_sc5 (ARRAY_NEW_DEFAULT v_typeidx))"
	| instr_case_64 :
		"(wf_uN 32 v_typeidx) ⟹
		 (wf_uN 32 v_u32) ⟹
		 wf_instr (instr_sc5 (ARRAY_NEW_FIXED v_typeidx v_u32))"
	| instr_case_65 :
		"(wf_uN 32 v_typeidx) ⟹
		 (wf_uN 32 v_dataidx) ⟹
		 wf_instr (instr_sc5 (ARRAY_NEW_DATA v_typeidx v_dataidx))"
	| instr_case_66 :
		"(wf_uN 32 v_typeidx) ⟹
		 (wf_uN 32 v_elemidx) ⟹
		 wf_instr (instr_sc5 (ARRAY_NEW_ELEM v_typeidx v_elemidx))"
	| instr_case_67 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_instr (instr_sc5 (ARRAY_GET sx_opt v_typeidx))"
	| instr_case_68 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_instr (instr_sc5 (ARRAY_SET v_typeidx))"
	| instr_case_69 :
		"wf_instr (instr_sc5 ARRAY_LEN)"
	| instr_case_70 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_instr (instr_sc6 (ARRAY_FILL v_typeidx))"
	| instr_case_71 :
		"(wf_uN 32 v_typeidx) ⟹
		 (wf_uN 32 typeidx_0) ⟹
		 wf_instr (instr_sc6 (ARRAY_COPY v_typeidx typeidx_0))"
	| instr_case_72 :
		"(wf_uN 32 v_typeidx) ⟹
		 (wf_uN 32 v_dataidx) ⟹
		 wf_instr (instr_sc6 (ARRAY_INIT_DATA v_typeidx v_dataidx))"
	| instr_case_73 :
		"(wf_uN 32 v_typeidx) ⟹
		 (wf_uN 32 v_elemidx) ⟹
		 wf_instr (instr_sc6 (ARRAY_INIT_ELEM v_typeidx v_elemidx))"
	| instr_case_74 :
		"wf_instr (instr_sc6 EXTERN_CONVERT_ANY)"
	| instr_case_75 :
		"wf_instr (instr_sc6 ANY_CONVERT_EXTERN)"
	| instr_case_76 :
		"(wf_num_underscore v_numtype var_0) ⟹
		 wf_instr (instr_sc6 (instr_st6_CONST v_numtype var_0))"
	| instr_case_77 :
		"(wf_unop_underscore v_numtype var_0) ⟹
		 wf_instr (instr_sc6 (UNOP v_numtype var_0))"
	| instr_case_78 :
		"(wf_binop_underscore v_numtype var_0) ⟹
		 wf_instr (instr_sc6 (BINOP v_numtype var_0))"
	| instr_case_79 :
		"(wf_testop_underscore v_numtype var_0) ⟹
		 wf_instr (instr_sc6 (TESTOP v_numtype var_0))"
	| instr_case_80 :
		"(wf_relop_underscore v_numtype var_0) ⟹
		 wf_instr (instr_sc6 (RELOP v_numtype var_0))"
	| instr_case_81 :
		"(wf_cvtop__underscore numtype_2 numtype_1 var_0) ⟹
		 wf_instr (instr_sc7 (CVTOP numtype_1 numtype_2 var_0))"
	| instr_case_82 :
		"(wf_uN (vsize v_vectype) var_0) ⟹
		 wf_instr (instr_sc7 (instr_st7_VCONST v_vectype var_0))"
	| instr_case_83 :
		"wf_instr (instr_sc7 (VVUNOP v_vectype v_vvunop))"
	| instr_case_84 :
		"wf_instr (instr_sc7 (VVBINOP v_vectype v_vvbinop))"
	| instr_case_85 :
		"wf_instr (instr_sc7 (VVTERNOP v_vectype v_vvternop))"
	| instr_case_86 :
		"wf_instr (instr_sc7 (VVTESTOP v_vectype v_vvtestop))"
	| instr_case_87 :
		"(wf_shape v_shape) ⟹
		 (wf_vunop_underscore v_shape var_0) ⟹
		 wf_instr (instr_sc7 (VUNOP v_shape var_0))"
	| instr_case_88 :
		"(wf_shape v_shape) ⟹
		 (wf_vbinop_underscore v_shape var_0) ⟹
		 wf_instr (instr_sc7 (VBINOP v_shape var_0))"
	| instr_case_89 :
		"(wf_shape v_shape) ⟹
		 (wf_vternop_underscore v_shape var_0) ⟹
		 wf_instr (instr_sc7 (VTERNOP v_shape var_0))"
	| instr_case_90 :
		"(wf_shape v_shape) ⟹
		 (wf_vtestop_underscore v_shape var_0) ⟹
		 wf_instr (instr_sc7 (VTESTOP v_shape var_0))"
	| instr_case_91 :
		"(wf_shape v_shape) ⟹
		 (wf_vrelop_underscore v_shape var_0) ⟹
		 wf_instr (instr_sc7 (VRELOP v_shape var_0))"
	| instr_case_92 :
		"(wf_ishape v_ishape) ⟹
		 (wf_vshiftop_underscore v_ishape var_0) ⟹
		 wf_instr (instr_sc8 (VSHIFTOP v_ishape var_0))"
	| instr_case_93 :
		"(wf_ishape v_ishape) ⟹
		 wf_instr (instr_sc8 (VBITMASK v_ishape))"
	| instr_case_94 :
		"(wf_bshape v_bshape) ⟹
		 (wf_vswizzlop_underscore v_bshape var_0) ⟹
		 wf_instr (instr_sc8 (VSWIZZLOP v_bshape var_0))"
	| instr_case_95 :
		"(wf_bshape v_bshape) ⟹
		 list_all (λ (v_laneidx :: laneidx). (wf_uN 8 v_laneidx)) laneidx_lst ⟹
		 ((mk_dim (length laneidx_lst)) = (fun_dim (proj_bshape_0 v_bshape))) ⟹
		 wf_instr (instr_sc8 (VSHUFFLE v_bshape laneidx_lst))"
	| instr_case_96 :
		"(wf_ishape ishape_1) ⟹
		 (wf_ishape ishape_2) ⟹
		 (wf_vextunop__underscore ishape_2 ishape_1 var_0) ⟹
		 wf_instr (instr_sc8 (VEXTUNOP ishape_1 ishape_2 var_0))"
	| instr_case_97 :
		"(wf_ishape ishape_1) ⟹
		 (wf_ishape ishape_2) ⟹
		 (wf_vextbinop__underscore ishape_2 ishape_1 var_0) ⟹
		 wf_instr (instr_sc8 (VEXTBINOP ishape_1 ishape_2 var_0))"
	| instr_case_98 :
		"(wf_ishape ishape_1) ⟹
		 (wf_ishape ishape_2) ⟹
		 (wf_vextternop__underscore ishape_2 ishape_1 var_0) ⟹
		 wf_instr (instr_sc8 (VEXTTERNOP ishape_1 ishape_2 var_0))"
	| instr_case_99 :
		"(wf_ishape ishape_1) ⟹
		 (wf_ishape ishape_2) ⟹
		 (((lsize (fun_lanetype (proj_ishape_0 ishape_2))) = (2 * (lsize (fun_lanetype (proj_ishape_0 ishape_1))))) ∧ ((2 * (lsize (fun_lanetype (proj_ishape_0 ishape_1)))) ≤ 32)) ⟹
		 wf_instr (instr_sc8 (VNARROW ishape_1 ishape_2 v_sx))"
	| instr_case_100 :
		"(wf_shape shape_1) ⟹
		 (wf_shape shape_2) ⟹
		 (wf_vcvtop__underscore shape_2 shape_1 var_0) ⟹
		 wf_instr (instr_sc8 (VCVTOP shape_1 shape_2 var_0))"
	| instr_case_101 :
		"(wf_shape v_shape) ⟹
		 wf_instr (instr_sc8 (VSPLAT v_shape))"
	| instr_case_102 :
		"(wf_shape v_shape) ⟹
		 (wf_uN 8 v_laneidx) ⟹
		 ((sx_opt = None) ⟷ ((fun_lanetype v_shape) ∈ set [lanetype_I32, lanetype_I64, lanetype_F32, lanetype_F64])) ⟹
		 wf_instr (instr_sc8 (VEXTRACT_LANE v_shape sx_opt v_laneidx))"
	| instr_case_103 :
		"(wf_shape v_shape) ⟹
		 (wf_uN 8 v_laneidx) ⟹
		 wf_instr (instr_sc9 (VREPLACE_LANE v_shape v_laneidx))"
	| instr_case_104 :
		"(wf_uN 31 v_u31) ⟹
		 wf_instr (instr_sc9 (instr_st9_REF_I31_NUM v_u31))"
	| instr_case_105 :
		"wf_instr (instr_sc9 (instr_st9_REF_STRUCT_ADDR v_structaddr))"
	| instr_case_106 :
		"wf_instr (instr_sc9 (instr_st9_REF_ARRAY_ADDR v_arrayaddr))"
	| instr_case_107 :
		"wf_instr (instr_sc9 (instr_st9_REF_FUNC_ADDR v_funcaddr))"
	| instr_case_108 :
		"wf_instr (instr_sc9 (instr_st9_REF_EXN_ADDR v_exnaddr))"
	| instr_case_109 :
		"wf_instr (instr_sc9 (instr_st9_REF_HOST_ADDR v_hostaddr))"
	| instr_case_110 :
		"(wf_addrref v_addrref) ⟹
		 wf_instr (instr_sc9 (instr_st9_REF_EXTERN v_addrref))"
	| instr_case_111 :
		"list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 list_all (λ (instr_lst_0 :: instr). (wf_instr instr_lst_0)) instr_lst_0 ⟹
		 wf_instr (instr_sc10 (LABEL_underscore v_n instr_lst instr_lst_0))"
	| instr_case_112 :
		"(wf_frame v_frame) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_instr (instr_sc10 (FRAME_underscore v_n v_frame instr_lst))"
	| instr_case_113 :
		"list_all (λ (v_catch :: catch). (wf_catch v_catch)) catch_lst ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_instr (instr_sc10 (HANDLER_underscore v_n catch_lst instr_lst))"
	| instr_case_114 :
		"wf_instr (instr_sc9 TRAP)"

(* Type Alias Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:394.1-395.9 *)
type_synonym expr = "(instr list)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:406.1-406.35 *)
definition memarg0 :: "memarg" where
	"memarg0 = ⦇ ALIGN = (mk_uN 0), OFFSET = (mk_uN 0) ⦈"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:409.1-409.69 *)
function (sequential) const :: "consttype ⇒ lit_underscore ⇒ instr" where
		  "const consttype_I32 (mk_lit__0 numtype_I32 c) = (instr_sc6 (instr_st6_CONST numtype_I32 c))"
		| "const consttype_I64 (mk_lit__0 numtype_I64 c) = (instr_sc6 (instr_st6_CONST numtype_I64 c))"
		| "const consttype_F32 (mk_lit__0 F32 c) = (instr_sc6 (instr_st6_CONST F32 c))"
		| "const consttype_F64 (mk_lit__0 F64 c) = (instr_sc6 (instr_st6_CONST F64 c))"
		| "const consttype_V128 (mk_lit__1 V128 c) = (instr_sc7 (instr_st7_VCONST V128 c))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:416.1-416.30 *)
function (sequential) free_shape :: "shape ⇒ free" where
		  "free_shape (X v_lanetype v_dim) = (free_lanetype v_lanetype)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:417.6-417.21 *)
inductive fun_free_blocktype :: "blocktype ⇒ free ⇒ bool" where
	  fun_free_blocktype_case_0 :
		"((var_0_opt = None) ⟷ (valtype_opt = None)) ⟹
		 list_all2 (λ (var_0 :: free) (v_valtype :: valtype). (fun_free_valtype v_valtype var_0)) (option_to_list var_0_opt) (option_to_list valtype_opt) ⟹
		 fun_free_blocktype (underscore_RESULT valtype_opt) (free_opt var_0_opt)"
	| fun_free_blocktype_case_1 :
		"fun_free_blocktype (blocktype__IDX v_typeidx) (free_typeidx v_typeidx)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:418.1-418.30 *)
function (sequential) free_catch :: "catch ⇒ free" where
		  "free_catch (CATCH v_tagidx v_labelidx) = (append_free (free_tagidx v_tagidx) (free_labelidx v_labelidx))"
		| "free_catch (CATCH_REF v_tagidx v_labelidx) = (append_free (free_tagidx v_tagidx) (free_labelidx v_labelidx))"
		| "free_catch (CATCH_ALL v_labelidx) = (free_labelidx v_labelidx)"
		| "free_catch (CATCH_ALL_REF v_labelidx) = (free_labelidx v_labelidx)"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:586.1-586.44 *)
inductive fun_shift_labelidxs :: "(labelidx list) ⇒ (labelidx list) ⇒ bool" where
	  fun_shift_labelidxs_case_0 :
		"fun_shift_labelidxs [] []"
	| fun_shift_labelidxs_case_1 :
		"(fun_shift_labelidxs labelidx'_lst var_0) ⟹
		 fun_shift_labelidxs ([(mk_uN 0)] @ labelidx'_lst) var_0"
	| fun_shift_labelidxs_case_2 :
		"(fun_shift_labelidxs labelidx'_lst var_0) ⟹
		 fun_shift_labelidxs ([v_labelidx] @ labelidx'_lst) ([(mk_uN ((((proj_uN_0 v_labelidx) :: nat) - (1 :: nat)) :: nat))] @ var_0)"

(* Mutual Recursion at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:420.1-421.31 *)
inductive fun_free_instr :: "instr ⇒ free ⇒ bool"
and fun_free_block :: "(instr list) ⇒ free ⇒ bool" where
	  fun_free_instr_case_0 :
		"fun_free_instr (instr_sc0 NOP) ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_instr_case_1 :
		"fun_free_instr (instr_sc0 UNREACHABLE) ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_instr_case_2 :
		"fun_free_instr (instr_sc0 DROP) ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_instr_case_3 :
		"((var_1_lst_opt = None) ⟷ (valtype_lst_opt = None)) ⟹
		 list_all2 (λ (var_1_lst :: (free list)) (valtype_lst :: (valtype list)). ((length var_1_lst) = (length valtype_lst))) (option_to_list var_1_lst_opt) (option_to_list valtype_lst_opt) ⟹
		 list_all2 (λ (var_1_lst :: (free list)) (valtype_lst :: (valtype list)). list_all2 (λ (var_1 :: free) (v_valtype :: valtype). (fun_free_valtype v_valtype var_1)) var_1_lst valtype_lst) (option_to_list var_1_lst_opt) (option_to_list valtype_lst_opt) ⟹
		 ((var_1_lst_opt = None) ⟷ (var_0_opt = None)) ⟹
		 list_all2 (λ (var_1_lst :: (free list)) (var_0 :: free). (fun_free_list var_1_lst var_0)) (option_to_list var_1_lst_opt) (option_to_list var_0_opt) ⟹
		 fun_free_instr (instr_sc0 (SELECT valtype_lst_opt)) (free_opt var_0_opt)"
	| fun_free_instr_case_4 :
		"(fun_free_block instr_lst var_1) ⟹
		 (fun_free_blocktype v_blocktype var_0) ⟹
		 fun_free_instr (instr_sc9 (BLOCK v_blocktype instr_lst)) (append_free var_0 var_1)"
	| fun_free_instr_case_5 :
		"(fun_free_block instr_lst var_1) ⟹
		 (fun_free_blocktype v_blocktype var_0) ⟹
		 fun_free_instr (instr_sc9 (LOOP v_blocktype instr_lst)) (append_free var_0 var_1)"
	| fun_free_instr_case_6 :
		"(fun_free_block instr_2_lst var_2) ⟹
		 (fun_free_block instr_1_lst var_1) ⟹
		 (fun_free_blocktype v_blocktype var_0) ⟹
		 fun_free_instr (instr_sc10 (IFELSE v_blocktype instr_1_lst instr_2_lst)) (append_free (append_free var_0 var_1) var_2)"
	| fun_free_instr_case_7 :
		"fun_free_instr (instr_sc0 (BR v_labelidx)) (free_labelidx v_labelidx)"
	| fun_free_instr_case_8 :
		"fun_free_instr (instr_sc0 (BR_IF v_labelidx)) (free_labelidx v_labelidx)"
	| fun_free_instr_case_9 :
		"(fun_free_list (map (λ (v_labelidx :: labelidx). (free_labelidx v_labelidx)) labelidx_lst) var_0) ⟹
		 fun_free_instr (instr_sc0 (BR_TABLE labelidx_lst labelidx')) (append_free var_0 (free_labelidx labelidx'))"
	| fun_free_instr_case_10 :
		"fun_free_instr (instr_sc0 (BR_ON_NULL v_labelidx)) (free_labelidx v_labelidx)"
	| fun_free_instr_case_11 :
		"fun_free_instr (instr_sc0 (BR_ON_NON_NULL v_labelidx)) (free_labelidx v_labelidx)"
	| fun_free_instr_case_12 :
		"(fun_free_reftype reftype_2 var_1) ⟹
		 (fun_free_reftype reftype_1 var_0) ⟹
		 fun_free_instr (instr_sc0 (BR_ON_CAST v_labelidx reftype_1 reftype_2)) (append_free (append_free (free_labelidx v_labelidx) var_0) var_1)"
	| fun_free_instr_case_13 :
		"(fun_free_reftype reftype_2 var_1) ⟹
		 (fun_free_reftype reftype_1 var_0) ⟹
		 fun_free_instr (instr_sc0 (BR_ON_CAST_FAIL v_labelidx reftype_1 reftype_2)) (append_free (append_free (free_labelidx v_labelidx) var_0) var_1)"
	| fun_free_instr_case_14 :
		"fun_free_instr (instr_sc1 (CALL v_funcidx)) (free_funcidx v_funcidx)"
	| fun_free_instr_case_15 :
		"(fun_free_typeuse v_typeuse var_0) ⟹
		 fun_free_instr (instr_sc1 (CALL_REF v_typeuse)) var_0"
	| fun_free_instr_case_16 :
		"(fun_free_typeuse v_typeuse var_0) ⟹
		 fun_free_instr (instr_sc1 (CALL_INDIRECT v_tableidx v_typeuse)) (append_free (free_tableidx v_tableidx) var_0)"
	| fun_free_instr_case_17 :
		"fun_free_instr (instr_sc1 RETURN) ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_instr_case_18 :
		"fun_free_instr (instr_sc1 (RETURN_CALL v_funcidx)) (free_funcidx v_funcidx)"
	| fun_free_instr_case_19 :
		"(fun_free_typeuse v_typeuse var_0) ⟹
		 fun_free_instr (instr_sc1 (RETURN_CALL_REF v_typeuse)) var_0"
	| fun_free_instr_case_20 :
		"(fun_free_typeuse v_typeuse var_0) ⟹
		 fun_free_instr (instr_sc1 (RETURN_CALL_INDIRECT v_tableidx v_typeuse)) (append_free (free_tableidx v_tableidx) var_0)"
	| fun_free_instr_case_21 :
		"fun_free_instr (instr_sc1 (THROW v_tagidx)) (free_tagidx v_tagidx)"
	| fun_free_instr_case_22 :
		"fun_free_instr (instr_sc1 THROW_REF) ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_instr_case_23 :
		"((length var_3_lst) = (length instr_lst)) ⟹
		 list_all2 (λ (var_3 :: free) (v_instr :: instr). (fun_free_instr v_instr var_3)) var_3_lst instr_lst ⟹
		 (fun_free_list var_3_lst var_2) ⟹
		 (fun_free_list (map (λ (v_catch :: catch). (free_catch v_catch)) catch_lst) var_1) ⟹
		 (fun_free_blocktype v_blocktype var_0) ⟹
		 fun_free_instr (instr_sc10 (TRY_TABLE v_blocktype (mk_list catch_lst) instr_lst)) (append_free (append_free var_0 var_1) var_2)"
	| fun_free_instr_case_24 :
		"fun_free_instr (instr_sc6 (instr_st6_CONST v_numtype numlit)) (free_numtype v_numtype)"
	| fun_free_instr_case_25 :
		"fun_free_instr (instr_sc6 (UNOP v_numtype unop)) (free_numtype v_numtype)"
	| fun_free_instr_case_26 :
		"fun_free_instr (instr_sc6 (BINOP v_numtype binop)) (free_numtype v_numtype)"
	| fun_free_instr_case_27 :
		"fun_free_instr (instr_sc6 (TESTOP v_numtype testop)) (free_numtype v_numtype)"
	| fun_free_instr_case_28 :
		"fun_free_instr (instr_sc6 (RELOP v_numtype relop)) (free_numtype v_numtype)"
	| fun_free_instr_case_29 :
		"fun_free_instr (instr_sc7 (CVTOP numtype_1 numtype_2 cvtop)) (append_free (free_numtype numtype_1) (free_numtype numtype_2))"
	| fun_free_instr_case_30 :
		"fun_free_instr (instr_sc7 (instr_st7_VCONST v_vectype veclit)) (free_vectype v_vectype)"
	| fun_free_instr_case_31 :
		"fun_free_instr (instr_sc7 (VVUNOP v_vectype v_vvunop)) (free_vectype v_vectype)"
	| fun_free_instr_case_32 :
		"fun_free_instr (instr_sc7 (VVBINOP v_vectype v_vvbinop)) (free_vectype v_vectype)"
	| fun_free_instr_case_33 :
		"fun_free_instr (instr_sc7 (VVTERNOP v_vectype v_vvternop)) (free_vectype v_vectype)"
	| fun_free_instr_case_34 :
		"fun_free_instr (instr_sc7 (VVTESTOP v_vectype v_vvtestop)) (free_vectype v_vectype)"
	| fun_free_instr_case_35 :
		"fun_free_instr (instr_sc7 (VUNOP v_shape vunop)) (free_shape v_shape)"
	| fun_free_instr_case_36 :
		"fun_free_instr (instr_sc7 (VBINOP v_shape vbinop)) (free_shape v_shape)"
	| fun_free_instr_case_37 :
		"fun_free_instr (instr_sc7 (VTERNOP v_shape vternop)) (free_shape v_shape)"
	| fun_free_instr_case_38 :
		"fun_free_instr (instr_sc7 (VTESTOP v_shape vtestop)) (free_shape v_shape)"
	| fun_free_instr_case_39 :
		"fun_free_instr (instr_sc7 (VRELOP v_shape vrelop)) (free_shape v_shape)"
	| fun_free_instr_case_40 :
		"fun_free_instr (instr_sc8 (VSHIFTOP v_ishape vshiftop)) (free_shape (proj_ishape_0 v_ishape))"
	| fun_free_instr_case_41 :
		"fun_free_instr (instr_sc8 (VBITMASK v_ishape)) (free_shape (proj_ishape_0 v_ishape))"
	| fun_free_instr_case_42 :
		"fun_free_instr (instr_sc8 (VSWIZZLOP v_bshape vswizzlop)) (free_shape (proj_bshape_0 v_bshape))"
	| fun_free_instr_case_43 :
		"fun_free_instr (instr_sc8 (VSHUFFLE v_bshape laneidx_lst)) (free_shape (proj_bshape_0 v_bshape))"
	| fun_free_instr_case_44 :
		"fun_free_instr (instr_sc8 (VEXTUNOP ishape_1 ishape_2 vextunop)) (append_free (free_shape (proj_ishape_0 ishape_1)) (free_shape (proj_ishape_0 ishape_2)))"
	| fun_free_instr_case_45 :
		"fun_free_instr (instr_sc8 (VEXTBINOP ishape_1 ishape_2 vextbinop)) (append_free (free_shape (proj_ishape_0 ishape_1)) (free_shape (proj_ishape_0 ishape_2)))"
	| fun_free_instr_case_46 :
		"fun_free_instr (instr_sc8 (VEXTTERNOP ishape_1 ishape_2 vextternop)) (append_free (free_shape (proj_ishape_0 ishape_1)) (free_shape (proj_ishape_0 ishape_2)))"
	| fun_free_instr_case_47 :
		"fun_free_instr (instr_sc8 (VNARROW ishape_1 ishape_2 v_sx)) (append_free (free_shape (proj_ishape_0 ishape_1)) (free_shape (proj_ishape_0 ishape_2)))"
	| fun_free_instr_case_48 :
		"fun_free_instr (instr_sc8 (VCVTOP shape_1 shape_2 vcvtop)) (append_free (free_shape shape_1) (free_shape shape_2))"
	| fun_free_instr_case_49 :
		"fun_free_instr (instr_sc8 (VSPLAT v_shape)) (free_shape v_shape)"
	| fun_free_instr_case_50 :
		"fun_free_instr (instr_sc8 (VEXTRACT_LANE v_shape sx_opt v_laneidx)) (free_shape v_shape)"
	| fun_free_instr_case_51 :
		"fun_free_instr (instr_sc9 (VREPLACE_LANE v_shape v_laneidx)) (free_shape v_shape)"
	| fun_free_instr_case_52 :
		"(fun_free_heaptype v_heaptype var_0) ⟹
		 fun_free_instr (instr_sc4 (instr_st4_REF_NULL v_heaptype)) var_0"
	| fun_free_instr_case_53 :
		"fun_free_instr (instr_sc4 REF_IS_NULL) ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_instr_case_54 :
		"fun_free_instr (instr_sc4 REF_AS_NON_NULL) ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_instr_case_55 :
		"fun_free_instr (instr_sc4 REF_EQ) ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_instr_case_56 :
		"(fun_free_reftype v_reftype var_0) ⟹
		 fun_free_instr (instr_sc4 (REF_TEST v_reftype)) var_0"
	| fun_free_instr_case_57 :
		"(fun_free_reftype v_reftype var_0) ⟹
		 fun_free_instr (instr_sc4 (REF_CAST v_reftype)) var_0"
	| fun_free_instr_case_58 :
		"fun_free_instr (instr_sc4 (REF_FUNC v_funcidx)) (free_funcidx v_funcidx)"
	| fun_free_instr_case_59 :
		"fun_free_instr (instr_sc4 REF_I31) ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_instr_case_60 :
		"fun_free_instr (instr_sc4 (I31_GET v_sx)) ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_instr_case_61 :
		"fun_free_instr (instr_sc4 (STRUCT_NEW v_typeidx)) ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_instr_case_62 :
		"fun_free_instr (instr_sc5 (STRUCT_NEW_DEFAULT v_typeidx)) (free_typeidx v_typeidx)"
	| fun_free_instr_case_63 :
		"fun_free_instr (instr_sc5 (STRUCT_GET sx_opt v_typeidx v_u32)) (free_typeidx v_typeidx)"
	| fun_free_instr_case_64 :
		"fun_free_instr (instr_sc5 (STRUCT_SET v_typeidx v_u32)) (free_typeidx v_typeidx)"
	| fun_free_instr_case_65 :
		"fun_free_instr (instr_sc5 (ARRAY_NEW v_typeidx)) (free_typeidx v_typeidx)"
	| fun_free_instr_case_66 :
		"fun_free_instr (instr_sc5 (ARRAY_NEW_DEFAULT v_typeidx)) (free_typeidx v_typeidx)"
	| fun_free_instr_case_67 :
		"fun_free_instr (instr_sc5 (ARRAY_NEW_FIXED v_typeidx v_u32)) (free_typeidx v_typeidx)"
	| fun_free_instr_case_68 :
		"fun_free_instr (instr_sc5 (ARRAY_NEW_DATA v_typeidx v_dataidx)) (append_free (free_typeidx v_typeidx) (free_dataidx v_dataidx))"
	| fun_free_instr_case_69 :
		"fun_free_instr (instr_sc5 (ARRAY_NEW_ELEM v_typeidx v_elemidx)) (append_free (free_typeidx v_typeidx) (free_elemidx v_elemidx))"
	| fun_free_instr_case_70 :
		"fun_free_instr (instr_sc5 (ARRAY_GET sx_opt v_typeidx)) (free_typeidx v_typeidx)"
	| fun_free_instr_case_71 :
		"fun_free_instr (instr_sc5 (ARRAY_SET v_typeidx)) (free_typeidx v_typeidx)"
	| fun_free_instr_case_72 :
		"fun_free_instr (instr_sc5 ARRAY_LEN) ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_instr_case_73 :
		"fun_free_instr (instr_sc6 (ARRAY_FILL v_typeidx)) (free_typeidx v_typeidx)"
	| fun_free_instr_case_74 :
		"fun_free_instr (instr_sc6 (ARRAY_COPY typeidx_1 typeidx_2)) (append_free (free_typeidx typeidx_1) (free_typeidx typeidx_2))"
	| fun_free_instr_case_75 :
		"fun_free_instr (instr_sc6 (ARRAY_INIT_DATA v_typeidx v_dataidx)) (append_free (free_typeidx v_typeidx) (free_dataidx v_dataidx))"
	| fun_free_instr_case_76 :
		"fun_free_instr (instr_sc6 (ARRAY_INIT_ELEM v_typeidx v_elemidx)) (append_free (free_typeidx v_typeidx) (free_elemidx v_elemidx))"
	| fun_free_instr_case_77 :
		"fun_free_instr (instr_sc6 EXTERN_CONVERT_ANY) ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_instr_case_78 :
		"fun_free_instr (instr_sc6 ANY_CONVERT_EXTERN) ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_instr_case_79 :
		"fun_free_instr (instr_sc1 (LOCAL_GET v_localidx)) (free_localidx v_localidx)"
	| fun_free_instr_case_80 :
		"fun_free_instr (instr_sc1 (LOCAL_SET v_localidx)) (free_localidx v_localidx)"
	| fun_free_instr_case_81 :
		"fun_free_instr (instr_sc2 (LOCAL_TEE v_localidx)) (free_localidx v_localidx)"
	| fun_free_instr_case_82 :
		"fun_free_instr (instr_sc2 (GLOBAL_GET v_globalidx)) (free_globalidx v_globalidx)"
	| fun_free_instr_case_83 :
		"fun_free_instr (instr_sc2 (GLOBAL_SET v_globalidx)) (free_globalidx v_globalidx)"
	| fun_free_instr_case_84 :
		"fun_free_instr (instr_sc2 (TABLE_GET v_tableidx)) (free_tableidx v_tableidx)"
	| fun_free_instr_case_85 :
		"fun_free_instr (instr_sc2 (TABLE_SET v_tableidx)) (free_tableidx v_tableidx)"
	| fun_free_instr_case_86 :
		"fun_free_instr (instr_sc2 (TABLE_SIZE v_tableidx)) (free_tableidx v_tableidx)"
	| fun_free_instr_case_87 :
		"fun_free_instr (instr_sc2 (TABLE_GROW v_tableidx)) (free_tableidx v_tableidx)"
	| fun_free_instr_case_88 :
		"fun_free_instr (instr_sc2 (TABLE_FILL v_tableidx)) (free_tableidx v_tableidx)"
	| fun_free_instr_case_89 :
		"fun_free_instr (instr_sc2 (TABLE_COPY tableidx_1 tableidx_2)) (append_free (free_tableidx tableidx_1) (free_tableidx tableidx_2))"
	| fun_free_instr_case_90 :
		"fun_free_instr (instr_sc2 (TABLE_INIT v_tableidx v_elemidx)) (append_free (free_tableidx v_tableidx) (free_elemidx v_elemidx))"
	| fun_free_instr_case_91 :
		"fun_free_instr (instr_sc2 (ELEM_DROP v_elemidx)) (free_elemidx v_elemidx)"
	| fun_free_instr_case_92 :
		"fun_free_instr (instr_sc3 (LOAD v_numtype loadop_opt v_memidx v_memarg)) (append_free (free_numtype v_numtype) (free_memidx v_memidx))"
	| fun_free_instr_case_93 :
		"fun_free_instr (instr_sc3 (STORE v_numtype storeop_opt v_memidx v_memarg)) (append_free (free_numtype v_numtype) (free_memidx v_memidx))"
	| fun_free_instr_case_94 :
		"fun_free_instr (instr_sc3 (VLOAD v_vectype vloadop_opt v_memidx v_memarg)) (append_free (free_vectype v_vectype) (free_memidx v_memidx))"
	| fun_free_instr_case_95 :
		"fun_free_instr (instr_sc3 (VLOAD_LANE v_vectype v_sz v_memidx v_memarg v_laneidx)) (append_free (free_vectype v_vectype) (free_memidx v_memidx))"
	| fun_free_instr_case_96 :
		"fun_free_instr (instr_sc3 (VSTORE v_vectype v_memidx v_memarg)) (append_free (free_vectype v_vectype) (free_memidx v_memidx))"
	| fun_free_instr_case_97 :
		"fun_free_instr (instr_sc3 (VSTORE_LANE v_vectype v_sz v_memidx v_memarg v_laneidx)) (append_free (free_vectype v_vectype) (free_memidx v_memidx))"
	| fun_free_instr_case_98 :
		"fun_free_instr (instr_sc3 (MEMORY_SIZE v_memidx)) (free_memidx v_memidx)"
	| fun_free_instr_case_99 :
		"fun_free_instr (instr_sc3 (MEMORY_GROW v_memidx)) (free_memidx v_memidx)"
	| fun_free_instr_case_100 :
		"fun_free_instr (instr_sc3 (MEMORY_FILL v_memidx)) (free_memidx v_memidx)"
	| fun_free_instr_case_101 :
		"fun_free_instr (instr_sc3 (MEMORY_COPY memidx_1 memidx_2)) (append_free (free_memidx memidx_1) (free_memidx memidx_2))"
	| fun_free_instr_case_102 :
		"fun_free_instr (instr_sc3 (MEMORY_INIT v_memidx v_dataidx)) (append_free (free_memidx v_memidx) (free_dataidx v_dataidx))"
	| fun_free_instr_case_103 :
		"fun_free_instr (instr_sc4 (DATA_DROP v_dataidx)) (free_dataidx v_dataidx)"
	| fun_free_block_case_0 :
		"((length var_2_lst) = (length instr_lst)) ⟹
		 list_all2 (λ (var_2 :: free) (v_instr :: instr). (fun_free_instr v_instr var_2)) var_2_lst instr_lst ⟹
		 (fun_free_list var_2_lst var_1) ⟹
		 (fun_shift_labelidxs (LABELS v_free) var_0) ⟹
		 (wf_free var_1) ⟹
		 list_all (λ (var_2 :: free). (wf_free var_2)) var_2_lst ⟹
		 (v_free = var_1) ⟹
		 fun_free_block instr_lst (v_free ⦇ LABELS := var_0  ⦈)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:422.6-422.16 *)
inductive fun_free_expr :: "expr ⇒ free ⇒ bool" where
	  fun_free_expr_case_0 :
		"((length var_1_lst) = (length instr_lst)) ⟹
		 list_all2 (λ (var_1 :: free) (v_instr :: instr). (fun_free_instr v_instr var_1)) var_1_lst instr_lst ⟹
		 (fun_free_list var_1_lst var_0) ⟹
		 fun_free_expr instr_lst var_0"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:5.1-6.43 *)
datatype elemmode =
	  ACTIVE "tableidx" "expr"
	| PASSIVE
	| DECLARE

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:5.8-5.16 *)
inductive wf_elemmode :: "elemmode ⇒ bool" where
	  elemmode_case_0 :
		"(wf_uN 32 v_tableidx) ⟹
		 list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_elemmode (ACTIVE v_tableidx v_expr)"
	| elemmode_case_1 :
		"wf_elemmode PASSIVE"
	| elemmode_case_2 :
		"wf_elemmode DECLARE"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:7.1-8.31 *)
datatype datamode =
	  datamode_ACTIVE "memidx" "expr"
	| datamode_PASSIVE

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:7.8-7.16 *)
inductive wf_datamode :: "datamode ⇒ bool" where
	  datamode_case_0 :
		"(wf_uN 32 v_memidx) ⟹
		 list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_datamode (datamode_ACTIVE v_memidx v_expr)"
	| datamode_case_1 :
		"wf_datamode datamode_PASSIVE"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:10.1-11.15 *)
datatype type =
	  res_TYPE "rectype"
	

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:13.1-14.14 *)
datatype tag =
	  tag_TAG "tagtype"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:13.8-13.11 *)
inductive wf_tag :: "tag ⇒ bool" where
	  tag_case_0 :
		"(wf_typeuse v_tagtype) ⟹
		 wf_tag (tag_TAG v_tagtype)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:16.1-17.25 *)
datatype global =
	  global_GLOBAL "globaltype" "expr"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:16.8-16.14 *)
inductive wf_global :: "global ⇒ bool" where
	  global_case_0 :
		"(wf_globaltype v_globaltype) ⟹
		 list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_global (global_GLOBAL v_globaltype v_expr)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:19.1-20.17 *)
datatype mem =
	  MEMORY "memtype"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:19.8-19.11 *)
inductive wf_mem :: "mem ⇒ bool" where
	  mem_case_0 :
		"(wf_memtype v_memtype) ⟹
		 wf_mem (MEMORY v_memtype)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:22.1-23.23 *)
datatype table =
	  table_TABLE "tabletype" "expr"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:22.8-22.13 *)
inductive wf_table :: "table ⇒ bool" where
	  table_case_0 :
		"(wf_tabletype v_tabletype) ⟹
		 list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_table (table_TABLE v_tabletype v_expr)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:25.1-26.22 *)
datatype data =
	  DATA "(byte list)" "datamode"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:25.8-25.12 *)
inductive wf_data :: "data ⇒ bool" where
	  data_case_0 :
		"list_all (λ (v_byte :: byte). (wf_byte v_byte)) byte_lst ⟹
		 (wf_datamode v_datamode) ⟹
		 wf_data (DATA byte_lst v_datamode)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:28.1-29.16 *)
datatype local =
	  LOCAL "valtype"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:28.8-28.13 *)
inductive wf_local :: "local ⇒ bool" where
	  local_case_0 :
		"(wf_valtype v_valtype) ⟹
		 wf_local (LOCAL v_valtype)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:31.1-32.27 *)
datatype func =
	  func_FUNC "typeidx" "(local list)" "expr"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:31.8-31.12 *)
inductive wf_func :: "func ⇒ bool" where
	  func_case_0 :
		"(wf_uN 32 v_typeidx) ⟹
		 list_all (λ (v_local :: local). (wf_local v_local)) local_lst ⟹
		 list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_func (func_FUNC v_typeidx local_lst v_expr)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:34.1-35.30 *)
datatype elem =
	  ELEM "reftype" "(expr list)" "elemmode"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:34.8-34.12 *)
inductive wf_elem :: "elem ⇒ bool" where
	  elem_case_0 :
		"(wf_reftype v_reftype) ⟹
		 list_all (λ (v_expr :: expr). list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr) expr_lst ⟹
		 (wf_elemmode v_elemmode) ⟹
		 wf_elem (ELEM v_reftype expr_lst v_elemmode)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:37.1-38.16 *)
datatype start =
	  START "funcidx"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:37.8-37.13 *)
inductive wf_start :: "start ⇒ bool" where
	  start_case_0 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_start (START v_funcidx)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:40.1-41.30 *)
datatype import =
	  IMPORT "name" "name" "externtype"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:40.8-40.14 *)
inductive wf_import :: "import ⇒ bool" where
	  import_case_0 :
		"(wf_name v_name) ⟹
		 (wf_name name_0) ⟹
		 (wf_externtype v_externtype) ⟹
		 wf_import (IMPORT v_name name_0 v_externtype)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:43.1-44.24 *)
datatype export =
	  EXPORT "name" "externidx"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:43.8-43.14 *)
inductive wf_export :: "export ⇒ bool" where
	  export_case_0 :
		"(wf_name v_name) ⟹
		 (wf_externidx v_externidx) ⟹
		 wf_export (EXPORT v_name v_externidx)"

(* Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:46.1-47.81 *)
datatype module =
	  module_MODULE "(type list)" "(import list)" "(tag list)" "(global list)" "(mem list)" "(table list)" "(func list)" "(data list)" "(elem list)" "(start option)" "(export list)"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:46.8-46.14 *)
inductive wf_module :: "module ⇒ bool" where
	  module_case_0 :
		"list_all (λ (v_import :: import). (wf_import v_import)) import_lst ⟹
		 list_all (λ (v_tag :: tag). (wf_tag v_tag)) tag_lst ⟹
		 list_all (λ (v_global :: global). (wf_global v_global)) global_lst ⟹
		 list_all (λ (v_mem :: mem). (wf_mem v_mem)) mem_lst ⟹
		 list_all (λ (v_table :: table). (wf_table v_table)) table_lst ⟹
		 list_all (λ (v_func :: func). (wf_func v_func)) func_lst ⟹
		 list_all (λ (v_data :: data). (wf_data v_data)) data_lst ⟹
		 list_all (λ (v_elem :: elem). (wf_elem v_elem)) elem_lst ⟹
		 list_all (λ (v_start :: start). (wf_start v_start)) (option_to_list start_opt) ⟹
		 list_all (λ (v_export :: export). (wf_export v_export)) export_lst ⟹
		 wf_module (module_MODULE type_lst import_lst tag_lst global_lst mem_lst table_lst func_lst data_lst elem_lst start_opt export_lst)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:62.6-62.16 *)
inductive fun_free_type :: "type ⇒ free ⇒ bool" where
	  fun_free_type_case_0 :
		"(fun_free_rectype v_rectype var_0) ⟹
		 fun_free_type (res_TYPE v_rectype) var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:63.6-63.15 *)
inductive fun_free_tag :: "tag ⇒ free ⇒ bool" where
	  fun_free_tag_case_0 :
		"(fun_free_tagtype v_tagtype var_0) ⟹
		 fun_free_tag (tag_TAG v_tagtype) var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:64.6-64.18 *)
inductive fun_free_global :: "global ⇒ free ⇒ bool" where
	  fun_free_global_case_0 :
		"(fun_free_expr v_expr var_1) ⟹
		 (fun_free_globaltype v_globaltype var_0) ⟹
		 fun_free_global (global_GLOBAL v_globaltype v_expr) (append_free var_0 var_1)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:65.1-65.26 *)
function (sequential) free_mem :: "mem ⇒ free" where
		  "free_mem (MEMORY v_memtype) = (free_memtype v_memtype)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:66.6-66.17 *)
inductive fun_free_table :: "table ⇒ free ⇒ bool" where
	  fun_free_table_case_0 :
		"(fun_free_expr v_expr var_1) ⟹
		 (fun_free_tabletype v_tabletype var_0) ⟹
		 fun_free_table (table_TABLE v_tabletype v_expr) (append_free var_0 var_1)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:67.6-67.17 *)
inductive fun_free_local :: "local ⇒ free ⇒ bool" where
	  fun_free_local_case_0 :
		"(fun_free_valtype t var_0) ⟹
		 fun_free_local (LOCAL t) var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:68.6-68.16 *)
inductive fun_free_func :: "func ⇒ free ⇒ bool" where
	  fun_free_func_case_0 :
		"(fun_free_block v_expr var_2) ⟹
		 ((length var_1_lst) = (length local_lst)) ⟹
		 list_all2 (λ (var_1 :: free) (v_local :: local). (fun_free_local v_local var_1)) var_1_lst local_lst ⟹
		 (fun_free_list var_1_lst var_0) ⟹
		 fun_free_func (func_FUNC v_typeidx local_lst v_expr) (append_free (append_free (free_typeidx v_typeidx) var_0) (var_2 ⦇ LOCALS := []  ⦈))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:71.6-71.20 *)
inductive fun_free_datamode :: "datamode ⇒ free ⇒ bool" where
	  fun_free_datamode_case_0 :
		"(fun_free_expr v_expr var_0) ⟹
		 fun_free_datamode (datamode_ACTIVE v_memidx v_expr) (append_free (free_memidx v_memidx) var_0)"
	| fun_free_datamode_case_1 :
		"fun_free_datamode datamode_PASSIVE ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:69.6-69.16 *)
inductive fun_free_data :: "data ⇒ free ⇒ bool" where
	  fun_free_data_case_0 :
		"(fun_free_datamode v_datamode var_0) ⟹
		 fun_free_data (DATA byte_lst v_datamode) var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:72.6-72.20 *)
inductive fun_free_elemmode :: "elemmode ⇒ free ⇒ bool" where
	  fun_free_elemmode_case_0 :
		"(fun_free_expr v_expr var_0) ⟹
		 fun_free_elemmode (ACTIVE v_tableidx v_expr) (append_free (free_tableidx v_tableidx) var_0)"
	| fun_free_elemmode_case_1 :
		"fun_free_elemmode PASSIVE ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"
	| fun_free_elemmode_case_2 :
		"fun_free_elemmode DECLARE ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], LOCALS = [], LABELS = [], TAGS = [] ⦈"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:70.6-70.16 *)
inductive fun_free_elem :: "elem ⇒ free ⇒ bool" where
	  fun_free_elem_case_0 :
		"(fun_free_elemmode v_elemmode var_3) ⟹
		 ((length var_2_lst) = (length expr_lst)) ⟹
		 list_all2 (λ (var_2 :: free) (v_expr :: expr). (fun_free_expr v_expr var_2)) var_2_lst expr_lst ⟹
		 (fun_free_list var_2_lst var_1) ⟹
		 (fun_free_reftype v_reftype var_0) ⟹
		 fun_free_elem (ELEM v_reftype expr_lst v_elemmode) (append_free (append_free var_0 var_1) var_3)"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:73.1-73.30 *)
function (sequential) free_start :: "start ⇒ free" where
		  "free_start (START v_funcidx) = (free_funcidx v_funcidx)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:74.6-74.18 *)
inductive fun_free_import :: "import ⇒ free ⇒ bool" where
	  fun_free_import_case_0 :
		"(fun_free_externtype v_externtype var_0) ⟹
		 fun_free_import (IMPORT name_1 name_2 v_externtype) var_0"

(* Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:75.1-75.32 *)
function (sequential) free_export :: "export ⇒ free" where
		  "free_export (EXPORT v_name v_externidx) = (free_externidx v_externidx)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:76.6-76.18 *)
inductive fun_free_module :: "module ⇒ free ⇒ bool" where
	  fun_free_module_case_0 :
		"(fun_free_list (map (λ (v_export :: export). (free_export v_export)) export_lst) var_17) ⟹
		 ((length var_16_lst) = (length import_lst)) ⟹
		 list_all2 (λ (var_16 :: free) (v_import :: import). (fun_free_import v_import var_16)) var_16_lst import_lst ⟹
		 (fun_free_list var_16_lst var_15) ⟹
		 ((length var_14_lst) = (length elem_lst)) ⟹
		 list_all2 (λ (var_14 :: free) (v_elem :: elem). (fun_free_elem v_elem var_14)) var_14_lst elem_lst ⟹
		 (fun_free_list var_14_lst var_13) ⟹
		 ((length var_12_lst) = (length data_lst)) ⟹
		 list_all2 (λ (var_12 :: free) (v_data :: data). (fun_free_data v_data var_12)) var_12_lst data_lst ⟹
		 (fun_free_list var_12_lst var_11) ⟹
		 ((length var_10_lst) = (length func_lst)) ⟹
		 list_all2 (λ (var_10 :: free) (v_func :: func). (fun_free_func v_func var_10)) var_10_lst func_lst ⟹
		 (fun_free_list var_10_lst var_9) ⟹
		 ((length var_8_lst) = (length table_lst)) ⟹
		 list_all2 (λ (var_8 :: free) (v_table :: table). (fun_free_table v_table var_8)) var_8_lst table_lst ⟹
		 (fun_free_list var_8_lst var_7) ⟹
		 (fun_free_list (map (λ (v_mem :: mem). (free_mem v_mem)) mem_lst) var_6) ⟹
		 ((length var_5_lst) = (length global_lst)) ⟹
		 list_all2 (λ (var_5 :: free) (v_global :: global). (fun_free_global v_global var_5)) var_5_lst global_lst ⟹
		 (fun_free_list var_5_lst var_4) ⟹
		 ((length var_3_lst) = (length tag_lst)) ⟹
		 list_all2 (λ (var_3 :: free) (v_tag :: tag). (fun_free_tag v_tag var_3)) var_3_lst tag_lst ⟹
		 (fun_free_list var_3_lst var_2) ⟹
		 ((length var_1_lst) = (length type_lst)) ⟹
		 list_all2 (λ (var_1 :: free) (v_type :: type). (fun_free_type v_type var_1)) var_1_lst type_lst ⟹
		 (fun_free_list var_1_lst var_0) ⟹
		 fun_free_module (module_MODULE type_lst import_lst tag_lst global_lst mem_lst table_lst func_lst data_lst elem_lst start_opt export_lst) (append_free (append_free (append_free (append_free (append_free (append_free (append_free (append_free (append_free (append_free var_0 var_2) var_4) var_6) var_7) var_9) var_11) var_13) (free_opt (map_option (λ (v_start :: start). (free_start v_start)) start_opt))) var_15) var_17)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:130.6-130.21 *)
inductive fun_funcidx_module :: "module ⇒ (funcidx list) ⇒ bool" where
	  fun_funcidx_module_case_0 :
		"(fun_free_module v_module var_0) ⟹
		 fun_funcidx_module v_module (FUNCS var_0)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:133.6-133.20 *)
inductive fun_dataidx_funcs :: "(func list) ⇒ (dataidx list) ⇒ bool" where
	  fun_dataidx_funcs_case_0 :
		"((length var_1_lst) = (length func_lst)) ⟹
		 list_all2 (λ (var_1 :: free) (v_func :: func). (fun_free_func v_func var_1)) var_1_lst func_lst ⟹
		 (fun_free_list var_1_lst var_0) ⟹
		 fun_dataidx_funcs func_lst (DATAS var_0)"

(* Inductive Type Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:8.1-9.16 *)
datatype init =
	  SET
	| UNSET

(* Inductive Type Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:11.1-12.15 *)
datatype localtype =
	  mk_localtype "init" "valtype"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:11.8-11.17 *)
inductive wf_localtype :: "localtype ⇒ bool" where
	  localtype_case_0 :
		"(wf_valtype v_valtype) ⟹
		 wf_localtype (mk_localtype v_init v_valtype)"

(* Inductive Type Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:14.1-15.56 *)
datatype instrtype =
	  mk_instrtype "resulttype" "(localidx list)" "resulttype"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:14.8-14.17 *)
inductive wf_instrtype :: "instrtype ⇒ bool" where
	  instrtype_case_0 :
		"list_all (λ (v_localidx :: localidx). (wf_uN 32 v_localidx)) localidx_lst ⟹
		 wf_instrtype (mk_instrtype v_resulttype localidx_lst resulttype_0)"

(* Record Creation Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:24.1-38.4 *)
record res_context =
	context_TYPES :: "(deftype list)"
	RECS :: "(subtype list)"
	context_TAGS :: "(tagtype list)"
	context_GLOBALS :: "(globaltype list)"
	context_MEMS :: "(memtype list)"
	context_TABLES :: "(tabletype list)"
	context_FUNCS :: "(deftype list)"
	context_DATAS :: "(res_datatype list)"
	context_ELEMS :: "(elemtype list)"
	context_LOCALS :: "(localtype list)"
	context_LABELS :: "(resulttype list)"
	context_RETURN :: "(resulttype option)"
	REFS :: "(funcidx list)"

definition append_res_context :: "res_context ⇒ res_context ⇒ res_context" where
	"append_res_context arg1 arg2 = ⦇
		context_TYPES = context_TYPES arg1 @ context_TYPES arg2,
		RECS = RECS arg1 @ RECS arg2,
		context_TAGS = context_TAGS arg1 @ context_TAGS arg2,
		context_GLOBALS = context_GLOBALS arg1 @ context_GLOBALS arg2,
		context_MEMS = context_MEMS arg1 @ context_MEMS arg2,
		context_TABLES = context_TABLES arg1 @ context_TABLES arg2,
		context_FUNCS = context_FUNCS arg1 @ context_FUNCS arg2,
		context_DATAS = context_DATAS arg1 @ context_DATAS arg2,
		context_ELEMS = context_ELEMS arg1 @ context_ELEMS arg2,
		context_LOCALS = context_LOCALS arg1 @ context_LOCALS arg2,
		context_LABELS = context_LABELS arg1 @ context_LABELS arg2,
		context_RETURN = context_RETURN arg1 @@@ context_RETURN arg2,
		REFS = REFS arg1 @ REFS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:24.8-24.15 *)
inductive wf_context :: "res_context ⇒ bool" where
	  context_case_underscore :
		"list_all (λ (var_1 :: subtype). (wf_subtype var_1)) var_1 ⟹
		 list_all (λ (var_2 :: tagtype). (wf_typeuse var_2)) var_2 ⟹
		 list_all (λ (var_3 :: globaltype). (wf_globaltype var_3)) var_3 ⟹
		 list_all (λ (var_4 :: memtype). (wf_memtype var_4)) var_4 ⟹
		 list_all (λ (var_5 :: tabletype). (wf_tabletype var_5)) var_5 ⟹
		 list_all (λ (var_8 :: elemtype). (wf_reftype var_8)) var_8 ⟹
		 list_all (λ (var_9 :: localtype). (wf_localtype var_9)) var_9 ⟹
		 list_all (λ (var_12 :: funcidx). (wf_uN 32 var_12)) var_12 ⟹
		 wf_context ⦇ context_TYPES = var_0, RECS = var_1, context_TAGS = var_2, context_GLOBALS = var_3, context_MEMS = var_4, context_TABLES = var_5, context_FUNCS = var_6, context_DATAS = var_7, context_ELEMS = var_8, context_LOCALS = var_9, context_LABELS = var_10, context_RETURN = var_11, REFS = var_12 ⦈"

(* Mutual Recursion at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:46.1-46.158 *)
inductive fun_with_locals :: "res_context ⇒ (localidx list) ⇒ (localtype list) ⇒ (res_context option) ⇒ bool" where
	  fun_with_locals_case_0 :
		"fun_with_locals C [] [] (Some C)"
	| fun_with_locals_case_1 :
		"(fun_with_locals (C ⦇ context_LOCALS := (list_update_func (context_LOCALS C) (proj_uN_0 x_1) (λ (underscore_underscore :: localtype). lct_1))  ⦈) x_lst lct_lst var_0) ⟹
		 fun_with_locals C ([x_1] @ x_lst) ([lct_1] @ lct_lst) var_0"
	| fun_with_locals_case_2 :
		"True ⟹
		 fun_with_locals x0 x1 x2 None"

(* Mutual Recursion at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:59.1-59.94 *)
inductive fun_clos_deftypes :: "(deftype list) ⇒ (deftype list) ⇒ bool" where
	  fun_clos_deftypes_case_0 :
		"fun_clos_deftypes [] []"
	| fun_clos_deftypes_case_1 :
		"(fun_clos_deftypes dt_lst var_1) ⟹
		 (fun_subst_all_deftype dt_n (map (λ (dt' :: deftype). (typeuse_deftype dt')) dt'_lst) var_0) ⟹
		 (dt'_lst = var_1) ⟹
		 fun_clos_deftypes (dt_lst @ [dt_n]) (dt'_lst @ [var_0])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:54.6-54.19 *)
inductive fun_clos_valtype :: "res_context ⇒ valtype ⇒ valtype ⇒ bool" where
	  fun_clos_valtype_case_0 :
		"(fun_clos_deftypes (context_TYPES C) var_1) ⟹
		 (fun_subst_all_valtype t (map (λ (dt :: deftype). (typeuse_deftype dt)) dt_lst) var_0) ⟹
		 (dt_lst = var_1) ⟹
		 fun_clos_valtype C t var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:55.6-55.19 *)
inductive fun_clos_deftype :: "res_context ⇒ deftype ⇒ deftype ⇒ bool" where
	  fun_clos_deftype_case_0 :
		"(fun_clos_deftypes (context_TYPES C) var_1) ⟹
		 (fun_subst_all_deftype dt (map (λ (dt' :: deftype). (typeuse_deftype dt')) dt'_lst) var_0) ⟹
		 (dt'_lst = var_1) ⟹
		 fun_clos_deftype C dt var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:56.6-56.19 *)
inductive fun_clos_tagtype :: "res_context ⇒ tagtype ⇒ tagtype ⇒ bool" where
	  fun_clos_tagtype_case_0 :
		"(fun_clos_deftypes (context_TYPES C) var_1) ⟹
		 (fun_subst_all_tagtype jt (map (λ (dt :: deftype). (typeuse_deftype dt)) dt_lst) var_0) ⟹
		 (dt_lst = var_1) ⟹
		 fun_clos_tagtype C jt var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:57.6-57.22 *)
inductive fun_clos_externtype :: "res_context ⇒ externtype ⇒ externtype ⇒ bool" where
	  fun_clos_externtype_case_0 :
		"(fun_clos_deftypes (context_TYPES C) var_1) ⟹
		 (fun_subst_all_externtype xt (map (λ (dt :: deftype). (typeuse_deftype dt)) dt_lst) var_0) ⟹
		 (dt_lst = var_1) ⟹
		 fun_clos_externtype C xt var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:58.6-58.22 *)
inductive fun_clos_moduletype :: "res_context ⇒ moduletype ⇒ moduletype ⇒ bool" where
	  fun_clos_moduletype_case_0 :
		"(fun_clos_deftypes (context_TYPES C) var_1) ⟹
		 (fun_subst_all_moduletype mmt (map (λ (dt :: deftype). (typeuse_deftype dt)) dt_lst) var_0) ⟹
		 (dt_lst = var_1) ⟹
		 fun_clos_moduletype C mmt var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:7.1-7.91 *)
inductive Numtype_ok :: "res_context ⇒ numtype ⇒ bool" where
	  mk_Numtype_ok :
		"Numtype_ok C v_numtype"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:8.1-8.91 *)
inductive Vectype_ok :: "res_context ⇒ vectype ⇒ bool" where
	  mk_Vectype_ok :
		"Vectype_ok C v_vectype"

(* Inductive Type Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:79.1-80.85 *)
datatype oktypeidx =
	  oktypeidx_OK "typeidx"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:79.8-79.17 *)
inductive wf_oktypeidx :: "oktypeidx ⇒ bool" where
	  oktypeidx_case_0 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_oktypeidx (oktypeidx_OK v_typeidx)"

(* Inductive Type Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:81.1-82.68 *)
datatype oktypeidxnat =
	  oktypeidxnat_OK "typeidx" "nat"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:81.8-81.20 *)
inductive wf_oktypeidxnat :: "oktypeidxnat ⇒ bool" where
	  oktypeidxnat_case_0 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_oktypeidxnat (oktypeidxnat_OK v_typeidx var_0)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:84.1-84.103 *)
inductive Packtype_ok :: "res_context ⇒ packtype ⇒ bool" where
	  mk_Packtype_ok :
		"Packtype_ok C v_packtype"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:133.1-133.116 *)
inductive Packtype_sub :: "res_context ⇒ packtype ⇒ packtype ⇒ bool" where
	  mk_Packtype_sub :
		"Packtype_sub C v_packtype v_packtype"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:7.1-7.103 *)
inductive Numtype_sub :: "res_context ⇒ numtype ⇒ numtype ⇒ bool" where
	  mk_Numtype_sub :
		"Numtype_sub C v_numtype v_numtype"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:65.1-66.70 *)
inductive Expand :: "deftype ⇒ comptype ⇒ bool" where
	  mk_Expand :
		"(fun_expanddt v_deftype var_0) ⟹
		 (wf_comptype var_0) ⟹
		 (var_0 = v_comptype) ⟹
		 Expand v_deftype v_comptype"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:8.1-8.103 *)
inductive Vectype_sub :: "res_context ⇒ vectype ⇒ vectype ⇒ bool" where
	  mk_Vectype_sub :
		"Vectype_sub C v_vectype v_vectype"

(* Auxiliary Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:151.1-151.85 *)
function (sequential) before :: "typeuse ⇒ typeidx ⇒ nat ⇒ bool" where
		  "before (underscore_DEF v_rectype v_n) x i = True"
		| "before (underscore_IDX v_typeidx) x i = ((proj_uN_0 v_typeidx) < (proj_uN_0 x))"
		| "before (REC j) x i = (j < i)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:156.6-156.15 *)
inductive fun_unrollht :: "res_context ⇒ heaptype ⇒ subtype ⇒ bool" where
	  fun_unrollht_case_0 :
		"(fun_unrolldt (deftype__DEF v_rectype v_n) var_0) ⟹
		 fun_unrollht C (heaptype__DEF v_rectype v_n) var_0"
	| fun_unrollht_case_1 :
		"((proj_uN_0 v_typeidx) < (length (context_TYPES C))) ⟹
		 (fun_unrolldt ((context_TYPES C) ! (proj_uN_0 v_typeidx)) var_0) ⟹
		 fun_unrollht C (heaptype__IDX v_typeidx) var_0"
	| fun_unrollht_case_2 :
		"(i < (length (RECS C))) ⟹
		 fun_unrollht C (heaptype_REC i) ((RECS C) ! i)"

(* Mutual Recursion at: ../specification/wasm-3.0/2.1-validation.types.spectec:9.1-135.117 *)
inductive Heaptype_ok :: "res_context ⇒ heaptype ⇒ bool"
and Reftype_ok :: "res_context ⇒ reftype ⇒ bool"
and Valtype_ok :: "res_context ⇒ valtype ⇒ bool"
and Typeuse_ok :: "res_context ⇒ typeuse ⇒ bool"
and Resulttype_ok :: "res_context ⇒ resulttype ⇒ bool"
and Fieldtype_ok :: "res_context ⇒ fieldtype ⇒ bool"
and Storagetype_ok :: "res_context ⇒ storagetype ⇒ bool"
and Comptype_ok :: "res_context ⇒ comptype ⇒ bool"
and Subtype_ok :: "res_context ⇒ subtype ⇒ oktypeidx ⇒ bool"
and Rectype_ok :: "res_context ⇒ rectype ⇒ oktypeidx ⇒ bool"
and Subtype_ok2 :: "res_context ⇒ subtype ⇒ oktypeidxnat ⇒ bool"
and Rectype_ok2 :: "res_context ⇒ rectype ⇒ oktypeidxnat ⇒ bool"
and Deftype_ok :: "res_context ⇒ deftype ⇒ bool"
and Comptype_sub :: "res_context ⇒ comptype ⇒ comptype ⇒ bool"
and Deftype_sub :: "res_context ⇒ deftype ⇒ deftype ⇒ bool"
and Heaptype_sub :: "res_context ⇒ heaptype ⇒ heaptype ⇒ bool"
and Reftype_sub :: "res_context ⇒ reftype ⇒ reftype ⇒ bool"
and Valtype_sub :: "res_context ⇒ valtype ⇒ valtype ⇒ bool"
and Resulttype_sub :: "res_context ⇒ resulttype ⇒ resulttype ⇒ bool"
and Storagetype_sub :: "res_context ⇒ storagetype ⇒ storagetype ⇒ bool"
and Fieldtype_sub :: "res_context ⇒ fieldtype ⇒ fieldtype ⇒ bool" where
	  abs :
		"Heaptype_ok C (heaptype_absheaptype v_absheaptype)"
	| Heaptype_ok__typeuse :
		"(Typeuse_ok C v_typeuse) ⟹
		 Heaptype_ok C (heaptype_typeuse v_typeuse)"
	| mk_Reftype_ok :
		"(Heaptype_ok C v_heaptype) ⟹
		 Reftype_ok C (reftype_REF (Some NULL) v_heaptype)"
	| Valtype_ok__num :
		"(Numtype_ok C v_numtype) ⟹
		 Valtype_ok C (valtype_numtype v_numtype)"
	| Valtype_ok__vec :
		"(Vectype_ok C v_vectype) ⟹
		 Valtype_ok C (valtype_vectype v_vectype)"
	| Valtype_ok__ref :
		"(Reftype_ok C v_reftype) ⟹
		 Valtype_ok C (valtype_reftype v_reftype)"
	| bot :
		"Valtype_ok C valtype_BOT"
	| Typeuse_ok__typeidx :
		"((proj_uN_0 v_typeidx) < (length (context_TYPES C))) ⟹
		 (((context_TYPES C) ! (proj_uN_0 v_typeidx)) = dt) ⟹
		 Typeuse_ok C (underscore_IDX v_typeidx)"
	| rec :
		"(wf_subtype st) ⟹
		 (i < (length (RECS C))) ⟹
		 (((RECS C) ! i) = st) ⟹
		 Typeuse_ok C (REC i)"
	| Typeuse_ok__deftype :
		"(Deftype_ok C v_deftype) ⟹
		 Typeuse_ok C (typeuse_deftype v_deftype)"
	| mk_Resulttype_ok :
		"list_all (λ (t :: valtype). (Valtype_ok C t)) t_lst ⟹
		 Resulttype_ok C (mk_list t_lst)"
	| mk_Fieldtype_ok :
		"(Storagetype_ok C v_storagetype) ⟹
		 Fieldtype_ok C (mk_fieldtype (Some MUT) v_storagetype)"
	| Storagetype_ok__val :
		"(Valtype_ok C v_valtype) ⟹
		 Storagetype_ok C (storagetype_valtype v_valtype)"
	| pack :
		"(Packtype_ok C v_packtype) ⟹
		 Storagetype_ok C (storagetype_packtype v_packtype)"
	| struct :
		"list_all (λ (v_fieldtype :: fieldtype). (Fieldtype_ok C v_fieldtype)) fieldtype_lst ⟹
		 Comptype_ok C (comptype_STRUCT (mk_list fieldtype_lst))"
	| array :
		"(Fieldtype_ok C v_fieldtype) ⟹
		 Comptype_ok C (comptype_ARRAY v_fieldtype)"
	| Comptype_ok__func :
		"(Resulttype_ok C (mk_list t_1_lst)) ⟹
		 (Resulttype_ok C (mk_list t_2_lst)) ⟹
		 Comptype_ok C (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))"
	| mk_Subtype_ok :
		"((length var_0_lst) = (length x_lst)) ⟹
		 list_all (λ (x :: idx). ((proj_uN_0 x) < (length (context_TYPES C)))) x_lst ⟹
		 list_all2 (λ (var_0 :: subtype) (x :: idx). (fun_unrolldt ((context_TYPES C) ! (proj_uN_0 x)) var_0)) var_0_lst x_lst ⟹
		 list_all (λ (var_0 :: subtype). (wf_subtype var_0)) var_0_lst ⟹
		 ((length comptype'_lst) = (length x'_lst_lst)) ⟹
		 list_all2 (λ (comptype' :: comptype) (x'_lst :: (typeidx list)). (wf_subtype (SUB None (map (λ (x' :: idx). (underscore_IDX x')) x'_lst) comptype'))) comptype'_lst x'_lst_lst ⟹
		 ((length x_lst) ≤ 1) ⟹
		 list_all (λ (x :: idx). ((proj_uN_0 x) < (proj_uN_0 x_0))) x_lst ⟹
		 ((length var_0_lst) = (length comptype'_lst)) ⟹
		 ((length var_0_lst) = (length x'_lst_lst)) ⟹
		 list_all3 (λ (var_0 :: subtype) (comptype' :: comptype) (x'_lst :: (typeidx list)). (var_0 = (SUB None (map (λ (x' :: idx). (underscore_IDX x')) x'_lst) comptype'))) var_0_lst comptype'_lst x'_lst_lst ⟹
		 (Comptype_ok C v_comptype) ⟹
		 list_all (λ (comptype' :: comptype). (Comptype_sub C v_comptype comptype')) comptype'_lst ⟹
		 Subtype_ok C (SUB (Some FINAL) (map (λ (x :: idx). (underscore_IDX x)) x_lst) v_comptype) (oktypeidx_OK x_0)"
	| empty :
		"Rectype_ok C (rectype_REC (mk_list [])) (oktypeidx_OK x)"
	| cons :
		"(wf_oktypeidx (oktypeidx_OK x)) ⟹
		 (wf_oktypeidx (oktypeidx_OK (mk_uN ((proj_uN_0 x) + 1)))) ⟹
		 (Subtype_ok C subtype_1 (oktypeidx_OK x)) ⟹
		 (Rectype_ok C (rectype_REC (mk_list subtype_lst)) (oktypeidx_OK (mk_uN ((proj_uN_0 x) + 1)))) ⟹
		 Rectype_ok C (rectype_REC (mk_list ([subtype_1] @ subtype_lst))) (oktypeidx_OK x)"
	| underscore_rec2 :
		"(wf_context ⦇ context_TYPES = [], RECS = subtype_lst, context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (wf_oktypeidxnat (oktypeidxnat_OK x 0)) ⟹
		 (Rectype_ok2 (append_context ⦇ context_TYPES = [], RECS = subtype_lst, context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈ C) (rectype_REC (mk_list subtype_lst)) (oktypeidxnat_OK x 0)) ⟹
		 Rectype_ok C (rectype_REC (mk_list subtype_lst)) (oktypeidx_OK x)"
	| mk_Subtype_ok2 :
		"((length var_0_lst) = (length typeuse_lst)) ⟹
		 list_all2 (λ (var_0 :: subtype) (v_typeuse :: typeuse). (fun_unrollht C (heaptype_typeuse v_typeuse) var_0)) var_0_lst typeuse_lst ⟹
		 (wf_comptype v_comptype) ⟹
		 list_all (λ (var_0 :: subtype). (wf_subtype var_0)) var_0_lst ⟹
		 ((length comptype'_lst) = (length typeuse'_lst_lst)) ⟹
		 list_all2 (λ (comptype' :: comptype) (typeuse'_lst :: (typeuse list)). (wf_subtype (SUB None typeuse'_lst comptype'))) comptype'_lst typeuse'_lst_lst ⟹
		 ((length typeuse_lst) ≤ 1) ⟹
		 list_all (λ (v_typeuse :: typeuse). (before v_typeuse x i)) typeuse_lst ⟹
		 ((length var_0_lst) = (length comptype'_lst)) ⟹
		 ((length var_0_lst) = (length typeuse'_lst_lst)) ⟹
		 list_all3 (λ (var_0 :: subtype) (comptype' :: comptype) (typeuse'_lst :: (typeuse list)). (var_0 = (SUB None typeuse'_lst comptype'))) var_0_lst comptype'_lst typeuse'_lst_lst ⟹
		 (Comptype_ok C v_comptype) ⟹
		 list_all (λ (comptype' :: comptype). (Comptype_sub C v_comptype comptype')) comptype'_lst ⟹
		 Subtype_ok2 C (SUB (Some FINAL) typeuse_lst compttype) (oktypeidxnat_OK x i)"
	| Rectype_ok2__empty :
		"Rectype_ok2 C (rectype_REC (mk_list [])) (oktypeidxnat_OK x i)"
	| Rectype_ok2__cons :
		"(wf_oktypeidxnat (oktypeidxnat_OK x i)) ⟹
		 (wf_oktypeidxnat (oktypeidxnat_OK (mk_uN ((proj_uN_0 x) + 1)) (i + 1))) ⟹
		 (Subtype_ok2 C subtype_1 (oktypeidxnat_OK x i)) ⟹
		 (Rectype_ok2 C (rectype_REC (mk_list subtype_lst)) (oktypeidxnat_OK (mk_uN ((proj_uN_0 x) + 1)) (i + 1))) ⟹
		 Rectype_ok2 C (rectype_REC (mk_list ([subtype_1] @ subtype_lst))) (oktypeidxnat_OK x i)"
	| mk_Deftype_ok :
		"list_all (λ (v_subtype :: subtype). (wf_subtype v_subtype)) subtype_lst ⟹
		 (wf_oktypeidx (oktypeidx_OK x)) ⟹
		 (Rectype_ok C v_rectype (oktypeidx_OK x)) ⟹
		 (v_rectype = (rectype_REC (mk_list subtype_lst))) ⟹
		 (i < v_n) ⟹
		 (v_n = (length subtype_lst)) ⟹
		 Deftype_ok C (deftype__DEF v_rectype i)"
	| Comptype_sub__struct :
		"((length ft_1_lst) = (length ft_2_lst)) ⟹
		 list_all2 (λ (ft_1 :: fieldtype) (ft_2 :: fieldtype). (Fieldtype_sub C ft_1 ft_2)) ft_1_lst ft_2_lst ⟹
		 Comptype_sub C (comptype_STRUCT (mk_list (ft_1_lst @ ft'_1_lst))) (comptype_STRUCT (mk_list ft_2_lst))"
	| Comptype_sub__array :
		"(Fieldtype_sub C ft_1 ft_2) ⟹
		 Comptype_sub C (comptype_ARRAY ft_1) (comptype_ARRAY ft_2)"
	| Comptype_sub__func :
		"(Resulttype_sub C (mk_list t_21_lst) (mk_list t_11_lst)) ⟹
		 (Resulttype_sub C (mk_list t_12_lst) (mk_list t_22_lst)) ⟹
		 Comptype_sub C (comptype_FUNC (mk_list t_11_lst) (mk_list t_12_lst)) (comptype_FUNC (mk_list t_21_lst) (mk_list t_22_lst))"
	| refl :
		"(fun_clos_deftype C deftype_2 var_1) ⟹
		 (fun_clos_deftype C deftype_1 var_0) ⟹
		 (var_0 = var_1) ⟹
		 Deftype_sub C deftype_1 deftype_2"
	| super :
		"(fun_unrolldt deftype_1 var_0) ⟹
		 (wf_subtype var_0) ⟹
		 (wf_subtype (SUB final_opt typeuse_lst ct)) ⟹
		 (var_0 = (SUB final_opt typeuse_lst ct)) ⟹
		 (i < (length typeuse_lst)) ⟹
		 (Heaptype_sub C (heaptype_typeuse (typeuse_lst ! i)) (heaptype_deftype deftype_2)) ⟹
		 Deftype_sub C deftype_1 deftype_2"
	| Heaptype_sub__refl :
		"Heaptype_sub C v_heaptype v_heaptype"
	| trans :
		"(wf_heaptype heaptype') ⟹
		 (Heaptype_ok C heaptype') ⟹
		 (Heaptype_sub C heaptype_1 heaptype') ⟹
		 (Heaptype_sub C heaptype' heaptype_2) ⟹
		 Heaptype_sub C heaptype_1 heaptype_2"
	| eq_any :
		"Heaptype_sub C heaptype_EQ heaptype_ANY"
	| i31_eq :
		"Heaptype_sub C heaptype_I31 heaptype_EQ"
	| struct_eq :
		"Heaptype_sub C heaptype_STRUCT heaptype_EQ"
	| array_eq :
		"Heaptype_sub C heaptype_ARRAY heaptype_EQ"
	| Heaptype_sub__struct :
		"(wf_comptype (comptype_STRUCT (mk_list fieldtype_lst))) ⟹
		 (Expand v_deftype (comptype_STRUCT (mk_list fieldtype_lst))) ⟹
		 Heaptype_sub C (heaptype_deftype v_deftype) heaptype_STRUCT"
	| Heaptype_sub__array :
		"(wf_comptype (comptype_ARRAY v_fieldtype)) ⟹
		 (Expand v_deftype (comptype_ARRAY v_fieldtype)) ⟹
		 Heaptype_sub C (heaptype_deftype v_deftype) heaptype_ARRAY"
	| Heaptype_sub__func :
		"(wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (Expand v_deftype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Heaptype_sub C (heaptype_deftype v_deftype) heaptype_FUNC"
	| def :
		"(Deftype_sub C deftype_1 deftype_2) ⟹
		 Heaptype_sub C (heaptype_deftype deftype_1) (heaptype_deftype deftype_2)"
	| typeidx_l :
		"((proj_uN_0 v_typeidx) < (length (context_TYPES C))) ⟹
		 (Heaptype_sub C (heaptype_deftype ((context_TYPES C) ! (proj_uN_0 v_typeidx))) v_heaptype) ⟹
		 Heaptype_sub C (heaptype__IDX v_typeidx) v_heaptype"
	| typeidx_r :
		"((proj_uN_0 v_typeidx) < (length (context_TYPES C))) ⟹
		 (Heaptype_sub C v_heaptype (heaptype_deftype ((context_TYPES C) ! (proj_uN_0 v_typeidx)))) ⟹
		 Heaptype_sub C v_heaptype (heaptype__IDX v_typeidx)"
	| Heaptype_sub__rec :
		"(j < (length typeuse_lst)) ⟹
		 (wf_subtype (SUB final_opt typeuse_lst ct)) ⟹
		 (i < (length (RECS C))) ⟹
		 (((RECS C) ! i) = (SUB final_opt typeuse_lst ct)) ⟹
		 Heaptype_sub C (heaptype_REC i) (heaptype_typeuse (typeuse_lst ! j))"
	| none :
		"(wf_heaptype heaptype_ANY) ⟹
		 (Heaptype_sub C v_heaptype heaptype_ANY) ⟹
		 Heaptype_sub C heaptype_NONE v_heaptype"
	| nofunc :
		"(wf_heaptype heaptype_FUNC) ⟹
		 (Heaptype_sub C v_heaptype heaptype_FUNC) ⟹
		 Heaptype_sub C heaptype_NOFUNC v_heaptype"
	| noexn :
		"(wf_heaptype heaptype_EXN) ⟹
		 (Heaptype_sub C v_heaptype heaptype_EXN) ⟹
		 Heaptype_sub C heaptype_NOEXN v_heaptype"
	| noextern :
		"(wf_heaptype heaptype_EXTERN) ⟹
		 (Heaptype_sub C v_heaptype heaptype_EXTERN) ⟹
		 Heaptype_sub C heaptype_NOEXTERN v_heaptype"
	| Heaptype_sub__bot :
		"Heaptype_sub C heaptype_BOT v_heaptype"
	| nonnull :
		"(Heaptype_sub C ht_1 ht_2) ⟹
		 Reftype_sub C (reftype_REF None ht_1) (reftype_REF None ht_2)"
	| Reftype_sub__null :
		"(Heaptype_sub C ht_1 ht_2) ⟹
		 Reftype_sub C (reftype_REF (Some NULL) ht_1) (reftype_REF (Some NULL) ht_2)"
	| Valtype_sub__num :
		"(Numtype_sub C numtype_1 numtype_2) ⟹
		 Valtype_sub C (valtype_numtype numtype_1) (valtype_numtype numtype_2)"
	| Valtype_sub__vec :
		"(Vectype_sub C vectype_1 vectype_2) ⟹
		 Valtype_sub C (valtype_vectype vectype_1) (valtype_vectype vectype_2)"
	| Valtype_sub__ref :
		"(Reftype_sub C reftype_1 reftype_2) ⟹
		 Valtype_sub C (valtype_reftype reftype_1) (valtype_reftype reftype_2)"
	| Valtype_sub__bot :
		"Valtype_sub C valtype_BOT v_valtype"
	| mk_Resulttype_sub :
		"((length t_1_lst) = (length t_2_lst)) ⟹
		 list_all2 (λ (t_1 :: valtype) (t_2 :: valtype). (Valtype_sub C t_1 t_2)) t_1_lst t_2_lst ⟹
		 Resulttype_sub C (mk_list t_1_lst) (mk_list t_2_lst)"
	| Storagetype_sub__val :
		"(Valtype_sub C valtype_1 valtype_2) ⟹
		 Storagetype_sub C (storagetype_valtype valtype_1) (storagetype_valtype valtype_2)"
	| Storagetype_sub__pack :
		"(Packtype_sub C packtype_1 packtype_2) ⟹
		 Storagetype_sub C (storagetype_packtype packtype_1) (storagetype_packtype packtype_2)"
	| Fieldtype_sub__const :
		"(Storagetype_sub C zt_1 zt_2) ⟹
		 Fieldtype_sub C (mk_fieldtype None zt_1) (mk_fieldtype None zt_2)"
	| Fieldtype_sub__var :
		"(Storagetype_sub C zt_1 zt_2) ⟹
		 (Storagetype_sub C zt_2 zt_1) ⟹
		 Fieldtype_sub C (mk_fieldtype (Some MUT) zt_1) (mk_fieldtype (Some MUT) zt_2)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:50.1-50.99 *)
inductive Instrtype_ok :: "res_context ⇒ instrtype ⇒ bool" where
	  mk_Instrtype_ok :
		"list_all (λ (lct :: localtype). (wf_localtype lct)) lct_lst ⟹
		 (Resulttype_ok C (mk_list t_1_lst)) ⟹
		 (Resulttype_ok C (mk_list t_2_lst)) ⟹
		 ((length lct_lst) = (length x_lst)) ⟹
		 list_all (λ (x :: idx). ((proj_uN_0 x) < (length (context_LOCALS C)))) x_lst ⟹
		 list_all2 (λ (lct :: localtype) (x :: idx). (((context_LOCALS C) ! (proj_uN_0 x)) = lct)) lct_lst x_lst ⟹
		 Instrtype_ok C (mk_instrtype (mk_list t_1_lst) x_lst (mk_list t_2_lst))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:68.1-69.70 *)
inductive Expand_use :: "typeuse ⇒ res_context ⇒ comptype ⇒ bool" where
	  Expand_use__deftype :
		"(Expand v_deftype v_comptype) ⟹
		 Expand_use (typeuse_deftype v_deftype) C v_comptype"
	| Expand_use__typeidx :
		"((proj_uN_0 v_typeidx) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 v_typeidx)) v_comptype) ⟹
		 Expand_use (underscore_IDX v_typeidx) C v_comptype"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:201.1-201.120 *)
inductive Limits_ok :: "res_context ⇒ limits ⇒ nat ⇒ bool" where
	  mk_Limits_ok :
		"(v_n ≤ k) ⟹
		 list_all (λ (v_m :: nat). ((v_n ≤ v_m) ∧ (v_m ≤ k))) (option_to_list m_opt) ⟹
		 Limits_ok C (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)) k"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:202.1-202.97 *)
inductive Tagtype_ok :: "res_context ⇒ tagtype ⇒ bool" where
	  mk_Tagtype_ok :
		"(wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (Typeuse_ok C v_typeuse) ⟹
		 (Expand_use v_typeuse C (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Tagtype_ok C v_typeuse"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:203.1-203.100 *)
inductive Globaltype_ok :: "res_context ⇒ globaltype ⇒ bool" where
	  mk_Globaltype_ok :
		"(Valtype_ok C t) ⟹
		 Globaltype_ok C (mk_globaltype (Some MUT) t)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:204.1-204.97 *)
inductive Memtype_ok :: "res_context ⇒ memtype ⇒ bool" where
	  mk_Memtype_ok :
		"(Limits_ok C v_limits (2 ^ ((((size (numtype_addrtype v_addrtype)) :: nat) - (16 :: nat)) :: nat))) ⟹
		 Memtype_ok C (PAGE v_addrtype v_limits)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:205.1-205.99 *)
inductive Tabletype_ok :: "res_context ⇒ tabletype ⇒ bool" where
	  mk_Tabletype_ok :
		"(Limits_ok C v_limits ((((2 ^ (size (numtype_addrtype v_addrtype))) :: nat) - (1 :: nat)) :: nat)) ⟹
		 (Reftype_ok C v_reftype) ⟹
		 Tabletype_ok C (mk_tabletype v_addrtype v_limits v_reftype)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:206.1-206.100 *)
inductive Externtype_ok :: "res_context ⇒ externtype ⇒ bool" where
	  Externtype_ok__tag :
		"(Tagtype_ok C v_tagtype) ⟹
		 Externtype_ok C (externtype_TAG v_tagtype)"
	| Externtype_ok__global :
		"(Globaltype_ok C v_globaltype) ⟹
		 Externtype_ok C (externtype_GLOBAL v_globaltype)"
	| Externtype_ok__mem :
		"(Memtype_ok C v_memtype) ⟹
		 Externtype_ok C (externtype_MEM v_memtype)"
	| Externtype_ok__table :
		"(Tabletype_ok C v_tabletype) ⟹
		 Externtype_ok C (externtype_TABLE v_tabletype)"
	| Externtype_ok__func :
		"(wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (Typeuse_ok C v_typeuse) ⟹
		 (Expand_use v_typeuse C (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Externtype_ok C (externtype_FUNC v_typeuse)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:117.1-117.114 *)
inductive Instrtype_sub :: "res_context ⇒ instrtype ⇒ instrtype ⇒ bool" where
	  mk_Instrtype_sub :
		"list_all (λ (x :: idx). (wf_uN 32 x)) x_lst ⟹
		 list_all (λ (iter :: localidx). (wf_uN 32 iter)) (setminus_underscore  x_2_lst x_1_lst) ⟹
		 list_all (λ (t :: valtype). (wf_localtype (mk_localtype SET t))) t_lst ⟹
		 (Resulttype_sub C (mk_list t_21_lst) (mk_list t_11_lst)) ⟹
		 (Resulttype_sub C (mk_list t_12_lst) (mk_list t_22_lst)) ⟹
		 (x_lst = (setminus_underscore  x_2_lst x_1_lst)) ⟹
		 ((length t_lst) = (length x_lst)) ⟹
		 list_all (λ (x :: idx). ((proj_uN_0 x) < (length (context_LOCALS C)))) x_lst ⟹
		 list_all2 (λ (t :: valtype) (x :: idx). (((context_LOCALS C) ! (proj_uN_0 x)) = (mk_localtype SET t))) t_lst x_lst ⟹
		 Instrtype_sub C (mk_instrtype (mk_list t_11_lst) x_1_lst (mk_list t_12_lst)) (mk_instrtype (mk_list t_21_lst) x_2_lst (mk_list t_22_lst))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:191.1-191.110 *)
inductive Limits_sub :: "res_context ⇒ limits ⇒ limits ⇒ bool" where
	  max :
		"(n_1 ≥ n_2) ⟹
		 list_all (λ (m_2 :: nat). (m_1 ≤ m_2)) (option_to_list m_2_opt) ⟹
		 Limits_sub C (mk_limits (mk_uN n_1) (Some (mk_uN m_1))) (mk_limits (mk_uN n_2) (map_option (λ (m_2 :: m). (mk_uN m_2)) m_2_opt))"
	| eps :
		"(n_1 ≥ n_2) ⟹
		 Limits_sub C (mk_limits (mk_uN n_1) None) (mk_limits (mk_uN n_2) None)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:192.1-192.111 *)
inductive Tagtype_sub :: "res_context ⇒ tagtype ⇒ tagtype ⇒ bool" where
	  mk_Tagtype_sub :
		"(Deftype_sub C deftype_1 deftype_2) ⟹
		 (Deftype_sub C deftype_2 deftype_1) ⟹
		 Tagtype_sub C (typeuse_deftype deftype_1) (typeuse_deftype deftype_2)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:193.1-193.114 *)
inductive Globaltype_sub :: "res_context ⇒ globaltype ⇒ globaltype ⇒ bool" where
	  Globaltype_sub__const :
		"(Valtype_sub C valtype_1 valtype_2) ⟹
		 Globaltype_sub C (mk_globaltype None valtype_1) (mk_globaltype None valtype_2)"
	| Globaltype_sub__var :
		"(Valtype_sub C valtype_1 valtype_2) ⟹
		 (Valtype_sub C valtype_2 valtype_1) ⟹
		 Globaltype_sub C (mk_globaltype (Some MUT) valtype_1) (mk_globaltype (Some MUT) valtype_2)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:194.1-194.111 *)
inductive Memtype_sub :: "res_context ⇒ memtype ⇒ memtype ⇒ bool" where
	  mk_Memtype_sub :
		"(Limits_sub C limits_1 limits_2) ⟹
		 Memtype_sub C (PAGE v_addrtype limits_1) (PAGE v_addrtype limits_2)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:195.1-195.113 *)
inductive Tabletype_sub :: "res_context ⇒ tabletype ⇒ tabletype ⇒ bool" where
	  mk_Tabletype_sub :
		"(Limits_sub C limits_1 limits_2) ⟹
		 (Reftype_sub C reftype_1 reftype_2) ⟹
		 (Reftype_sub C reftype_2 reftype_1) ⟹
		 Tabletype_sub C (mk_tabletype v_addrtype limits_1 reftype_1) (mk_tabletype v_addrtype limits_2 reftype_2)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:196.1-196.114 *)
inductive Externtype_sub :: "res_context ⇒ externtype ⇒ externtype ⇒ bool" where
	  Externtype_sub__tag :
		"(Tagtype_sub C tagtype_1 tagtype_2) ⟹
		 Externtype_sub C (externtype_TAG tagtype_1) (externtype_TAG tagtype_2)"
	| Externtype_sub__global :
		"(Globaltype_sub C globaltype_1 globaltype_2) ⟹
		 Externtype_sub C (externtype_GLOBAL globaltype_1) (externtype_GLOBAL globaltype_2)"
	| Externtype_sub__mem :
		"(Memtype_sub C memtype_1 memtype_2) ⟹
		 Externtype_sub C (externtype_MEM memtype_1) (externtype_MEM memtype_2)"
	| Externtype_sub__table :
		"(Tabletype_sub C tabletype_1 tabletype_2) ⟹
		 Externtype_sub C (externtype_TABLE tabletype_1) (externtype_TABLE tabletype_2)"
	| Externtype_sub__func :
		"(Deftype_sub C deftype_1 deftype_2) ⟹
		 Externtype_sub C (externtype_FUNC (typeuse_deftype deftype_1)) (externtype_FUNC (typeuse_deftype deftype_2))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:42.1-42.121 *)
inductive Blocktype_ok :: "res_context ⇒ blocktype ⇒ instrtype ⇒ bool" where
	  Blocktype_ok__valtype :
		"list_all (λ (v_valtype :: valtype). (Valtype_ok C v_valtype)) (option_to_list valtype_opt) ⟹
		 Blocktype_ok C (underscore_RESULT valtype_opt) (mk_instrtype (mk_list []) [] (mk_list (option_to_list valtype_opt)))"
	| Blocktype_ok__typeidx :
		"(wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 ((proj_uN_0 v_typeidx) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 v_typeidx)) (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Blocktype_ok C (blocktype__IDX v_typeidx) (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:164.1-164.77 *)
inductive Catch_ok :: "res_context ⇒ catch ⇒ bool" where
	  Catch_ok__catch :
		"(wf_comptype (comptype_FUNC (mk_list t_lst) (mk_list []))) ⟹
		 ((as_deftype ((context_TAGS C) ! (proj_uN_0 x))) ≠ None) ⟹
		 ((proj_uN_0 x) < (length (context_TAGS C))) ⟹
		 (Expand (the ((as_deftype ((context_TAGS C) ! (proj_uN_0 x))))) (comptype_FUNC (mk_list t_lst) (mk_list []))) ⟹
		 ((proj_uN_0 l) < (length (context_LABELS C))) ⟹
		 (Resulttype_sub C (mk_list t_lst) ((context_LABELS C) ! (proj_uN_0 l))) ⟹
		 Catch_ok C (CATCH x l)"
	| catch_ref :
		"(wf_comptype (comptype_FUNC (mk_list t_lst) (mk_list []))) ⟹
		 ((as_deftype ((context_TAGS C) ! (proj_uN_0 x))) ≠ None) ⟹
		 ((proj_uN_0 x) < (length (context_TAGS C))) ⟹
		 (Expand (the ((as_deftype ((context_TAGS C) ! (proj_uN_0 x))))) (comptype_FUNC (mk_list t_lst) (mk_list []))) ⟹
		 ((proj_uN_0 l) < (length (context_LABELS C))) ⟹
		 (Resulttype_sub C (mk_list (t_lst @ [(REF None heaptype_EXN)])) ((context_LABELS C) ! (proj_uN_0 l))) ⟹
		 Catch_ok C (CATCH_REF x l)"
	| catch_all :
		"((proj_uN_0 l) < (length (context_LABELS C))) ⟹
		 (Resulttype_sub C (mk_list []) ((context_LABELS C) ! (proj_uN_0 l))) ⟹
		 Catch_ok C (CATCH_ALL l)"
	| catch_all_ref :
		"((proj_uN_0 l) < (length (context_LABELS C))) ⟹
		 (Resulttype_sub C (mk_list [(REF None heaptype_EXN)]) ((context_LABELS C) ! (proj_uN_0 l))) ⟹
		 Catch_ok C (CATCH_ALL_REF l)"

(* Auxiliary Definition at: ../specification/wasm-3.0/4.1-execution.values.spectec:7.1-7.44 *)
function (sequential) default_underscore :: "valtype ⇒ ((val option) option)" where
		  "default_underscore valtype_I32 = (Some (Some (res_CONST (numtype_addrtype I32) (mk_num__0 I32 (mk_uN 0)))))"
		| "default_underscore valtype_I64 = (Some (Some (res_CONST (numtype_addrtype I64) (mk_num__0 I64 (mk_uN 0)))))"
		| "default_underscore valtype_F32 = (Some (Some (res_CONST (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 (fzero (size (numtype_Fnn Fnn_F32)))))))"
		| "default_underscore valtype_F64 = (Some (Some (res_CONST (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 (fzero (size (numtype_Fnn Fnn_F64)))))))"
		| "default_underscore valtype_V128 = (Some (Some (VCONST V128 (mk_uN 0))))"
		| "default_underscore (REF (Some NULL) ht) = (Some (Some (REF_NULL ht)))"
		| "default_underscore (REF None ht) = (Some None)"
		| "default_underscore x0 = None"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:9.1-10.71 *)
inductive Defaultable :: "valtype ⇒ bool" where
	  mk_Defaultable :
		"list_all (λ (iter :: val). (wf_val iter)) (option_to_list (the ((default_underscore t)))) ⟹
		 ((default_underscore t) ≠ None) ⟹
		 ((the ((default_underscore t))) ≠ None) ⟹
		 Defaultable t"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:408.1-408.131 *)
inductive Memarg_ok :: "memarg ⇒ addrtype ⇒ N ⇒ bool" where
	  mk_Memarg_ok :
		"(((2 ^ v_n) :: nat) ≤ ((v_N :: nat) div (8 :: nat))) ⟹
		 (v_m < (2 ^ (size (numtype_addrtype at)))) ⟹
		 Memarg_ok ⦇ ALIGN = (mk_uN v_n), OFFSET = (mk_uN v_m) ⦈ at v_N"

(* Auxiliary Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:255.1-255.111 *)
function (sequential) is_packtype :: "storagetype ⇒ bool" where
		  "is_packtype zt = (zt ≠ (storagetype_valtype (unpack zt)))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:5.1-6.96 *)
inductive Instr_ok :: "res_context ⇒ instr ⇒ instrtype ⇒ bool"
and Instrs_ok :: "res_context ⇒ (instr list) ⇒ instrtype ⇒ bool" where
	  nop :
		"Instr_ok C (instr_sc0 NOP) (mk_instrtype (mk_list []) [] (mk_list []))"
	| unreachable :
		"(wf_instrtype (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (Instrtype_ok C (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc0 UNREACHABLE) (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))"
	| drop :
		"(Valtype_ok C t) ⟹
		 Instr_ok C (instr_sc0 DROP) (mk_instrtype (mk_list [t]) [] (mk_list []))"
	| select_expl :
		"(Valtype_ok C t) ⟹
		 Instr_ok C (instr_sc0 (SELECT (Some [t]))) (mk_instrtype (mk_list [t, t, valtype_I32]) [] (mk_list [t]))"
	| select_impl :
		"(wf_valtype t') ⟹
		 (Valtype_ok C t) ⟹
		 (Valtype_sub C t t') ⟹
		 ((t' = (valtype_numtype v_numtype)) ∨ (t' = (valtype_vectype v_vectype))) ⟹
		 Instr_ok C (instr_sc0 (SELECT None)) (mk_instrtype (mk_list [t, t, valtype_I32]) [] (mk_list [t]))"
	| block :
		"(wf_instrtype (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [(mk_list t_2_lst)], context_RETURN = None, REFS = [] ⦈) ⟹
		 (wf_instrtype (mk_instrtype (mk_list t_1_lst) x_lst (mk_list t_2_lst))) ⟹
		 (Blocktype_ok C bt (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (Instrs_ok (append_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [(mk_list t_2_lst)], context_RETURN = None, REFS = [] ⦈ C) instr_lst (mk_instrtype (mk_list t_1_lst) x_lst (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc9 (BLOCK bt instr_lst)) (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))"
	| loop :
		"(wf_instrtype (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [(mk_list t_1_lst)], context_RETURN = None, REFS = [] ⦈) ⟹
		 (wf_instrtype (mk_instrtype (mk_list t_1_lst) x_lst (mk_list t_2_lst))) ⟹
		 (Blocktype_ok C bt (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (Instrs_ok (append_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [(mk_list t_1_lst)], context_RETURN = None, REFS = [] ⦈ C) instr_lst (mk_instrtype (mk_list t_1_lst) x_lst (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc9 (LOOP bt instr_lst)) (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))"
	| res_if :
		"(wf_instrtype (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [(mk_list t_2_lst)], context_RETURN = None, REFS = [] ⦈) ⟹
		 (wf_instrtype (mk_instrtype (mk_list t_1_lst) x_1_lst (mk_list t_2_lst))) ⟹
		 (wf_instrtype (mk_instrtype (mk_list t_1_lst) x_2_lst (mk_list t_2_lst))) ⟹
		 (Blocktype_ok C bt (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (Instrs_ok (append_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [(mk_list t_2_lst)], context_RETURN = None, REFS = [] ⦈ C) instr_1_lst (mk_instrtype (mk_list t_1_lst) x_1_lst (mk_list t_2_lst))) ⟹
		 (Instrs_ok (append_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [(mk_list t_2_lst)], context_RETURN = None, REFS = [] ⦈ C) instr_2_lst (mk_instrtype (mk_list t_1_lst) x_2_lst (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc10 (IFELSE bt instr_1_lst instr_2_lst)) (mk_instrtype (mk_list (t_1_lst @ [valtype_I32])) [] (mk_list t_2_lst))"
	| br :
		"(wf_instrtype (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 ((proj_uN_0 l) < (length (context_LABELS C))) ⟹
		 ((proj_list_0  ((context_LABELS C) ! (proj_uN_0 l))) = t_lst) ⟹
		 (Instrtype_ok C (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc0 (BR l)) (mk_instrtype (mk_list (t_1_lst @ t_lst)) [] (mk_list t_2_lst))"
	| br_if :
		"((proj_uN_0 l) < (length (context_LABELS C))) ⟹
		 ((proj_list_0  ((context_LABELS C) ! (proj_uN_0 l))) = t_lst) ⟹
		 Instr_ok C (instr_sc0 (BR_IF l)) (mk_instrtype (mk_list (t_lst @ [valtype_I32])) [] (mk_list t_lst))"
	| br_table :
		"(wf_instrtype (mk_instrtype (mk_list (t_1_lst @ (t_lst @ [valtype_I32]))) [] (mk_list t_2_lst))) ⟹
		 list_all (λ (l :: labelidx). ((proj_uN_0 l) < (length (context_LABELS C)))) l_lst ⟹
		 list_all (λ (l :: labelidx). (Resulttype_sub C (mk_list t_lst) ((context_LABELS C) ! (proj_uN_0 l)))) l_lst ⟹
		 ((proj_uN_0 l') < (length (context_LABELS C))) ⟹
		 (Resulttype_sub C (mk_list t_lst) ((context_LABELS C) ! (proj_uN_0 l'))) ⟹
		 (Instrtype_ok C (mk_instrtype (mk_list (t_1_lst @ (t_lst @ [valtype_I32]))) [] (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc0 (BR_TABLE l_lst l')) (mk_instrtype (mk_list (t_1_lst @ (t_lst @ [valtype_I32]))) [] (mk_list t_2_lst))"
	| br_on_null :
		"((proj_uN_0 l) < (length (context_LABELS C))) ⟹
		 ((proj_list_0  ((context_LABELS C) ! (proj_uN_0 l))) = t_lst) ⟹
		 (Heaptype_ok C ht) ⟹
		 Instr_ok C (instr_sc0 (BR_ON_NULL l)) (mk_instrtype (mk_list (t_lst @ [(REF (Some NULL) ht)])) [] (mk_list (t_lst @ [(REF None ht)])))"
	| br_on_non_null :
		"((proj_uN_0 l) < (length (context_LABELS C))) ⟹
		 (((context_LABELS C) ! (proj_uN_0 l)) = (mk_list (t_lst @ [(REF (Some NULL) ht)]))) ⟹
		 Instr_ok C (instr_sc0 (BR_ON_NON_NULL l)) (mk_instrtype (mk_list (t_lst @ [(REF (Some NULL) ht)])) [] (mk_list t_lst))"
	| br_on_cast :
		"(wf_reftype rt) ⟹
		 ((proj_uN_0 l) < (length (context_LABELS C))) ⟹
		 (((context_LABELS C) ! (proj_uN_0 l)) = (mk_list (t_lst @ [(valtype_reftype rt)]))) ⟹
		 (Reftype_ok C rt_1) ⟹
		 (Reftype_ok C rt_2) ⟹
		 (Reftype_sub C rt_2 rt_1) ⟹
		 (Reftype_sub C rt_2 rt) ⟹
		 Instr_ok C (instr_sc0 (BR_ON_CAST l rt_1 rt_2)) (mk_instrtype (mk_list (t_lst @ [(valtype_reftype rt_1)])) [] (mk_list (t_lst @ [(valtype_reftype (diffrt rt_1 rt_2))])))"
	| br_on_cast_fail :
		"(wf_reftype rt) ⟹
		 (wf_reftype (diffrt rt_1 rt_2)) ⟹
		 ((proj_uN_0 l) < (length (context_LABELS C))) ⟹
		 (((context_LABELS C) ! (proj_uN_0 l)) = (mk_list (t_lst @ [(valtype_reftype rt)]))) ⟹
		 (Reftype_ok C rt_1) ⟹
		 (Reftype_ok C rt_2) ⟹
		 (Reftype_sub C rt_2 rt_1) ⟹
		 (Reftype_sub C (diffrt rt_1 rt_2) rt) ⟹
		 Instr_ok C (instr_sc0 (BR_ON_CAST_FAIL l rt_1 rt_2)) (mk_instrtype (mk_list (t_lst @ [(valtype_reftype rt_1)])) [] (mk_list (t_lst @ [(valtype_reftype rt_2)])))"
	| call :
		"(wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 ((proj_uN_0 x) < (length (context_FUNCS C))) ⟹
		 (Expand ((context_FUNCS C) ! (proj_uN_0 x)) (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc1 (CALL x)) (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))"
	| call_ref :
		"(wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc1 (CALL_REF (underscore_IDX x))) (mk_instrtype (mk_list (t_1_lst @ [(REF (Some NULL) (heaptype__IDX x))])) [] (mk_list t_2_lst))"
	| call_indirect :
		"(wf_tabletype (mk_tabletype at lim rt)) ⟹
		 (wf_reftype (reftype_REF (Some NULL) heaptype_FUNC)) ⟹
		 (wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype at lim rt)) ⟹
		 (Reftype_sub C rt (reftype_REF (Some NULL) heaptype_FUNC)) ⟹
		 ((proj_uN_0 y) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 y)) (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc1 (CALL_INDIRECT x (underscore_IDX y))) (mk_instrtype (mk_list (t_1_lst @ [(valtype_addrtype at)])) [] (mk_list t_2_lst))"
	| return :
		"(wf_instrtype (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 ((context_RETURN C) = (Some (mk_list t_lst))) ⟹
		 (Instrtype_ok C (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc1 RETURN) (mk_instrtype (mk_list (t_1_lst @ t_lst)) [] (mk_list t_2_lst))"
	| return_call :
		"list_all (λ (t'_2 :: valtype). (wf_valtype t'_2)) t'_2_lst ⟹
		 (wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (wf_instrtype (mk_instrtype (mk_list t_3_lst) [] (mk_list t_4_lst))) ⟹
		 ((proj_uN_0 x) < (length (context_FUNCS C))) ⟹
		 (Expand ((context_FUNCS C) ! (proj_uN_0 x)) (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 ((context_RETURN C) = (Some (mk_list t'_2_lst))) ⟹
		 (Resulttype_sub C (mk_list t_2_lst) (mk_list t'_2_lst)) ⟹
		 (Instrtype_ok C (mk_instrtype (mk_list t_3_lst) [] (mk_list t_4_lst))) ⟹
		 Instr_ok C (instr_sc1 (RETURN_CALL x)) (mk_instrtype (mk_list (t_3_lst @ t_1_lst)) [] (mk_list t_4_lst))"
	| return_call_ref :
		"list_all (λ (t'_2 :: valtype). (wf_valtype t'_2)) t'_2_lst ⟹
		 (wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (wf_instrtype (mk_instrtype (mk_list t_3_lst) [] (mk_list t_4_lst))) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 ((context_RETURN C) = (Some (mk_list t'_2_lst))) ⟹
		 (Resulttype_sub C (mk_list t_2_lst) (mk_list t'_2_lst)) ⟹
		 (Instrtype_ok C (mk_instrtype (mk_list t_3_lst) [] (mk_list t_4_lst))) ⟹
		 Instr_ok C (instr_sc1 (RETURN_CALL_REF (underscore_IDX x))) (mk_instrtype (mk_list (t_3_lst @ (t_1_lst @ [(REF (Some NULL) (heaptype__IDX x))]))) [] (mk_list t_4_lst))"
	| return_call_indirect :
		"list_all (λ (t'_2 :: valtype). (wf_valtype t'_2)) t'_2_lst ⟹
		 (wf_tabletype (mk_tabletype at lim rt)) ⟹
		 (wf_reftype (reftype_REF (Some NULL) heaptype_FUNC)) ⟹
		 (wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (wf_instrtype (mk_instrtype (mk_list t_3_lst) [] (mk_list t_4_lst))) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype at lim rt)) ⟹
		 (Reftype_sub C rt (reftype_REF (Some NULL) heaptype_FUNC)) ⟹
		 ((proj_uN_0 y) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 y)) (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 ((context_RETURN C) = (Some (mk_list t'_2_lst))) ⟹
		 (Resulttype_sub C (mk_list t_2_lst) (mk_list t'_2_lst)) ⟹
		 (Instrtype_ok C (mk_instrtype (mk_list t_3_lst) [] (mk_list t_4_lst))) ⟹
		 Instr_ok C (instr_sc1 (RETURN_CALL_INDIRECT x (underscore_IDX y))) (mk_instrtype (mk_list (t_3_lst @ (t_1_lst @ [(valtype_addrtype at)]))) [] (mk_list t_4_lst))"
	| throw :
		"(wf_comptype (comptype_FUNC (mk_list t_lst) (mk_list []))) ⟹
		 (wf_instrtype (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 ((as_deftype ((context_TAGS C) ! (proj_uN_0 x))) ≠ None) ⟹
		 ((proj_uN_0 x) < (length (context_TAGS C))) ⟹
		 (Expand (the ((as_deftype ((context_TAGS C) ! (proj_uN_0 x))))) (comptype_FUNC (mk_list t_lst) (mk_list []))) ⟹
		 (Instrtype_ok C (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc1 (THROW x)) (mk_instrtype (mk_list (t_1_lst @ t_lst)) [] (mk_list t_2_lst))"
	| throw_ref :
		"(wf_instrtype (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (Instrtype_ok C (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc1 THROW_REF) (mk_instrtype (mk_list (t_1_lst @ [(REF (Some NULL) heaptype_EXN)])) [] (mk_list t_2_lst))"
	| try_table :
		"(wf_instrtype (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [(mk_list t_2_lst)], context_RETURN = None, REFS = [] ⦈) ⟹
		 (wf_instrtype (mk_instrtype (mk_list t_1_lst) x_lst (mk_list t_2_lst))) ⟹
		 (Blocktype_ok C bt (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (Instrs_ok (append_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [(mk_list t_2_lst)], context_RETURN = None, REFS = [] ⦈ C) instr_lst (mk_instrtype (mk_list t_1_lst) x_lst (mk_list t_2_lst))) ⟹
		 list_all (λ (v_catch :: catch). (Catch_ok C v_catch)) catch_lst ⟹
		 Instr_ok C (instr_sc10 (TRY_TABLE bt (mk_list catch_lst) instr_lst)) (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))"
	| ref_null :
		"(Heaptype_ok C ht) ⟹
		 Instr_ok C (instr_sc4 (instr_st4_REF_NULL ht)) (mk_instrtype (mk_list []) [] (mk_list [(REF (Some NULL) ht)]))"
	| ref_func :
		"((proj_uN_0 x) < (length (context_FUNCS C))) ⟹
		 (((context_FUNCS C) ! (proj_uN_0 x)) = dt) ⟹
		 ((length (REFS C)) > 0) ⟹
		 (x ∈ set (REFS C)) ⟹
		 Instr_ok C (instr_sc4 (REF_FUNC x)) (mk_instrtype (mk_list []) [] (mk_list [(REF None (heaptype_deftype dt))]))"
	| ref_i31 :
		"Instr_ok C (instr_sc4 REF_I31) (mk_instrtype (mk_list [valtype_I32]) [] (mk_list [(REF None heaptype_I31)]))"
	| ref_is_null :
		"(Heaptype_ok C ht) ⟹
		 Instr_ok C (instr_sc4 REF_IS_NULL) (mk_instrtype (mk_list [(REF (Some NULL) ht)]) [] (mk_list [valtype_I32]))"
	| ref_as_non_null :
		"(Heaptype_ok C ht) ⟹
		 Instr_ok C (instr_sc4 REF_AS_NON_NULL) (mk_instrtype (mk_list [(REF (Some NULL) ht)]) [] (mk_list [(REF None ht)]))"
	| ref_eq :
		"Instr_ok C (instr_sc4 REF_EQ) (mk_instrtype (mk_list [(REF (Some NULL) heaptype_EQ), (REF (Some NULL) heaptype_EQ)]) [] (mk_list [valtype_I32]))"
	| ref_test :
		"(Reftype_ok C rt) ⟹
		 (Reftype_ok C rt') ⟹
		 (Reftype_sub C rt rt') ⟹
		 Instr_ok C (instr_sc4 (REF_TEST rt)) (mk_instrtype (mk_list [(valtype_reftype rt')]) [] (mk_list [valtype_I32]))"
	| ref_cast :
		"(Reftype_ok C rt) ⟹
		 (Reftype_ok C rt') ⟹
		 (Reftype_sub C rt rt') ⟹
		 Instr_ok C (instr_sc4 (REF_CAST rt)) (mk_instrtype (mk_list [(valtype_reftype rt')]) [] (mk_list [(valtype_reftype rt)]))"
	| i31_get :
		"Instr_ok C (instr_sc4 (I31_GET v_sx)) (mk_instrtype (mk_list [(REF (Some NULL) heaptype_I31)]) [] (mk_list [valtype_I32]))"
	| struct_new :
		"(wf_comptype (comptype_STRUCT (mk_list (list_zipWith (λ (mut_opt :: (mut option)) (zt :: storagetype). (mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_STRUCT (mk_list (list_zipWith (λ (mut_opt :: (mut option)) (zt :: storagetype). (mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ⟹
		 Instr_ok C (instr_sc4 (STRUCT_NEW x)) (mk_instrtype (mk_list (map (λ (zt :: storagetype). (unpack zt)) zt_lst)) [] (mk_list [(REF None (heaptype__IDX x))]))"
	| struct_new_default :
		"list_all (λ (zt :: storagetype). (wf_valtype (unpack zt))) zt_lst ⟹
		 (wf_comptype (comptype_STRUCT (mk_list (list_zipWith (λ (mut_opt :: (mut option)) (zt :: storagetype). (mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_STRUCT (mk_list (list_zipWith (λ (mut_opt :: (mut option)) (zt :: storagetype). (mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ⟹
		 list_all (λ (zt :: storagetype). (Defaultable (unpack zt))) zt_lst ⟹
		 Instr_ok C (instr_sc5 (STRUCT_NEW_DEFAULT x)) (mk_instrtype (mk_list []) [] (mk_list [(REF None (heaptype__IDX x))]))"
	| struct_get :
		"(wf_comptype (comptype_STRUCT (mk_list ft_lst))) ⟹
		 (wf_fieldtype (mk_fieldtype mut_opt zt)) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_STRUCT (mk_list ft_lst))) ⟹
		 ((proj_uN_0 i) < (length ft_lst)) ⟹
		 ((ft_lst ! (proj_uN_0 i)) = (mk_fieldtype mut_opt zt)) ⟹
		 ((sx_opt ≠ None) ⟷ (is_packtype zt)) ⟹
		 Instr_ok C (instr_sc5 (STRUCT_GET sx_opt x i)) (mk_instrtype (mk_list [(REF (Some NULL) (heaptype__IDX x))]) [] (mk_list [(unpack zt)]))"
	| struct_set :
		"(wf_comptype (comptype_STRUCT (mk_list ft_lst))) ⟹
		 (wf_fieldtype (mk_fieldtype (Some MUT) zt)) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_STRUCT (mk_list ft_lst))) ⟹
		 ((proj_uN_0 i) < (length ft_lst)) ⟹
		 ((ft_lst ! (proj_uN_0 i)) = (mk_fieldtype (Some MUT) zt)) ⟹
		 Instr_ok C (instr_sc5 (STRUCT_SET x i)) (mk_instrtype (mk_list [(REF (Some NULL) (heaptype__IDX x)), (unpack zt)]) [] (mk_list []))"
	| array_new :
		"(wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 Instr_ok C (instr_sc5 (ARRAY_NEW x)) (mk_instrtype (mk_list [(unpack zt), valtype_I32]) [] (mk_list [(REF None (heaptype__IDX x))]))"
	| array_new_default :
		"(wf_valtype (unpack zt)) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 (Defaultable (unpack zt)) ⟹
		 Instr_ok C (instr_sc5 (ARRAY_NEW_DEFAULT x)) (mk_instrtype (mk_list [valtype_I32]) [] (mk_list [(REF None (heaptype__IDX x))]))"
	| array_new_fixed :
		"(wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 Instr_ok C (instr_sc5 (ARRAY_NEW_FIXED x (mk_uN v_n))) (mk_instrtype (mk_list (repeat v_n (unpack zt))) [] (mk_list [(REF None (heaptype__IDX x))]))"
	| array_new_elem :
		"(wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt (storagetype_reftype rt)))) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_ARRAY (mk_fieldtype mut_opt (storagetype_reftype rt)))) ⟹
		 ((proj_uN_0 y) < (length (context_ELEMS C))) ⟹
		 (Reftype_sub C ((context_ELEMS C) ! (proj_uN_0 y)) rt) ⟹
		 Instr_ok C (instr_sc5 (ARRAY_NEW_ELEM x y)) (mk_instrtype (mk_list [valtype_I32, valtype_I32]) [] (mk_list [(REF None (heaptype__IDX x))]))"
	| array_new_data :
		"(wf_valtype (unpack zt)) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 (((unpack zt) = (valtype_numtype v_numtype)) ∨ ((unpack zt) = (valtype_vectype v_vectype))) ⟹
		 ((proj_uN_0 y) < (length (context_DATAS C))) ⟹
		 (((context_DATAS C) ! (proj_uN_0 y)) = OK) ⟹
		 Instr_ok C (instr_sc5 (ARRAY_NEW_DATA x y)) (mk_instrtype (mk_list [valtype_I32, valtype_I32]) [] (mk_list [(REF None (heaptype__IDX x))]))"
	| array_get :
		"(wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 ((sx_opt ≠ None) ⟷ (is_packtype zt)) ⟹
		 Instr_ok C (instr_sc5 (ARRAY_GET sx_opt x)) (mk_instrtype (mk_list [(REF (Some NULL) (heaptype__IDX x)), valtype_I32]) [] (mk_list [(unpack zt)]))"
	| array_set :
		"(wf_comptype (comptype_ARRAY (mk_fieldtype (Some MUT) zt))) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_ARRAY (mk_fieldtype (Some MUT) zt))) ⟹
		 Instr_ok C (instr_sc5 (ARRAY_SET x)) (mk_instrtype (mk_list [(REF (Some NULL) (heaptype__IDX x)), valtype_I32, (unpack zt)]) [] (mk_list []))"
	| array_len :
		"Instr_ok C (instr_sc5 ARRAY_LEN) (mk_instrtype (mk_list [(REF (Some NULL) heaptype_ARRAY)]) [] (mk_list [valtype_I32]))"
	| array_fill :
		"(wf_comptype (comptype_ARRAY (mk_fieldtype (Some MUT) zt))) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_ARRAY (mk_fieldtype (Some MUT) zt))) ⟹
		 Instr_ok C (instr_sc6 (ARRAY_FILL x)) (mk_instrtype (mk_list [(REF (Some NULL) (heaptype__IDX x)), valtype_I32, (unpack zt), valtype_I32]) [] (mk_list []))"
	| array_copy :
		"(wf_comptype (comptype_ARRAY (mk_fieldtype (Some MUT) zt_1))) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt_2))) ⟹
		 ((proj_uN_0 x_1) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x_1)) (comptype_ARRAY (mk_fieldtype (Some MUT) zt_1))) ⟹
		 ((proj_uN_0 x_2) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x_2)) (comptype_ARRAY (mk_fieldtype mut_opt zt_2))) ⟹
		 (Storagetype_sub C zt_2 zt_1) ⟹
		 Instr_ok C (instr_sc6 (ARRAY_COPY x_1 x_2)) (mk_instrtype (mk_list [(REF (Some NULL) (heaptype__IDX x_1)), valtype_I32, (REF (Some NULL) (heaptype__IDX x_2)), valtype_I32, valtype_I32]) [] (mk_list []))"
	| array_init_elem :
		"(wf_comptype (comptype_ARRAY (mk_fieldtype (Some MUT) zt))) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_ARRAY (mk_fieldtype (Some MUT) zt))) ⟹
		 ((proj_uN_0 y) < (length (context_ELEMS C))) ⟹
		 (Storagetype_sub C (storagetype_reftype ((context_ELEMS C) ! (proj_uN_0 y))) zt) ⟹
		 Instr_ok C (instr_sc6 (ARRAY_INIT_ELEM x y)) (mk_instrtype (mk_list [(REF (Some NULL) (heaptype__IDX x)), valtype_I32, valtype_I32, valtype_I32]) [] (mk_list []))"
	| array_init_data :
		"(wf_valtype (unpack zt)) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype (Some MUT) zt))) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_ARRAY (mk_fieldtype (Some MUT) zt))) ⟹
		 (((unpack zt) = (valtype_numtype v_numtype)) ∨ ((unpack zt) = (valtype_vectype v_vectype))) ⟹
		 ((proj_uN_0 y) < (length (context_DATAS C))) ⟹
		 (((context_DATAS C) ! (proj_uN_0 y)) = OK) ⟹
		 Instr_ok C (instr_sc6 (ARRAY_INIT_DATA x y)) (mk_instrtype (mk_list [(REF (Some NULL) (heaptype__IDX x)), valtype_I32, valtype_I32, valtype_I32]) [] (mk_list []))"
	| extern_convert_any :
		"(null_1_opt = null_2_opt) ⟹
		 Instr_ok C (instr_sc6 EXTERN_CONVERT_ANY) (mk_instrtype (mk_list [(REF null_1_opt heaptype_ANY)]) [] (mk_list [(REF null_2_opt heaptype_EXTERN)]))"
	| any_convert_extern :
		"(null_1_opt = null_2_opt) ⟹
		 Instr_ok C (instr_sc6 ANY_CONVERT_EXTERN) (mk_instrtype (mk_list [(REF null_1_opt heaptype_EXTERN)]) [] (mk_list [(REF null_2_opt heaptype_ANY)]))"
	| local_get :
		"(wf_localtype (mk_localtype SET t)) ⟹
		 ((proj_uN_0 x) < (length (context_LOCALS C))) ⟹
		 (((context_LOCALS C) ! (proj_uN_0 x)) = (mk_localtype SET t)) ⟹
		 Instr_ok C (instr_sc1 (LOCAL_GET x)) (mk_instrtype (mk_list []) [] (mk_list [t]))"
	| local_set :
		"(wf_localtype (mk_localtype v_init t)) ⟹
		 ((proj_uN_0 x) < (length (context_LOCALS C))) ⟹
		 (((context_LOCALS C) ! (proj_uN_0 x)) = (mk_localtype v_init t)) ⟹
		 Instr_ok C (instr_sc1 (LOCAL_SET x)) (mk_instrtype (mk_list [t]) [x] (mk_list []))"
	| local_tee :
		"(wf_localtype (mk_localtype v_init t)) ⟹
		 ((proj_uN_0 x) < (length (context_LOCALS C))) ⟹
		 (((context_LOCALS C) ! (proj_uN_0 x)) = (mk_localtype v_init t)) ⟹
		 Instr_ok C (instr_sc2 (LOCAL_TEE x)) (mk_instrtype (mk_list [t]) [x] (mk_list [t]))"
	| global_get :
		"(wf_globaltype (mk_globaltype mut_opt t)) ⟹
		 ((proj_uN_0 x) < (length (context_GLOBALS C))) ⟹
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype mut_opt t)) ⟹
		 Instr_ok C (instr_sc2 (GLOBAL_GET x)) (mk_instrtype (mk_list []) [] (mk_list [t]))"
	| global_set :
		"(wf_globaltype (mk_globaltype (Some MUT) t)) ⟹
		 ((proj_uN_0 x) < (length (context_GLOBALS C))) ⟹
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype (Some MUT) t)) ⟹
		 Instr_ok C (instr_sc2 (GLOBAL_SET x)) (mk_instrtype (mk_list [t]) [] (mk_list []))"
	| table_get :
		"(wf_tabletype (mk_tabletype at lim rt)) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype at lim rt)) ⟹
		 Instr_ok C (instr_sc2 (TABLE_GET x)) (mk_instrtype (mk_list [(valtype_addrtype at)]) [] (mk_list [(valtype_reftype rt)]))"
	| table_set :
		"(wf_tabletype (mk_tabletype at lim rt)) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype at lim rt)) ⟹
		 Instr_ok C (instr_sc2 (TABLE_SET x)) (mk_instrtype (mk_list [(valtype_addrtype at), (valtype_reftype rt)]) [] (mk_list []))"
	| table_size :
		"(wf_tabletype (mk_tabletype at lim rt)) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype at lim rt)) ⟹
		 Instr_ok C (instr_sc2 (TABLE_SIZE x)) (mk_instrtype (mk_list []) [] (mk_list [(valtype_addrtype at)]))"
	| table_grow :
		"(wf_tabletype (mk_tabletype at lim rt)) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype at lim rt)) ⟹
		 Instr_ok C (instr_sc2 (TABLE_GROW x)) (mk_instrtype (mk_list [(valtype_reftype rt), (valtype_addrtype at)]) [] (mk_list [valtype_I32]))"
	| table_fill :
		"(wf_tabletype (mk_tabletype at lim rt)) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype at lim rt)) ⟹
		 Instr_ok C (instr_sc2 (TABLE_FILL x)) (mk_instrtype (mk_list [(valtype_addrtype at), (valtype_reftype rt), (valtype_addrtype at)]) [] (mk_list []))"
	| table_copy :
		"(wf_tabletype (mk_tabletype at_1 lim_1 rt_1)) ⟹
		 (wf_tabletype (mk_tabletype at_2 lim_2 rt_2)) ⟹
		 ((proj_uN_0 x_1) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x_1)) = (mk_tabletype at_1 lim_1 rt_1)) ⟹
		 ((proj_uN_0 x_2) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x_2)) = (mk_tabletype at_2 lim_2 rt_2)) ⟹
		 (Reftype_sub C rt_2 rt_1) ⟹
		 Instr_ok C (instr_sc2 (TABLE_COPY x_1 x_2)) (mk_instrtype (mk_list [(valtype_addrtype at_1), (valtype_addrtype at_2), (valtype_addrtype (minat at_1 at_2))]) [] (mk_list []))"
	| table_init :
		"(wf_reftype rt_2) ⟹
		 (wf_tabletype (mk_tabletype at lim rt_1)) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype at lim rt_1)) ⟹
		 ((proj_uN_0 y) < (length (context_ELEMS C))) ⟹
		 (((context_ELEMS C) ! (proj_uN_0 y)) = rt_2) ⟹
		 (Reftype_sub C rt_2 rt_1) ⟹
		 Instr_ok C (instr_sc2 (TABLE_INIT x y)) (mk_instrtype (mk_list [(valtype_addrtype at), valtype_I32, valtype_I32]) [] (mk_list []))"
	| elem_drop :
		"(wf_reftype rt) ⟹
		 ((proj_uN_0 x) < (length (context_ELEMS C))) ⟹
		 (((context_ELEMS C) ! (proj_uN_0 x)) = rt) ⟹
		 Instr_ok C (instr_sc2 (ELEM_DROP x)) (mk_instrtype (mk_list []) [] (mk_list []))"
	| memory_size :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 Instr_ok C (instr_sc3 (MEMORY_SIZE x)) (mk_instrtype (mk_list []) [] (mk_list [(valtype_addrtype at)]))"
	| memory_grow :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 Instr_ok C (instr_sc3 (MEMORY_GROW x)) (mk_instrtype (mk_list [(valtype_addrtype at)]) [] (mk_list [(valtype_addrtype at)]))"
	| memory_fill :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 Instr_ok C (instr_sc3 (MEMORY_FILL x)) (mk_instrtype (mk_list [(valtype_addrtype at), valtype_I32, (valtype_addrtype at)]) [] (mk_list []))"
	| memory_copy :
		"(wf_memtype (PAGE at_1 lim_1)) ⟹
		 (wf_memtype (PAGE at_2 lim_2)) ⟹
		 ((proj_uN_0 x_1) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x_1)) = (PAGE at_1 lim_1)) ⟹
		 ((proj_uN_0 x_2) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x_2)) = (PAGE at_2 lim_2)) ⟹
		 Instr_ok C (instr_sc3 (MEMORY_COPY x_1 x_2)) (mk_instrtype (mk_list [(valtype_addrtype at_1), (valtype_addrtype at_2), (valtype_addrtype (minat at_1 at_2))]) [] (mk_list []))"
	| memory_init :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 ((proj_uN_0 y) < (length (context_DATAS C))) ⟹
		 (((context_DATAS C) ! (proj_uN_0 y)) = OK) ⟹
		 Instr_ok C (instr_sc3 (MEMORY_INIT x y)) (mk_instrtype (mk_list [(valtype_addrtype at), valtype_I32, valtype_I32]) [] (mk_list []))"
	| data_drop :
		"((proj_uN_0 x) < (length (context_DATAS C))) ⟹
		 (((context_DATAS C) ! (proj_uN_0 x)) = OK) ⟹
		 Instr_ok C (instr_sc4 (DATA_DROP x)) (mk_instrtype (mk_list []) [] (mk_list []))"
	| load_val :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 (Memarg_ok v_memarg at (size nt)) ⟹
		 Instr_ok C (instr_sc3 (LOAD nt None x v_memarg)) (mk_instrtype (mk_list [(valtype_addrtype at)]) [] (mk_list [(valtype_numtype nt)]))"
	| load_pack :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 (Memarg_ok v_memarg at v_M) ⟹
		 Instr_ok C (instr_sc3 (LOAD (numtype_addrtype v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_M) v_sx))) x v_memarg)) (mk_instrtype (mk_list [(valtype_addrtype at)]) [] (mk_list [(valtype_addrtype v_Inn)]))"
	| store_val :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 (Memarg_ok v_memarg at (size nt)) ⟹
		 Instr_ok C (instr_sc3 (STORE nt None x v_memarg)) (mk_instrtype (mk_list [(valtype_addrtype at), (valtype_numtype nt)]) [] (mk_list []))"
	| store_pack :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 (Memarg_ok v_memarg at v_M) ⟹
		 Instr_ok C (instr_sc3 (STORE (numtype_addrtype v_Inn) (Some (mk_storeop__0 v_Inn (mk_storeop_Inn (mk_sz v_M)))) x v_memarg)) (mk_instrtype (mk_list [(valtype_addrtype at), (valtype_addrtype v_Inn)]) [] (mk_list []))"
	| vload_val :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 (Memarg_ok v_memarg at (vsize V128)) ⟹
		 Instr_ok C (instr_sc3 (VLOAD V128 None x v_memarg)) (mk_instrtype (mk_list [(valtype_addrtype at)]) [] (mk_list [valtype_V128]))"
	| vload_pack :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 (Memarg_ok v_memarg at (v_M * v_N)) ⟹
		 Instr_ok C (instr_sc3 (VLOAD V128 (Some (SHAPEX_underscore (mk_sz v_M) v_N v_sx)) x v_memarg)) (mk_instrtype (mk_list [(valtype_addrtype at)]) [] (mk_list [valtype_V128]))"
	| vload_splat :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 (Memarg_ok v_memarg at v_N) ⟹
		 Instr_ok C (instr_sc3 (VLOAD V128 (Some (SPLAT (mk_sz v_N))) x v_memarg)) (mk_instrtype (mk_list [(valtype_addrtype at)]) [] (mk_list [valtype_V128]))"
	| vload_zero :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 (Memarg_ok v_memarg at v_N) ⟹
		 Instr_ok C (instr_sc3 (VLOAD V128 (Some (vloadop__ZERO (mk_sz v_N))) x v_memarg)) (mk_instrtype (mk_list [(valtype_addrtype at)]) [] (mk_list [valtype_V128]))"
	| vload_lane :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 (Memarg_ok v_memarg at v_N) ⟹
		 (((proj_uN_0 i) :: nat) < ((128 :: nat) div (v_N :: nat))) ⟹
		 Instr_ok C (instr_sc3 (VLOAD_LANE V128 (mk_sz v_N) x v_memarg i)) (mk_instrtype (mk_list [(valtype_addrtype at), valtype_V128]) [] (mk_list [valtype_V128]))"
	| vstore :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 (Memarg_ok v_memarg at (vsize V128)) ⟹
		 Instr_ok C (instr_sc3 (VSTORE V128 x v_memarg)) (mk_instrtype (mk_list [(valtype_addrtype at), valtype_V128]) [] (mk_list []))"
	| vstore_lane :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 (Memarg_ok v_memarg at v_N) ⟹
		 (((proj_uN_0 i) :: nat) < ((128 :: nat) div (v_N :: nat))) ⟹
		 Instr_ok C (instr_sc3 (VSTORE_LANE V128 (mk_sz v_N) x v_memarg i)) (mk_instrtype (mk_list [(valtype_addrtype at), valtype_V128]) [] (mk_list []))"
	| Instr_ok__const :
		"Instr_ok C (instr_sc6 (instr_st6_CONST nt c_nt)) (mk_instrtype (mk_list []) [] (mk_list [(valtype_numtype nt)]))"
	| unop :
		"Instr_ok C (instr_sc6 (UNOP nt unop_nt)) (mk_instrtype (mk_list [(valtype_numtype nt)]) [] (mk_list [(valtype_numtype nt)]))"
	| binop :
		"Instr_ok C (instr_sc6 (BINOP nt binop_nt)) (mk_instrtype (mk_list [(valtype_numtype nt), (valtype_numtype nt)]) [] (mk_list [(valtype_numtype nt)]))"
	| testop :
		"Instr_ok C (instr_sc6 (TESTOP nt testop_nt)) (mk_instrtype (mk_list [(valtype_numtype nt)]) [] (mk_list [valtype_I32]))"
	| relop :
		"Instr_ok C (instr_sc6 (RELOP nt relop_nt)) (mk_instrtype (mk_list [(valtype_numtype nt), (valtype_numtype nt)]) [] (mk_list [valtype_I32]))"
	| cvtop :
		"Instr_ok C (instr_sc7 (CVTOP nt_1 nt_2 cvtop)) (mk_instrtype (mk_list [(valtype_numtype nt_2)]) [] (mk_list [(valtype_numtype nt_1)]))"
	| vconst :
		"Instr_ok C (instr_sc7 (instr_st7_VCONST V128 c)) (mk_instrtype (mk_list []) [] (mk_list [valtype_V128]))"
	| Instr_ok__vvunop :
		"Instr_ok C (instr_sc7 (VVUNOP V128 v_vvunop)) (mk_instrtype (mk_list [valtype_V128]) [] (mk_list [valtype_V128]))"
	| Instr_ok__vvbinop :
		"Instr_ok C (instr_sc7 (VVBINOP V128 v_vvbinop)) (mk_instrtype (mk_list [valtype_V128, valtype_V128]) [] (mk_list [valtype_V128]))"
	| Instr_ok__vvternop :
		"Instr_ok C (instr_sc7 (VVTERNOP V128 v_vvternop)) (mk_instrtype (mk_list [valtype_V128, valtype_V128, valtype_V128]) [] (mk_list [valtype_V128]))"
	| Instr_ok__vvtestop :
		"Instr_ok C (instr_sc7 (VVTESTOP V128 v_vvtestop)) (mk_instrtype (mk_list [valtype_V128]) [] (mk_list [valtype_I32]))"
	| vunop :
		"Instr_ok C (instr_sc7 (VUNOP sh vunop)) (mk_instrtype (mk_list [valtype_V128]) [] (mk_list [valtype_V128]))"
	| vbinop :
		"Instr_ok C (instr_sc7 (VBINOP sh vbinop)) (mk_instrtype (mk_list [valtype_V128, valtype_V128]) [] (mk_list [valtype_V128]))"
	| vternop :
		"Instr_ok C (instr_sc7 (VTERNOP sh vternop)) (mk_instrtype (mk_list [valtype_V128, valtype_V128, valtype_V128]) [] (mk_list [valtype_V128]))"
	| vtestop :
		"Instr_ok C (instr_sc7 (VTESTOP sh vtestop)) (mk_instrtype (mk_list [valtype_V128]) [] (mk_list [valtype_I32]))"
	| vrelop :
		"Instr_ok C (instr_sc7 (VRELOP sh vrelop)) (mk_instrtype (mk_list [valtype_V128, valtype_V128]) [] (mk_list [valtype_V128]))"
	| vshiftop :
		"Instr_ok C (instr_sc8 (VSHIFTOP sh vshiftop)) (mk_instrtype (mk_list [valtype_V128, valtype_I32]) [] (mk_list [valtype_V128]))"
	| vbitmask :
		"Instr_ok C (instr_sc8 (VBITMASK sh)) (mk_instrtype (mk_list [valtype_V128]) [] (mk_list [valtype_I32]))"
	| vswizzlop :
		"Instr_ok C (instr_sc8 (VSWIZZLOP sh vswizzlop)) (mk_instrtype (mk_list [valtype_V128, valtype_V128]) [] (mk_list [valtype_V128]))"
	| vshuffle :
		"(wf_dim (fun_dim (proj_bshape_0 sh))) ⟹
		 list_all (λ (i :: laneidx). ((proj_uN_0 i) < (2 * (proj_dim_0 (fun_dim (proj_bshape_0 sh)))))) i_lst ⟹
		 Instr_ok C (instr_sc8 (VSHUFFLE sh i_lst)) (mk_instrtype (mk_list [valtype_V128, valtype_V128]) [] (mk_list [valtype_V128]))"
	| vsplat :
		"Instr_ok C (instr_sc8 (VSPLAT sh)) (mk_instrtype (mk_list [(valtype_numtype (unpackshape sh))]) [] (mk_list [valtype_V128]))"
	| vextract_lane :
		"(wf_dim (fun_dim sh)) ⟹
		 ((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) ⟹
		 Instr_ok C (instr_sc8 (VEXTRACT_LANE sh sx_opt i)) (mk_instrtype (mk_list [valtype_V128]) [] (mk_list [(valtype_numtype (unpackshape sh))]))"
	| vreplace_lane :
		"(wf_dim (fun_dim sh)) ⟹
		 ((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) ⟹
		 Instr_ok C (instr_sc9 (VREPLACE_LANE sh i)) (mk_instrtype (mk_list [valtype_V128, (valtype_numtype (unpackshape sh))]) [] (mk_list [valtype_V128]))"
	| vextunop :
		"Instr_ok C (instr_sc8 (VEXTUNOP sh_1 sh_2 vextunop)) (mk_instrtype (mk_list [valtype_V128]) [] (mk_list [valtype_V128]))"
	| vextbinop :
		"Instr_ok C (instr_sc8 (VEXTBINOP sh_1 sh_2 vextbinop)) (mk_instrtype (mk_list [valtype_V128, valtype_V128]) [] (mk_list [valtype_V128]))"
	| vextternop :
		"Instr_ok C (instr_sc8 (VEXTTERNOP sh_1 sh_2 vextternop)) (mk_instrtype (mk_list [valtype_V128, valtype_V128, valtype_V128]) [] (mk_list [valtype_V128]))"
	| vnarrow :
		"Instr_ok C (instr_sc8 (VNARROW sh_1 sh_2 v_sx)) (mk_instrtype (mk_list [valtype_V128, valtype_V128]) [] (mk_list [valtype_V128]))"
	| vcvtop :
		"Instr_ok C (instr_sc8 (VCVTOP sh_1 sh_2 vcvtop)) (mk_instrtype (mk_list [valtype_V128]) [] (mk_list [valtype_V128]))"
	| Instrs_ok__empty :
		"Instrs_ok C [] (mk_instrtype (mk_list []) [] (mk_list []))"
	| Instrs_ok__instr :
		"(wf_instrtype (mk_instrtype (mk_list t_1_lst) x_lst (mk_list t_2_lst))) ⟹
		 (Instr_ok C v_instr (mk_instrtype (mk_list t_1_lst) x_lst (mk_list t_2_lst))) ⟹
		 Instrs_ok C [v_instr] (mk_instrtype (mk_list t_1_lst) x_lst (mk_list t_2_lst))"
	| seq :
		"(fun_with_locals C x_1_lst (map (λ (t :: valtype). (mk_localtype SET t)) t_lst) var_0) ⟹
		 (var_0 ≠ None) ⟹
		 (wf_context (the (var_0))) ⟹
		 (wf_instrtype (mk_instrtype (mk_list t_1_lst) x_1_lst (mk_list t_2_lst))) ⟹
		 ((length init_lst) = (length t_lst)) ⟹
		 list_all2 (λ (v_init :: init) (t :: valtype). (wf_localtype (mk_localtype v_init t))) init_lst t_lst ⟹
		 list_all (λ (t :: valtype). (wf_localtype (mk_localtype SET t))) t_lst ⟹
		 (wf_instrtype (mk_instrtype (mk_list t_2_lst) x_2_lst (mk_list t_3_lst))) ⟹
		 (Instrs_ok C instr_1_lst (mk_instrtype (mk_list t_1_lst) x_1_lst (mk_list t_2_lst))) ⟹
		 ((length init_lst) = (length x_1_lst)) ⟹
		 list_all (λ (x_1 :: idx). ((proj_uN_0 x_1) < (length (context_LOCALS C)))) x_1_lst ⟹
		 list_all3 (λ (v_init :: init) (t :: valtype) (x_1 :: idx). (((context_LOCALS C) ! (proj_uN_0 x_1)) = (mk_localtype v_init t))) init_lst t_lst x_1_lst ⟹
		 (Instrs_ok (the (var_0)) instr_2_lst (mk_instrtype (mk_list t_2_lst) x_2_lst (mk_list t_3_lst))) ⟹
		 Instrs_ok C (instr_1_lst @ instr_2_lst) (mk_instrtype (mk_list t_1_lst) (x_1_lst @ x_2_lst) (mk_list t_3_lst))"
	| sub :
		"(wf_instrtype it) ⟹
		 (Instrs_ok C instr_lst it) ⟹
		 (Instrtype_sub C it it') ⟹
		 (Instrtype_ok C it') ⟹
		 Instrs_ok C instr_lst it'"
	| Instrs_ok__frame :
		"(wf_instrtype (mk_instrtype (mk_list t_1_lst) x_lst (mk_list t_2_lst))) ⟹
		 (Instrs_ok C instr_lst (mk_instrtype (mk_list t_1_lst) x_lst (mk_list t_2_lst))) ⟹
		 (Resulttype_ok C (mk_list t_lst)) ⟹
		 Instrs_ok C instr_lst (mk_instrtype (mk_list (t_lst @ t_1_lst)) x_lst (mk_list (t_lst @ t_2_lst)))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:7.1-7.94 *)
inductive Expr_ok :: "res_context ⇒ expr ⇒ resulttype ⇒ bool" where
	  mk_Expr_ok :
		"(wf_instrtype (mk_instrtype (mk_list []) [] (mk_list t_lst))) ⟹
		 (Instrs_ok C instr_lst (mk_instrtype (mk_list []) [] (mk_list t_lst))) ⟹
		 Expr_ok C instr_lst (mk_list t_lst)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:12.1-13.75 *)
inductive Nondefaultable :: "valtype ⇒ bool" where
	  mk_Nondefaultable :
		"list_all (λ (iter :: val). (wf_val iter)) (option_to_list (the ((default_underscore t)))) ⟹
		 ((default_underscore t) ≠ None) ⟹
		 ((the ((default_underscore t))) = None) ⟹
		 Nondefaultable t"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:649.1-649.104 *)
inductive Instr_const :: "res_context ⇒ instr ⇒ bool" where
	  Instr_const__const :
		"Instr_const C (instr_sc6 (instr_st6_CONST nt c_nt))"
	| Instr_const__vconst :
		"Instr_const C (instr_sc7 (instr_st7_VCONST vt c_vt))"
	| Instr_const__ref_null :
		"Instr_const C (instr_sc4 (instr_st4_REF_NULL ht))"
	| Instr_const__ref_i31 :
		"Instr_const C (instr_sc4 REF_I31)"
	| Instr_const__ref_func :
		"Instr_const C (instr_sc4 (REF_FUNC x))"
	| Instr_const__struct_new :
		"Instr_const C (instr_sc4 (STRUCT_NEW x))"
	| Instr_const__struct_new_default :
		"Instr_const C (instr_sc5 (STRUCT_NEW_DEFAULT x))"
	| Instr_const__array_new :
		"Instr_const C (instr_sc5 (ARRAY_NEW x))"
	| Instr_const__array_new_default :
		"Instr_const C (instr_sc5 (ARRAY_NEW_DEFAULT x))"
	| Instr_const__array_new_fixed :
		"Instr_const C (instr_sc5 (ARRAY_NEW_FIXED x (mk_uN v_n)))"
	| Instr_const__any_convert_extern :
		"Instr_const C (instr_sc6 ANY_CONVERT_EXTERN)"
	| Instr_const__extern_convert_any :
		"Instr_const C (instr_sc6 EXTERN_CONVERT_ANY)"
	| Instr_const__global_get :
		"(wf_globaltype (mk_globaltype None t)) ⟹
		 ((proj_uN_0 x) < (length (context_GLOBALS C))) ⟹
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype None t)) ⟹
		 Instr_const C (instr_sc2 (GLOBAL_GET x))"
	| Instr_const__binop :
		"(wf_binop_underscore (numtype_addrtype v_Inn) (mk_binop__0 v_Inn ADD)) ⟹
		 (wf_binop_underscore (numtype_addrtype v_Inn) (mk_binop__0 v_Inn binop_Inn_SUB)) ⟹
		 (wf_binop_underscore (numtype_addrtype v_Inn) (mk_binop__0 v_Inn MUL)) ⟹
		 (v_Inn ∈ set [I32, I64]) ⟹
		 (binop ∈ set [(mk_binop__0 v_Inn ADD), (mk_binop__0 v_Inn binop_Inn_SUB), (mk_binop__0 v_Inn MUL)]) ⟹
		 Instr_const C (instr_sc6 (BINOP (numtype_addrtype v_Inn) binop))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:650.1-650.103 *)
inductive Expr_const :: "res_context ⇒ expr ⇒ bool" where
	  mk_Expr_const :
		"list_all (λ (v_instr :: instr). (Instr_const C v_instr)) instr_lst ⟹
		 Expr_const C instr_lst"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:651.1-651.105 *)
inductive Expr_ok_const :: "res_context ⇒ expr ⇒ valtype ⇒ bool" where
	  mk_Expr_ok_const :
		"(Expr_ok C v_expr (mk_list [t])) ⟹
		 (Expr_const C v_expr) ⟹
		 Expr_ok_const C v_expr t"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:7.1-7.97 *)
inductive Type_ok :: "res_context ⇒ type ⇒ (deftype list) ⇒ bool" where
	  mk_Type_ok :
		"(fun_rolldt x v_rectype var_0) ⟹
		 (wf_context ⦇ context_TYPES = dt_lst, RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (wf_oktypeidx (oktypeidx_OK x)) ⟹
		 ((proj_uN_0 x) = (length (context_TYPES C))) ⟹
		 (dt_lst = var_0) ⟹
		 (Rectype_ok (append_context C ⦇ context_TYPES = dt_lst, RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) v_rectype (oktypeidx_OK x)) ⟹
		 Type_ok C (res_TYPE v_rectype) dt_lst"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:8.1-8.96 *)
inductive Tag_ok :: "res_context ⇒ tag ⇒ tagtype ⇒ bool" where
	  mk_Tag_ok :
		"(fun_clos_tagtype C v_tagtype var_0) ⟹
		 (Tagtype_ok C v_tagtype) ⟹
		 Tag_ok C (tag_TAG v_tagtype) var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:9.1-9.99 *)
inductive Global_ok :: "res_context ⇒ global ⇒ globaltype ⇒ bool" where
	  mk_Global_ok :
		"(wf_globaltype (mk_globaltype (Some MUT) t)) ⟹
		 (Globaltype_ok C v_globaltype) ⟹
		 (v_globaltype = (mk_globaltype (Some MUT) t)) ⟹
		 (Expr_ok_const C v_expr t) ⟹
		 Global_ok C (global_GLOBAL v_globaltype v_expr) v_globaltype"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:10.1-10.96 *)
inductive Mem_ok :: "res_context ⇒ mem ⇒ memtype ⇒ bool" where
	  mk_Mem_ok :
		"(Memtype_ok C v_memtype) ⟹
		 Mem_ok C (MEMORY v_memtype) v_memtype"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:11.1-11.98 *)
inductive Table_ok :: "res_context ⇒ table ⇒ tabletype ⇒ bool" where
	  mk_Table_ok :
		"(wf_tabletype (mk_tabletype at lim rt)) ⟹
		 (Tabletype_ok C v_tabletype) ⟹
		 (v_tabletype = (mk_tabletype at lim rt)) ⟹
		 (Expr_ok_const C v_expr (valtype_reftype rt)) ⟹
		 Table_ok C (table_TABLE v_tabletype v_expr) v_tabletype"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:18.1-18.98 *)
inductive Local_ok :: "res_context ⇒ local ⇒ localtype ⇒ bool" where
	  res_set :
		"(Defaultable t) ⟹
		 Local_ok C (LOCAL t) (mk_localtype SET t)"
	| unset :
		"(Nondefaultable t) ⟹
		 Local_ok C (LOCAL t) (mk_localtype UNSET t)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:12.1-12.97 *)
inductive Func_ok :: "res_context ⇒ func ⇒ deftype ⇒ bool" where
	  mk_Func_ok :
		"((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = ((map (λ (t_1 :: valtype). (mk_localtype SET t_1)) t_1_lst) @ lct_lst), context_LABELS = [(mk_list t_2_lst)], context_RETURN = (Some (mk_list t_2_lst)), REFS = [] ⦈) ⟹
		 (Expand ((context_TYPES C) ! (proj_uN_0 x)) (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 ((length lct_lst) = (length local_lst)) ⟹
		 list_all2 (λ (lct :: localtype) (v_local :: local). (Local_ok C v_local lct)) lct_lst local_lst ⟹
		 (Expr_ok (append_context C ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = ((map (λ (t_1 :: valtype). (mk_localtype SET t_1)) t_1_lst) @ lct_lst), context_LABELS = [(mk_list t_2_lst)], context_RETURN = (Some (mk_list t_2_lst)), REFS = [] ⦈) v_expr (mk_list t_2_lst)) ⟹
		 Func_ok C (func_FUNC x local_lst v_expr) ((context_TYPES C) ! (proj_uN_0 x))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:15.1-15.118 *)
inductive Datamode_ok :: "res_context ⇒ datamode ⇒ res_datatype ⇒ bool" where
	  res_passive :
		"Datamode_ok C datamode_PASSIVE OK"
	| active :
		"(wf_memtype (PAGE at lim)) ⟹
		 ((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = (PAGE at lim)) ⟹
		 (Expr_ok_const C v_expr (valtype_addrtype at)) ⟹
		 Datamode_ok C (datamode_ACTIVE x v_expr) OK"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:13.1-13.115 *)
inductive Data_ok :: "res_context ⇒ data ⇒ res_datatype ⇒ bool" where
	  mk_Data_ok :
		"(Datamode_ok C v_datamode OK) ⟹
		 Data_ok C (DATA b_lst v_datamode) OK"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:16.1-16.101 *)
inductive Elemmode_ok :: "res_context ⇒ elemmode ⇒ elemtype ⇒ bool" where
	  Elemmode_ok__passive :
		"Elemmode_ok C PASSIVE rt"
	| res_declare :
		"Elemmode_ok C DECLARE rt"
	| Elemmode_ok__active :
		"(wf_tabletype (mk_tabletype at lim rt')) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype at lim rt')) ⟹
		 (Reftype_sub C rt rt') ⟹
		 (Expr_ok_const C v_expr (valtype_addrtype at)) ⟹
		 Elemmode_ok C (ACTIVE x v_expr) rt"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:14.1-14.97 *)
inductive Elem_ok :: "res_context ⇒ elem ⇒ elemtype ⇒ bool" where
	  mk_Elem_ok :
		"(Reftype_ok C v_elemtype) ⟹
		 list_all (λ (v_expr :: expr). (Expr_ok_const C v_expr (valtype_reftype v_elemtype))) expr_lst ⟹
		 (Elemmode_ok C v_elemmode v_elemtype) ⟹
		 Elem_ok C (ELEM v_elemtype expr_lst v_elemmode) v_elemtype"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:17.1-17.98 *)
inductive Start_ok :: "res_context ⇒ start ⇒ bool" where
	  mk_Start_ok :
		"(wf_comptype (comptype_FUNC (mk_list []) (mk_list []))) ⟹
		 ((proj_uN_0 x) < (length (context_FUNCS C))) ⟹
		 (Expand ((context_FUNCS C) ! (proj_uN_0 x)) (comptype_FUNC (mk_list []) (mk_list []))) ⟹
		 Start_ok C (START x)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:98.1-98.105 *)
inductive Import_ok :: "res_context ⇒ import ⇒ externtype ⇒ bool" where
	  mk_Import_ok :
		"(fun_clos_externtype C xt var_0) ⟹
		 (Externtype_ok C xt) ⟹
		 Import_ok C (IMPORT name_1 name_2 xt) var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:100.1-100.108 *)
inductive Externidx_ok :: "res_context ⇒ externidx ⇒ externtype ⇒ bool" where
	  Externidx_ok__tag :
		"((proj_uN_0 x) < (length (context_TAGS C))) ⟹
		 (((context_TAGS C) ! (proj_uN_0 x)) = jt) ⟹
		 Externidx_ok C (TAG x) (externtype_TAG jt)"
	| Externidx_ok__global :
		"((proj_uN_0 x) < (length (context_GLOBALS C))) ⟹
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = gt) ⟹
		 Externidx_ok C (GLOBAL x) (externtype_GLOBAL gt)"
	| Externidx_ok__mem :
		"((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = mt) ⟹
		 Externidx_ok C (MEM x) (externtype_MEM mt)"
	| Externidx_ok__table :
		"((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = tt) ⟹
		 Externidx_ok C (TABLE x) (externtype_TABLE tt)"
	| Externidx_ok__func :
		"((proj_uN_0 x) < (length (context_FUNCS C))) ⟹
		 (((context_FUNCS C) ! (proj_uN_0 x)) = dt) ⟹
		 Externidx_ok C (FUNC x) (externtype_FUNC (typeuse_deftype dt))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:99.1-99.105 *)
inductive Export_ok :: "res_context ⇒ export ⇒ name ⇒ externtype ⇒ bool" where
	  mk_Export_ok :
		"(Externidx_ok C v_externidx xt) ⟹
		 Export_ok C (EXPORT v_name v_externidx) v_name xt"

(* Mutual Recursion at: ../specification/wasm-3.0/2.4-validation.modules.spectec:136.1-136.100 *)
inductive Globals_ok :: "res_context ⇒ (global list) ⇒ (globaltype list) ⇒ bool" where
	  Globals_ok__empty :
		"Globals_ok C [] []"
	| Globals_ok__cons :
		"(wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [gt_1], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (Global_ok C global_1 gt_1) ⟹
		 (Globals_ok (append_context C ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [gt_1], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) global_lst gt_lst) ⟹
		 Globals_ok C ([global_1] @ global_lst) ([gt_1] @ gt_lst)"

(* Mutual Recursion at: ../specification/wasm-3.0/2.4-validation.modules.spectec:135.1-135.98 *)
inductive Types_ok :: "res_context ⇒ (type list) ⇒ (deftype list) ⇒ bool" where
	  Types_ok__empty :
		"Types_ok C [] []"
	| Types_ok__cons :
		"(wf_context ⦇ context_TYPES = dt_1_lst, RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (Type_ok C type_1 dt_1_lst) ⟹
		 (Types_ok (append_context C ⦇ context_TYPES = dt_1_lst, RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) type_lst dt_lst) ⟹
		 Types_ok C ([type_1] @ type_lst) (dt_1_lst @ dt_lst)"

(* Inductive Type Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:139.1-139.44 *)
datatype nonfuncs =
	  mk_nonfuncs "(global list)" "(mem list)" "(table list)" "(elem list)"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:139.8-139.16 *)
inductive wf_nonfuncs :: "nonfuncs ⇒ bool" where
	  nonfuncs_case_0 :
		"list_all (λ (v_global :: global). (wf_global v_global)) global_lst ⟹
		 list_all (λ (v_mem :: mem). (wf_mem v_mem)) mem_lst ⟹
		 list_all (λ (v_table :: table). (wf_table v_table)) table_lst ⟹
		 list_all (λ (v_elem :: elem). (wf_elem v_elem)) elem_lst ⟹
		 wf_nonfuncs (mk_nonfuncs global_lst mem_lst table_lst elem_lst)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:140.6-140.23 *)
inductive fun_funcidx_nonfuncs :: "nonfuncs ⇒ (funcidx list) ⇒ bool" where
	  fun_funcidx_nonfuncs_case_0 :
		"(fun_funcidx_module (module_MODULE [] [] [] global_lst mem_lst table_lst [] [] elem_lst None []) var_0) ⟹
		 fun_funcidx_nonfuncs (mk_nonfuncs global_lst mem_lst table_lst elem_lst) var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:134.1-134.99 *)
inductive Module_ok :: "module ⇒ moduletype ⇒ bool" where
	  mk_Module_ok :
		"(fun_funcsxt xt_I_lst var_6) ⟹
		 (fun_tablesxt xt_I_lst var_5) ⟹
		 (fun_memsxt xt_I_lst var_4) ⟹
		 (fun_globalsxt xt_I_lst var_3) ⟹
		 (fun_tagsxt xt_I_lst var_2) ⟹
		 (fun_funcidx_nonfuncs (mk_nonfuncs global_lst mem_lst table_lst elem_lst) var_1) ⟹
		 (fun_clos_moduletype C (mk_moduletype xt_I_lst xt_E_lst) var_0) ⟹
		 (wf_context C') ⟹
		 list_all (λ (nm :: name). (wf_name nm)) nm_lst ⟹
		 list_all (λ (iter :: funcidx). (wf_uN 32 iter)) var_1 ⟹
		 list_all (λ (iter :: tagtype). (wf_typeuse iter)) var_2 ⟹
		 list_all (λ (iter :: globaltype). (wf_globaltype iter)) var_3 ⟹
		 list_all (λ (iter :: memtype). (wf_memtype iter)) var_4 ⟹
		 list_all (λ (iter :: tabletype). (wf_tabletype iter)) var_5 ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (wf_context ⦇ context_TYPES = dt'_lst, RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = (jt_I_lst @ jt_lst), context_GLOBALS = gt_lst, context_MEMS = (mt_I_lst @ mt_lst), context_TABLES = (tt_I_lst @ tt_lst), context_FUNCS = [], context_DATAS = ok_lst, context_ELEMS = rt_lst, context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (wf_context ⦇ context_TYPES = dt'_lst, RECS = [], context_TAGS = [], context_GLOBALS = gt_I_lst, context_MEMS = [], context_TABLES = [], context_FUNCS = (dt_I_lst @ dt_lst), context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = x_lst ⦈) ⟹
		 (wf_nonfuncs (mk_nonfuncs global_lst mem_lst table_lst elem_lst)) ⟹
		 (Types_ok ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈ type_lst dt'_lst) ⟹
		 ((length import_lst) = (length xt_I_lst)) ⟹
		 list_all2 (λ (v_import :: import) (xt_I :: externtype). (Import_ok ⦇ context_TYPES = dt'_lst, RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈ v_import xt_I)) import_lst xt_I_lst ⟹
		 ((length jt_lst) = (length tag_lst)) ⟹
		 list_all2 (λ (jt :: tagtype) (v_tag :: tag). (Tag_ok C' v_tag jt)) jt_lst tag_lst ⟹
		 (Globals_ok C' global_lst gt_lst) ⟹
		 ((length mem_lst) = (length mt_lst)) ⟹
		 list_all2 (λ (v_mem :: mem) (mt :: memtype). (Mem_ok C' v_mem mt)) mem_lst mt_lst ⟹
		 ((length table_lst) = (length tt_lst)) ⟹
		 list_all2 (λ (v_table :: table) (tt :: tabletype). (Table_ok C' v_table tt)) table_lst tt_lst ⟹
		 ((length dt_lst) = (length func_lst)) ⟹
		 list_all2 (λ (dt :: deftype) (v_func :: func). (Func_ok C v_func dt)) dt_lst func_lst ⟹
		 ((length data_lst) = (length ok_lst)) ⟹
		 list_all2 (λ (v_data :: data) (ok :: res_datatype). (Data_ok C v_data ok)) data_lst ok_lst ⟹
		 ((length elem_lst) = (length rt_lst)) ⟹
		 list_all2 (λ (v_elem :: elem) (rt :: elemtype). (Elem_ok C v_elem rt)) elem_lst rt_lst ⟹
		 list_all (λ (v_start :: start). (Start_ok C v_start)) (option_to_list start_opt) ⟹
		 ((length export_lst) = (length nm_lst)) ⟹
		 ((length export_lst) = (length xt_E_lst)) ⟹
		 list_all3 (λ (v_export :: export) (nm :: name) (xt_E :: externtype). (Export_ok C v_export nm xt_E)) export_lst nm_lst xt_E_lst ⟹
		 (disjoint_underscore  nm_lst) ⟹
		 (C = (append_context C' ⦇ context_TYPES = [], RECS = [], context_TAGS = (jt_I_lst @ jt_lst), context_GLOBALS = gt_lst, context_MEMS = (mt_I_lst @ mt_lst), context_TABLES = (tt_I_lst @ tt_lst), context_FUNCS = [], context_DATAS = ok_lst, context_ELEMS = rt_lst, context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈)) ⟹
		 (C' = ⦇ context_TYPES = dt'_lst, RECS = [], context_TAGS = [], context_GLOBALS = gt_I_lst, context_MEMS = [], context_TABLES = [], context_FUNCS = (dt_I_lst @ dt_lst), context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = x_lst ⦈) ⟹
		 (x_lst = var_1) ⟹
		 (jt_I_lst = var_2) ⟹
		 (gt_I_lst = var_3) ⟹
		 (mt_I_lst = var_4) ⟹
		 (tt_I_lst = var_5) ⟹
		 (dt_I_lst = var_6) ⟹
		 Module_ok (module_MODULE type_lst import_lst tag_lst global_lst mem_lst table_lst func_lst data_lst elem_lst start_opt export_lst) var_0"

(* Inductive Type Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:5.1-5.24 *)
datatype relaxed2 =
	  mk_relaxed2 "nat"
	

(* Auxiliary Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:5.1-5.24 *)
function (sequential) proj_relaxed2_0 :: "relaxed2 ⇒ (nat)" where
		  "proj_relaxed2_0 (mk_relaxed2 v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:5.8-5.16 *)
inductive wf_relaxed2 :: "relaxed2 ⇒ bool" where
	  relaxed2_case_0 :
		"((i = 0) ∨ (i = 1)) ⟹
		 wf_relaxed2 (mk_relaxed2 i)"

(* Inductive Type Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:6.1-6.32 *)
datatype relaxed4 =
	  mk_relaxed4 "nat"
	

(* Auxiliary Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:6.1-6.32 *)
function (sequential) proj_relaxed4_0 :: "relaxed4 ⇒ (nat)" where
		  "proj_relaxed4_0 (mk_relaxed4 v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:6.8-6.16 *)
inductive wf_relaxed4 :: "relaxed4 ⇒ bool" where
	  relaxed4_case_0 :
		"((((i = 0) ∨ (i = 1)) ∨ (i = 2)) ∨ (i = 3)) ⟹
		 wf_relaxed4 (mk_relaxed4 i)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:8.1-8.83 *)
function (sequential) fun_relaxed2 :: "relaxed2 ⇒ 'v_X ⇒ 'v_X ⇒ 'v_X" where
		  "fun_relaxed2 i  X_1 X_2 = (if (ND ) then ([X_1, X_2] ! (proj_relaxed2_0 i)) else ([X_1, X_2] ! 0))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:9.1-9.89 *)
function (sequential) fun_relaxed4 :: "relaxed4 ⇒ 'v_X ⇒ 'v_X ⇒ 'v_X ⇒ 'v_X ⇒ 'v_X" where
		  "fun_relaxed4 i  X_1 X_2 X_3 X_4 = (if (ND ) then ([X_1, X_2, X_3, X_4] ! (proj_relaxed4_0 i)) else ([X_1, X_2, X_3, X_4] ! 0))"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:18.1-18.43 *)
axiomatization R_fmadd :: "relaxed2"

(* Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:19.1-19.43 *)
axiomatization R_fmin :: "relaxed4"

(* Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:20.1-20.43 *)
axiomatization R_fmax :: "relaxed4"

(* Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:21.1-21.43 *)
axiomatization R_idot :: "relaxed2"

(* Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:22.1-22.43 *)
axiomatization R_iq15mulr :: "relaxed2"

(* Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:23.1-23.43 *)
axiomatization R_trunc_u :: "relaxed4"

(* Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:24.1-24.43 *)
axiomatization R_trunc_s :: "relaxed2"

(* Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:25.1-25.43 *)
axiomatization R_swizzle :: "relaxed2"

(* Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:26.1-26.43 *)
axiomatization R_laneselect :: "relaxed2"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:7.1-7.41 *)
axiomatization s33_to_u32 :: "s33 ⇒ u32"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:12.1-12.107 *)
axiomatization ibits_underscore :: "N ⇒ iN ⇒ (bit list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:13.1-13.107 *)
axiomatization fbits_underscore :: "N ⇒ fN ⇒ (bit list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:14.1-14.109 *)
axiomatization ibytes_underscore :: "N ⇒ iN ⇒ (byte list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:15.1-15.109 *)
axiomatization fbytes_underscore :: "N ⇒ fN ⇒ (byte list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:16.1-16.104 *)
axiomatization nbytes_underscore :: "numtype ⇒ num_underscore ⇒ (byte list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:17.1-17.104 *)
axiomatization vbytes_underscore :: "vectype ⇒ vec_underscore ⇒ (byte list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:18.1-18.104 *)
axiomatization zbytes_underscore :: "storagetype ⇒ lit_underscore ⇒ (byte list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:19.1-19.104 *)
axiomatization cbytes_underscore :: "Cnn ⇒ lit_underscore ⇒ (byte list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:21.1-21.91 *)
axiomatization inv_ibits_underscore :: "N ⇒ (bit list) ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:22.1-22.91 *)
axiomatization inv_fbits_underscore :: "N ⇒ (bit list) ⇒ fN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:23.1-23.92 *)
axiomatization inv_ibytes_underscore :: "N ⇒ (byte list) ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:24.1-24.92 *)
axiomatization inv_fbytes_underscore :: "N ⇒ (byte list) ⇒ fN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:25.1-25.87 *)
axiomatization inv_nbytes_underscore :: "numtype ⇒ (byte list) ⇒ num_underscore"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:26.1-26.87 *)
axiomatization inv_vbytes_underscore :: "vectype ⇒ (byte list) ⇒ vec_underscore"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:27.1-27.92 *)
axiomatization inv_zbytes_underscore :: "storagetype ⇒ (byte list) ⇒ lit_underscore"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:28.1-28.87 *)
axiomatization inv_cbytes_underscore :: "Cnn ⇒ (byte list) ⇒ lit_underscore"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:52.6-52.14 *)
inductive fun_signed_underscore :: "N ⇒ nat ⇒ nat ⇒ bool" where
	  fun_signed__case_0 :
		"(i < (2 ^ (((v_N :: nat) - (1 :: nat)) :: nat))) ⟹
		 fun_signed_underscore v_N i (i :: nat)"
	| fun_signed__case_1 :
		"(((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) ≤ i) ∧ (i < (2 ^ v_N))) ⟹
		 fun_signed_underscore v_N i ((i :: nat) - ((2 ^ v_N) :: nat))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:56.6-56.18 *)
inductive fun_inv_signed_underscore :: "N ⇒ nat ⇒ nat ⇒ bool" where
	  fun_inv_signed__case_0 :
		"(((0 :: nat) ≤ i) ∧ (i < ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat))) ⟹
		 fun_inv_signed_underscore v_N i (i :: nat)"
	| fun_inv_signed__case_1 :
		"(((0 - ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat)) ≤ i) ∧ (i < (0 :: nat))) ⟹
		 fun_inv_signed_underscore v_N i ((i + ((2 ^ v_N) :: nat)) :: nat)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:61.1-61.60 *)
function (sequential) fun_sx :: "storagetype ⇒ ((sx option) option)" where
		  "fun_sx storagetype_I32 = (Some None)"
		| "fun_sx storagetype_I64 = (Some None)"
		| "fun_sx storagetype_F32 = (Some None)"
		| "fun_sx storagetype_F64 = (Some None)"
		| "fun_sx storagetype_V128 = (Some None)"
		| "fun_sx I8 = (Some (Some S))"
		| "fun_sx I16 = (Some (Some S))"
		| "fun_sx x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:68.1-68.51 *)
function (sequential) fun_zero :: "lanetype ⇒ lane_underscore" where
		  "fun_zero lanetype_I32 = (mk_lane__2 Jnn_I32 (mk_uN 0))"
		| "fun_zero lanetype_I64 = (mk_lane__2 Jnn_I64 (mk_uN 0))"
		| "fun_zero lanetype_I8 = (mk_lane__2 Jnn_I8 (mk_uN 0))"
		| "fun_zero lanetype_I16 = (mk_lane__2 Jnn_I16 (mk_uN 0))"
		| "fun_zero lanetype_F32 = (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 (fzero (size (numtype_Fnn Fnn_F32)))))"
		| "fun_zero lanetype_F64 = (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 (fzero (size (numtype_Fnn Fnn_F64)))))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:72.1-72.22 *)
function (sequential) res_bool :: "bool ⇒ nat" where
		  "res_bool False = 0"
		| "res_bool True = 1"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:76.1-76.23 *)
axiomatization truncz :: "nat ⇒ nat"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:80.1-80.59 *)
axiomatization ceilz :: "nat ⇒ nat"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:87.1-87.61 *)
function (sequential) sat_u_underscore :: "N ⇒ nat ⇒ nat" where
		  "sat_u_underscore v_N i = (if (i < (0 :: nat)) then 0 else (if (i > (((2 ^ v_N) :: nat) - (1 :: nat))) then ((((2 ^ v_N) :: nat) - (1 :: nat)) :: nat) else (i :: nat)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:92.1-92.61 *)
function (sequential) sat_s_underscore :: "N ⇒ nat ⇒ nat" where
		  "sat_s_underscore v_N i = (if (i < (0 - ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat))) then (0 - ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat)) else (if (i > (((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat) - (1 :: nat))) then (((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat) - (1 :: nat)) else i))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:100.1-100.29 *)
function (sequential) ineg_underscore :: "N ⇒ iN ⇒ iN" where
		  "ineg_underscore v_N i_1 = (mk_uN (((((2 ^ v_N) :: nat) - ((proj_uN_0 i_1) :: nat)) mod ((2 ^ v_N) :: nat)) :: nat))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:101.1-101.29 *)
axiomatization iabs_underscore :: "N ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:102.1-102.29 *)
axiomatization iclz_underscore :: "N ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:103.1-103.29 *)
axiomatization ictz_underscore :: "N ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:104.1-104.32 *)
axiomatization ipopcnt_underscore :: "N ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:105.6-105.15 *)
inductive fun_iextend_underscore :: "N ⇒ M ⇒ sx ⇒ iN ⇒ iN ⇒ bool" where
	  fun_iextend__case_0 :
		"fun_iextend_underscore v_N v_M U i (mk_uN ((proj_uN_0 i) mod (2 ^ v_M)))"
	| fun_iextend__case_1 :
		"(fun_signed_underscore v_M ((proj_uN_0 i) mod (2 ^ v_M)) var_1) ⟹
		 (fun_inv_signed_underscore v_N var_1 var_0) ⟹
		 fun_iextend_underscore v_N v_M S i (mk_uN var_0)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:107.1-107.36 *)
function (sequential) iadd_underscore :: "N ⇒ iN ⇒ iN ⇒ iN" where
		  "iadd_underscore v_N i_1 i_2 = (mk_uN (((proj_uN_0 i_1) + (proj_uN_0 i_2)) mod (2 ^ v_N)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:108.1-108.36 *)
function (sequential) isub_underscore :: "N ⇒ iN ⇒ iN ⇒ iN" where
		  "isub_underscore v_N i_1 i_2 = (mk_uN ((((((2 ^ v_N) + (proj_uN_0 i_1)) :: nat) - ((proj_uN_0 i_2) :: nat)) mod ((2 ^ v_N) :: nat)) :: nat))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:109.1-109.36 *)
function (sequential) imul_underscore :: "N ⇒ iN ⇒ iN ⇒ iN" where
		  "imul_underscore v_N i_1 i_2 = (mk_uN (((proj_uN_0 i_1) * (proj_uN_0 i_2)) mod (2 ^ v_N)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:110.6-110.12 *)
inductive fun_idiv_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ (iN option) ⇒ bool" where
	  fun_idiv__case_0 :
		"fun_idiv_underscore v_N U i_1 (mk_uN 0) None"
	| fun_idiv__case_1 :
		"fun_idiv_underscore v_N U i_1 i_2 (Some (mk_uN ((truncz (((proj_uN_0 i_1) :: nat) div ((proj_uN_0 i_2) :: nat))) :: nat)))"
	| fun_idiv__case_2 :
		"fun_idiv_underscore v_N S i_1 (mk_uN 0) None"
	| fun_idiv__case_3 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) ⟹
		 (((var_0 :: nat) div (var_1 :: nat)) = ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat)) ⟹
		 fun_idiv_underscore v_N S i_1 i_2 None"
	| fun_idiv__case_4 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_2) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_1) ⟹
		 (fun_inv_signed_underscore v_N (truncz ((var_1 :: nat) div (var_2 :: nat))) var_0) ⟹
		 fun_idiv_underscore v_N S i_1 i_2 (Some (mk_uN var_0))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:111.6-111.12 *)
inductive fun_irem_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ (iN option) ⇒ bool" where
	  fun_irem__case_0 :
		"fun_irem_underscore v_N U i_1 (mk_uN 0) None"
	| fun_irem__case_1 :
		"fun_irem_underscore v_N U i_1 i_2 (Some (mk_uN ((((proj_uN_0 i_1) :: nat) - (((proj_uN_0 i_2) * ((truncz (((proj_uN_0 i_1) :: nat) div ((proj_uN_0 i_2) :: nat))) :: nat)) :: nat)) :: nat)))"
	| fun_irem__case_2 :
		"fun_irem_underscore v_N S i_1 (mk_uN 0) None"
	| fun_irem__case_3 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_2) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_1) ⟹
		 (fun_inv_signed_underscore v_N (j_1 - (j_2 * (truncz ((j_1 :: nat) div (j_2 :: nat))))) var_0) ⟹
		 ((j_1 = var_1) ∧ (j_2 = var_2)) ⟹
		 fun_irem_underscore v_N S i_1 i_2 (Some (mk_uN var_0))"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:112.1-112.83 *)
axiomatization imin_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ iN"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:113.1-113.83 *)
axiomatization imax_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ iN"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:114.1-114.88 *)
axiomatization iadd_sat_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ iN"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:115.1-115.88 *)
axiomatization isub_sat_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:116.1-116.92 *)
axiomatization iq15mulr_sat_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:117.1-117.101 *)
axiomatization irelaxed_q15mulr_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ (iN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:118.1-118.84 *)
axiomatization iavgr_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:120.1-120.29 *)
axiomatization inot_underscore :: "N ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:121.1-121.29 *)
axiomatization irev_underscore :: "N ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:122.1-122.36 *)
axiomatization iand_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:123.1-123.39 *)
axiomatization iandnot_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:124.1-124.35 *)
axiomatization ior_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:125.1-125.36 *)
axiomatization ixor_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:126.1-126.34 *)
axiomatization ishl_underscore :: "N ⇒ iN ⇒ u32 ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:127.1-127.76 *)
axiomatization ishr_underscore :: "N ⇒ sx ⇒ iN ⇒ u32 ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:128.1-128.37 *)
axiomatization irotl_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:129.1-129.37 *)
axiomatization irotr_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:131.1-131.49 *)
axiomatization ibitselect_underscore :: "N ⇒ iN ⇒ iN ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:132.1-132.59 *)
axiomatization irelaxed_laneselect_underscore :: "N ⇒ iN ⇒ iN ⇒ iN ⇒ (iN list)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:134.1-134.27 *)
function (sequential) ieqz_underscore :: "N ⇒ iN ⇒ u32" where
		  "ieqz_underscore v_N i_1 = (mk_uN (res_bool ((proj_uN_0 i_1) = 0)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:135.1-135.27 *)
function (sequential) inez_underscore :: "N ⇒ iN ⇒ u32" where
		  "inez_underscore v_N i_1 = (mk_uN (res_bool ((proj_uN_0 i_1) ≠ 0)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:137.1-137.33 *)
function (sequential) ieq_underscore :: "N ⇒ iN ⇒ iN ⇒ u32" where
		  "ieq_underscore v_N i_1 i_2 = (mk_uN (res_bool (i_1 = i_2)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:138.1-138.33 *)
function (sequential) ine_underscore :: "N ⇒ iN ⇒ iN ⇒ u32" where
		  "ine_underscore v_N i_1 i_2 = (mk_uN (res_bool (i_1 ≠ i_2)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:139.1-139.75 *)
axiomatization ilt_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ u32"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:140.1-140.75 *)
axiomatization igt_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ u32"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:141.1-141.75 *)
axiomatization ile_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ u32"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:142.1-142.75 *)
axiomatization ige_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ u32"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:242.1-242.30 *)
axiomatization fabs_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:243.1-243.30 *)
axiomatization fneg_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:244.1-244.31 *)
axiomatization fsqrt_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:245.1-245.31 *)
axiomatization fceil_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:246.1-246.32 *)
axiomatization ffloor_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:247.1-247.32 *)
axiomatization ftrunc_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:248.1-248.34 *)
axiomatization fnearest_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:250.1-250.37 *)
axiomatization fadd_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:251.1-251.37 *)
axiomatization fsub_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:252.1-252.37 *)
axiomatization fmul_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:253.1-253.37 *)
axiomatization fdiv_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:254.1-254.37 *)
axiomatization fmin_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:255.1-255.37 *)
axiomatization fmax_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:256.1-256.38 *)
axiomatization fpmin_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:257.1-257.38 *)
axiomatization fpmax_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:258.1-258.82 *)
axiomatization frelaxed_min_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:259.1-259.82 *)
axiomatization frelaxed_max_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:260.1-260.42 *)
axiomatization fcopysign_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:262.1-262.33 *)
axiomatization feq_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:263.1-263.33 *)
axiomatization fne_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:264.1-264.33 *)
axiomatization flt_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:265.1-265.33 *)
axiomatization fgt_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:266.1-266.33 *)
axiomatization fle_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:267.1-267.33 *)
axiomatization fge_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:269.1-269.91 *)
axiomatization frelaxed_madd_underscore :: "N ⇒ fN ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:270.1-270.92 *)
axiomatization frelaxed_nmadd_underscore :: "N ⇒ fN ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:308.1-308.33 *)
axiomatization wrap__underscore :: "M ⇒ N ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:309.1-309.90 *)
axiomatization extend__underscore :: "M ⇒ N ⇒ sx ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:310.1-310.89 *)
axiomatization trunc__underscore :: "M ⇒ N ⇒ sx ⇒ fN ⇒ (iN option)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:311.1-311.94 *)
axiomatization trunc_sat__underscore :: "M ⇒ N ⇒ sx ⇒ fN ⇒ (iN option)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:312.1-312.98 *)
axiomatization relaxed_trunc__underscore :: "M ⇒ N ⇒ sx ⇒ fN ⇒ (iN option)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:313.1-313.36 *)
axiomatization demote__underscore :: "M ⇒ N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:314.1-314.37 *)
axiomatization promote__underscore :: "M ⇒ N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:315.1-315.91 *)
axiomatization convert__underscore :: "M ⇒ N ⇒ sx ⇒ iN ⇒ fN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:316.1-316.88 *)
axiomatization narrow__underscore :: "M ⇒ N ⇒ sx ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:318.1-318.76 *)
axiomatization reinterpret__underscore :: "numtype ⇒ numtype ⇒ num_underscore ⇒ num_underscore"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:338.1-339.49 *)
function (sequential) lpacknum_underscore :: "lanetype ⇒ num_underscore ⇒ lane_underscore" where
		  "lpacknum_underscore lanetype_I32 c = (mk_lane__0 numtype_I32 c)"
		| "lpacknum_underscore lanetype_I64 c = (mk_lane__0 numtype_I64 c)"
		| "lpacknum_underscore lanetype_F32 c = (mk_lane__0 F32 c)"
		| "lpacknum_underscore lanetype_F64 c = (mk_lane__0 F64 c)"
		| "lpacknum_underscore lanetype_I8 (mk_num__0 I32 c) = (mk_lane__1 packtype_I8 (wrap__underscore (size (lunpack (lanetype_packtype packtype_I8))) (psize packtype_I8) c))"
		| "lpacknum_underscore lanetype_I16 (mk_num__0 I32 c) = (mk_lane__1 packtype_I16 (wrap__underscore (size (lunpack (lanetype_packtype packtype_I16))) (psize packtype_I16) c))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:340.1-341.49 *)
function (sequential) cpacknum_underscore :: "storagetype ⇒ lit_underscore ⇒ lit_underscore" where
		  "cpacknum_underscore storagetype_I32 c = c"
		| "cpacknum_underscore storagetype_I64 c = c"
		| "cpacknum_underscore storagetype_F32 c = c"
		| "cpacknum_underscore storagetype_F64 c = c"
		| "cpacknum_underscore storagetype_V128 c = c"
		| "cpacknum_underscore I8 (mk_lit__0 numtype_I32 (mk_num__0 I32 c)) = (mk_lit__2 packtype_I8 (wrap__underscore (size (lunpack (lanetype_packtype packtype_I8))) (psize packtype_I8) c))"
		| "cpacknum_underscore I16 (mk_lit__0 numtype_I32 (mk_num__0 I32 c)) = (mk_lit__2 packtype_I16 (wrap__underscore (size (lunpack (lanetype_packtype packtype_I16))) (psize packtype_I16) c))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:350.1-351.53 *)
function (sequential) lunpacknum_underscore :: "lanetype ⇒ lane_underscore ⇒ num_underscore" where
		  "lunpacknum_underscore lanetype_I32 (mk_lane__0 numtype_I32 c) = c"
		| "lunpacknum_underscore lanetype_I64 (mk_lane__0 numtype_I64 c) = c"
		| "lunpacknum_underscore lanetype_F32 (mk_lane__0 F32 c) = c"
		| "lunpacknum_underscore lanetype_F64 (mk_lane__0 F64 c) = c"
		| "lunpacknum_underscore lanetype_I8 (mk_lane__1 packtype_I8 c) = (mk_num__0 I32 (extend__underscore (psize packtype_I8) (size (lunpack (lanetype_packtype packtype_I8))) U c))"
		| "lunpacknum_underscore lanetype_I16 (mk_lane__1 packtype_I16 c) = (mk_num__0 I32 (extend__underscore (psize packtype_I16) (size (lunpack (lanetype_packtype packtype_I16))) U c))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:352.1-353.53 *)
function (sequential) cunpacknum_underscore :: "storagetype ⇒ lit_underscore ⇒ lit_underscore" where
		  "cunpacknum_underscore storagetype_I32 c = c"
		| "cunpacknum_underscore storagetype_I64 c = c"
		| "cunpacknum_underscore storagetype_F32 c = c"
		| "cunpacknum_underscore storagetype_F64 c = c"
		| "cunpacknum_underscore storagetype_V128 c = c"
		| "cunpacknum_underscore I8 (mk_lit__2 packtype_I8 c) = (mk_lit__0 numtype_I32 (mk_num__0 I32 (extend__underscore (psize packtype_I8) (size (lunpack (lanetype_packtype packtype_I8))) U c)))"
		| "cunpacknum_underscore I16 (mk_lit__2 packtype_I16 c) = (mk_lit__0 numtype_I32 (mk_num__0 I32 (extend__underscore (psize packtype_I16) (size (lunpack (lanetype_packtype packtype_I16))) U c)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:364.6-364.12 *)
inductive fun_unop_underscore :: "numtype ⇒ unop_underscore ⇒ num_underscore ⇒ (num_underscore list) ⇒ bool" where
	  fun_unop__case_0 :
		"fun_unop_underscore numtype_I32 (mk_unop__0 I32 CLZ) (mk_num__0 I32 i) [(mk_num__0 I32 (iclz_underscore (sizenn (numtype_addrtype I32)) i))]"
	| fun_unop__case_1 :
		"fun_unop_underscore numtype_I64 (mk_unop__0 I64 CLZ) (mk_num__0 I64 i) [(mk_num__0 I64 (iclz_underscore (sizenn (numtype_addrtype I64)) i))]"
	| fun_unop__case_2 :
		"fun_unop_underscore numtype_I32 (mk_unop__0 I32 CTZ) (mk_num__0 I32 i) [(mk_num__0 I32 (ictz_underscore (sizenn (numtype_addrtype I32)) i))]"
	| fun_unop__case_3 :
		"fun_unop_underscore numtype_I64 (mk_unop__0 I64 CTZ) (mk_num__0 I64 i) [(mk_num__0 I64 (ictz_underscore (sizenn (numtype_addrtype I64)) i))]"
	| fun_unop__case_4 :
		"fun_unop_underscore numtype_I32 (mk_unop__0 I32 POPCNT) (mk_num__0 I32 i) [(mk_num__0 I32 (ipopcnt_underscore (sizenn (numtype_addrtype I32)) i))]"
	| fun_unop__case_5 :
		"fun_unop_underscore numtype_I64 (mk_unop__0 I64 POPCNT) (mk_num__0 I64 i) [(mk_num__0 I64 (ipopcnt_underscore (sizenn (numtype_addrtype I64)) i))]"
	| fun_unop__case_6 :
		"(fun_iextend_underscore (sizenn (numtype_addrtype I32)) v_M S i var_0) ⟹
		 fun_unop_underscore numtype_I32 (mk_unop__0 I32 (EXTEND (mk_sz v_M))) (mk_num__0 I32 i) [(mk_num__0 I32 var_0)]"
	| fun_unop__case_7 :
		"(fun_iextend_underscore (sizenn (numtype_addrtype I64)) v_M S i var_0) ⟹
		 fun_unop_underscore numtype_I64 (mk_unop__0 I64 (EXTEND (mk_sz v_M))) (mk_num__0 I64 i) [(mk_num__0 I64 var_0)]"
	| fun_unop__case_8 :
		"fun_unop_underscore F32 (mk_unop__1 Fnn_F32 ABS) (mk_num__1 Fnn_F32 f) (map (λ (iter_0_1 :: fN). (mk_num__1 Fnn_F32 iter_0_1)) (fabs_underscore (sizenn (numtype_Fnn Fnn_F32)) f))"
	| fun_unop__case_9 :
		"fun_unop_underscore F64 (mk_unop__1 Fnn_F64 ABS) (mk_num__1 Fnn_F64 f) (map (λ (iter_0_2 :: fN). (mk_num__1 Fnn_F64 iter_0_2)) (fabs_underscore (sizenn (numtype_Fnn Fnn_F64)) f))"
	| fun_unop__case_10 :
		"fun_unop_underscore F32 (mk_unop__1 Fnn_F32 unop_Fnn_NEG) (mk_num__1 Fnn_F32 f) (map (λ (iter_0_3 :: fN). (mk_num__1 Fnn_F32 iter_0_3)) (fneg_underscore (sizenn (numtype_Fnn Fnn_F32)) f))"
	| fun_unop__case_11 :
		"fun_unop_underscore F64 (mk_unop__1 Fnn_F64 unop_Fnn_NEG) (mk_num__1 Fnn_F64 f) (map (λ (iter_0_4 :: fN). (mk_num__1 Fnn_F64 iter_0_4)) (fneg_underscore (sizenn (numtype_Fnn Fnn_F64)) f))"
	| fun_unop__case_12 :
		"fun_unop_underscore F32 (mk_unop__1 Fnn_F32 SQRT) (mk_num__1 Fnn_F32 f) (map (λ (iter_0_5 :: fN). (mk_num__1 Fnn_F32 iter_0_5)) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F32)) f))"
	| fun_unop__case_13 :
		"fun_unop_underscore F64 (mk_unop__1 Fnn_F64 SQRT) (mk_num__1 Fnn_F64 f) (map (λ (iter_0_6 :: fN). (mk_num__1 Fnn_F64 iter_0_6)) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F64)) f))"
	| fun_unop__case_14 :
		"fun_unop_underscore F32 (mk_unop__1 Fnn_F32 CEIL) (mk_num__1 Fnn_F32 f) (map (λ (iter_0_7 :: fN). (mk_num__1 Fnn_F32 iter_0_7)) (fceil_underscore (sizenn (numtype_Fnn Fnn_F32)) f))"
	| fun_unop__case_15 :
		"fun_unop_underscore F64 (mk_unop__1 Fnn_F64 CEIL) (mk_num__1 Fnn_F64 f) (map (λ (iter_0_8 :: fN). (mk_num__1 Fnn_F64 iter_0_8)) (fceil_underscore (sizenn (numtype_Fnn Fnn_F64)) f))"
	| fun_unop__case_16 :
		"fun_unop_underscore F32 (mk_unop__1 Fnn_F32 FLOOR) (mk_num__1 Fnn_F32 f) (map (λ (iter_0_9 :: fN). (mk_num__1 Fnn_F32 iter_0_9)) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F32)) f))"
	| fun_unop__case_17 :
		"fun_unop_underscore F64 (mk_unop__1 Fnn_F64 FLOOR) (mk_num__1 Fnn_F64 f) (map (λ (iter_0_10 :: fN). (mk_num__1 Fnn_F64 iter_0_10)) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F64)) f))"
	| fun_unop__case_18 :
		"fun_unop_underscore F32 (mk_unop__1 Fnn_F32 TRUNC) (mk_num__1 Fnn_F32 f) (map (λ (iter_0_11 :: fN). (mk_num__1 Fnn_F32 iter_0_11)) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F32)) f))"
	| fun_unop__case_19 :
		"fun_unop_underscore F64 (mk_unop__1 Fnn_F64 TRUNC) (mk_num__1 Fnn_F64 f) (map (λ (iter_0_12 :: fN). (mk_num__1 Fnn_F64 iter_0_12)) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F64)) f))"
	| fun_unop__case_20 :
		"fun_unop_underscore F32 (mk_unop__1 Fnn_F32 NEAREST) (mk_num__1 Fnn_F32 f) (map (λ (iter_0_13 :: fN). (mk_num__1 Fnn_F32 iter_0_13)) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F32)) f))"
	| fun_unop__case_21 :
		"fun_unop_underscore F64 (mk_unop__1 Fnn_F64 NEAREST) (mk_num__1 Fnn_F64 f) (map (λ (iter_0_14 :: fN). (mk_num__1 Fnn_F64 iter_0_14)) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F64)) f))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:366.6-366.13 *)
inductive fun_binop_underscore :: "numtype ⇒ binop_underscore ⇒ num_underscore ⇒ num_underscore ⇒ (num_underscore list) ⇒ bool" where
	  fun_binop__case_0 :
		"fun_binop_underscore numtype_I32 (mk_binop__0 I32 ADD) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) [(mk_num__0 I32 (iadd_underscore (sizenn (numtype_addrtype I32)) i_1 i_2))]"
	| fun_binop__case_1 :
		"fun_binop_underscore numtype_I64 (mk_binop__0 I64 ADD) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) [(mk_num__0 I64 (iadd_underscore (sizenn (numtype_addrtype I64)) i_1 i_2))]"
	| fun_binop__case_2 :
		"fun_binop_underscore numtype_I32 (mk_binop__0 I32 binop_Inn_SUB) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) [(mk_num__0 I32 (isub_underscore (sizenn (numtype_addrtype I32)) i_1 i_2))]"
	| fun_binop__case_3 :
		"fun_binop_underscore numtype_I64 (mk_binop__0 I64 binop_Inn_SUB) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) [(mk_num__0 I64 (isub_underscore (sizenn (numtype_addrtype I64)) i_1 i_2))]"
	| fun_binop__case_4 :
		"fun_binop_underscore numtype_I32 (mk_binop__0 I32 MUL) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) [(mk_num__0 I32 (imul_underscore (sizenn (numtype_addrtype I32)) i_1 i_2))]"
	| fun_binop__case_5 :
		"fun_binop_underscore numtype_I64 (mk_binop__0 I64 MUL) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) [(mk_num__0 I64 (imul_underscore (sizenn (numtype_addrtype I64)) i_1 i_2))]"
	| fun_binop__case_6 :
		"(fun_idiv_underscore (sizenn (numtype_addrtype I32)) v_sx i_1 i_2 var_0) ⟹
		 fun_binop_underscore numtype_I32 (mk_binop__0 I32 (DIV v_sx)) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) (map (λ (iter_0_15 :: iN). (mk_num__0 I32 iter_0_15)) (option_to_list var_0))"
	| fun_binop__case_7 :
		"(fun_idiv_underscore (sizenn (numtype_addrtype I64)) v_sx i_1 i_2 var_0) ⟹
		 fun_binop_underscore numtype_I64 (mk_binop__0 I64 (DIV v_sx)) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) (map (λ (iter_0_16 :: iN). (mk_num__0 I64 iter_0_16)) (option_to_list var_0))"
	| fun_binop__case_8 :
		"(fun_irem_underscore (sizenn (numtype_addrtype I32)) v_sx i_1 i_2 var_0) ⟹
		 fun_binop_underscore numtype_I32 (mk_binop__0 I32 (REM v_sx)) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) (map (λ (iter_0_17 :: iN). (mk_num__0 I32 iter_0_17)) (option_to_list var_0))"
	| fun_binop__case_9 :
		"(fun_irem_underscore (sizenn (numtype_addrtype I64)) v_sx i_1 i_2 var_0) ⟹
		 fun_binop_underscore numtype_I64 (mk_binop__0 I64 (REM v_sx)) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) (map (λ (iter_0_18 :: iN). (mk_num__0 I64 iter_0_18)) (option_to_list var_0))"
	| fun_binop__case_10 :
		"fun_binop_underscore numtype_I32 (mk_binop__0 I32 AND) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) [(mk_num__0 I32 (iand_underscore (sizenn (numtype_addrtype I32)) i_1 i_2))]"
	| fun_binop__case_11 :
		"fun_binop_underscore numtype_I64 (mk_binop__0 I64 AND) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) [(mk_num__0 I64 (iand_underscore (sizenn (numtype_addrtype I64)) i_1 i_2))]"
	| fun_binop__case_12 :
		"fun_binop_underscore numtype_I32 (mk_binop__0 I32 OR) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) [(mk_num__0 I32 (ior_underscore (sizenn (numtype_addrtype I32)) i_1 i_2))]"
	| fun_binop__case_13 :
		"fun_binop_underscore numtype_I64 (mk_binop__0 I64 OR) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) [(mk_num__0 I64 (ior_underscore (sizenn (numtype_addrtype I64)) i_1 i_2))]"
	| fun_binop__case_14 :
		"fun_binop_underscore numtype_I32 (mk_binop__0 I32 XOR) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) [(mk_num__0 I32 (ixor_underscore (sizenn (numtype_addrtype I32)) i_1 i_2))]"
	| fun_binop__case_15 :
		"fun_binop_underscore numtype_I64 (mk_binop__0 I64 XOR) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) [(mk_num__0 I64 (ixor_underscore (sizenn (numtype_addrtype I64)) i_1 i_2))]"
	| fun_binop__case_16 :
		"fun_binop_underscore numtype_I32 (mk_binop__0 I32 SHL) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) [(mk_num__0 I32 (ishl_underscore (sizenn (numtype_addrtype I32)) i_1 (mk_uN (proj_uN_0 i_2))))]"
	| fun_binop__case_17 :
		"fun_binop_underscore numtype_I64 (mk_binop__0 I64 SHL) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) [(mk_num__0 I64 (ishl_underscore (sizenn (numtype_addrtype I64)) i_1 (mk_uN (proj_uN_0 i_2))))]"
	| fun_binop__case_18 :
		"fun_binop_underscore numtype_I32 (mk_binop__0 I32 (SHR v_sx)) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) [(mk_num__0 I32 (ishr_underscore (sizenn (numtype_addrtype I32)) v_sx i_1 (mk_uN (proj_uN_0 i_2))))]"
	| fun_binop__case_19 :
		"fun_binop_underscore numtype_I64 (mk_binop__0 I64 (SHR v_sx)) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) [(mk_num__0 I64 (ishr_underscore (sizenn (numtype_addrtype I64)) v_sx i_1 (mk_uN (proj_uN_0 i_2))))]"
	| fun_binop__case_20 :
		"fun_binop_underscore numtype_I32 (mk_binop__0 I32 ROTL) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) [(mk_num__0 I32 (irotl_underscore (sizenn (numtype_addrtype I32)) i_1 i_2))]"
	| fun_binop__case_21 :
		"fun_binop_underscore numtype_I64 (mk_binop__0 I64 ROTL) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) [(mk_num__0 I64 (irotl_underscore (sizenn (numtype_addrtype I64)) i_1 i_2))]"
	| fun_binop__case_22 :
		"fun_binop_underscore numtype_I32 (mk_binop__0 I32 ROTR) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) [(mk_num__0 I32 (irotr_underscore (sizenn (numtype_addrtype I32)) i_1 i_2))]"
	| fun_binop__case_23 :
		"fun_binop_underscore numtype_I64 (mk_binop__0 I64 ROTR) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) [(mk_num__0 I64 (irotr_underscore (sizenn (numtype_addrtype I64)) i_1 i_2))]"
	| fun_binop__case_24 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_ADD) (mk_num__1 Fnn_F32 f_1) (mk_num__1 Fnn_F32 f_2) (map (λ (iter_0_19 :: fN). (mk_num__1 Fnn_F32 iter_0_19)) (fadd_underscore (sizenn (numtype_Fnn Fnn_F32)) f_1 f_2))"
	| fun_binop__case_25 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_ADD) (mk_num__1 Fnn_F64 f_1) (mk_num__1 Fnn_F64 f_2) (map (λ (iter_0_20 :: fN). (mk_num__1 Fnn_F64 iter_0_20)) (fadd_underscore (sizenn (numtype_Fnn Fnn_F64)) f_1 f_2))"
	| fun_binop__case_26 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_SUB) (mk_num__1 Fnn_F32 f_1) (mk_num__1 Fnn_F32 f_2) (map (λ (iter_0_21 :: fN). (mk_num__1 Fnn_F32 iter_0_21)) (fsub_underscore (sizenn (numtype_Fnn Fnn_F32)) f_1 f_2))"
	| fun_binop__case_27 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_SUB) (mk_num__1 Fnn_F64 f_1) (mk_num__1 Fnn_F64 f_2) (map (λ (iter_0_22 :: fN). (mk_num__1 Fnn_F64 iter_0_22)) (fsub_underscore (sizenn (numtype_Fnn Fnn_F64)) f_1 f_2))"
	| fun_binop__case_28 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_MUL) (mk_num__1 Fnn_F32 f_1) (mk_num__1 Fnn_F32 f_2) (map (λ (iter_0_23 :: fN). (mk_num__1 Fnn_F32 iter_0_23)) (fmul_underscore (sizenn (numtype_Fnn Fnn_F32)) f_1 f_2))"
	| fun_binop__case_29 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_MUL) (mk_num__1 Fnn_F64 f_1) (mk_num__1 Fnn_F64 f_2) (map (λ (iter_0_24 :: fN). (mk_num__1 Fnn_F64 iter_0_24)) (fmul_underscore (sizenn (numtype_Fnn Fnn_F64)) f_1 f_2))"
	| fun_binop__case_30 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_DIV) (mk_num__1 Fnn_F32 f_1) (mk_num__1 Fnn_F32 f_2) (map (λ (iter_0_25 :: fN). (mk_num__1 Fnn_F32 iter_0_25)) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F32)) f_1 f_2))"
	| fun_binop__case_31 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_DIV) (mk_num__1 Fnn_F64 f_1) (mk_num__1 Fnn_F64 f_2) (map (λ (iter_0_26 :: fN). (mk_num__1 Fnn_F64 iter_0_26)) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F64)) f_1 f_2))"
	| fun_binop__case_32 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 res_MIN) (mk_num__1 Fnn_F32 f_1) (mk_num__1 Fnn_F32 f_2) (map (λ (iter_0_27 :: fN). (mk_num__1 Fnn_F32 iter_0_27)) (fmin_underscore (sizenn (numtype_Fnn Fnn_F32)) f_1 f_2))"
	| fun_binop__case_33 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 res_MIN) (mk_num__1 Fnn_F64 f_1) (mk_num__1 Fnn_F64 f_2) (map (λ (iter_0_28 :: fN). (mk_num__1 Fnn_F64 iter_0_28)) (fmin_underscore (sizenn (numtype_Fnn Fnn_F64)) f_1 f_2))"
	| fun_binop__case_34 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 res_MAX) (mk_num__1 Fnn_F32 f_1) (mk_num__1 Fnn_F32 f_2) (map (λ (iter_0_29 :: fN). (mk_num__1 Fnn_F32 iter_0_29)) (fmax_underscore (sizenn (numtype_Fnn Fnn_F32)) f_1 f_2))"
	| fun_binop__case_35 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 res_MAX) (mk_num__1 Fnn_F64 f_1) (mk_num__1 Fnn_F64 f_2) (map (λ (iter_0_30 :: fN). (mk_num__1 Fnn_F64 iter_0_30)) (fmax_underscore (sizenn (numtype_Fnn Fnn_F64)) f_1 f_2))"
	| fun_binop__case_36 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 COPYSIGN) (mk_num__1 Fnn_F32 f_1) (mk_num__1 Fnn_F32 f_2) (map (λ (iter_0_31 :: fN). (mk_num__1 Fnn_F32 iter_0_31)) (fcopysign_underscore (sizenn (numtype_Fnn Fnn_F32)) f_1 f_2))"
	| fun_binop__case_37 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 COPYSIGN) (mk_num__1 Fnn_F64 f_1) (mk_num__1 Fnn_F64 f_2) (map (λ (iter_0_32 :: fN). (mk_num__1 Fnn_F64 iter_0_32)) (fcopysign_underscore (sizenn (numtype_Fnn Fnn_F64)) f_1 f_2))"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:368.1-369.28 *)
function (sequential) fun_testop_underscore :: "numtype ⇒ testop_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_testop_underscore numtype_I32 (mk_testop__0 I32 EQZ) (mk_num__0 I32 i) = (ieqz_underscore (sizenn (numtype_addrtype I32)) i)"
		| "fun_testop_underscore numtype_I64 (mk_testop__0 I64 EQZ) (mk_num__0 I64 i) = (ieqz_underscore (sizenn (numtype_addrtype I64)) i)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__I64 :: "relop_underscore ⇒ num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__I64 (mk_relop__0 I64 relop_Inn_EQ) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) = (ieq_underscore (sizenn (numtype_addrtype I64)) i_1 i_2)"
		| "fun_relop__I64 (mk_relop__0 I64 NE) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) = (ine_underscore (sizenn (numtype_addrtype I64)) i_1 i_2)"
		| "fun_relop__I64 (mk_relop__0 I64 (LT v_sx)) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) = (ilt_underscore (sizenn (numtype_addrtype I64)) v_sx i_1 i_2)"
		| "fun_relop__I64 (mk_relop__0 I64 (GT v_sx)) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) = (igt_underscore (sizenn (numtype_addrtype I64)) v_sx i_1 i_2)"
		| "fun_relop__I64 (mk_relop__0 I64 (LE v_sx)) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) = (ile_underscore (sizenn (numtype_addrtype I64)) v_sx i_1 i_2)"
		| "fun_relop__I64 (mk_relop__0 I64 (GE v_sx)) (mk_num__0 I64 i_1) (mk_num__0 I64 i_2) = (ige_underscore (sizenn (numtype_addrtype I64)) v_sx i_1 i_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__I32 :: "relop_underscore ⇒ num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__I32 (mk_relop__0 I32 relop_Inn_EQ) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) = (ieq_underscore (sizenn (numtype_addrtype I32)) i_1 i_2)"
		| "fun_relop__I32 (mk_relop__0 I32 NE) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) = (ine_underscore (sizenn (numtype_addrtype I32)) i_1 i_2)"
		| "fun_relop__I32 (mk_relop__0 I32 (LT v_sx)) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) = (ilt_underscore (sizenn (numtype_addrtype I32)) v_sx i_1 i_2)"
		| "fun_relop__I32 (mk_relop__0 I32 (GT v_sx)) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) = (igt_underscore (sizenn (numtype_addrtype I32)) v_sx i_1 i_2)"
		| "fun_relop__I32 (mk_relop__0 I32 (LE v_sx)) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) = (ile_underscore (sizenn (numtype_addrtype I32)) v_sx i_1 i_2)"
		| "fun_relop__I32 (mk_relop__0 I32 (GE v_sx)) (mk_num__0 I32 i_1) (mk_num__0 I32 i_2) = (ige_underscore (sizenn (numtype_addrtype I32)) v_sx i_1 i_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F64_mk_relop__1_F64_NE :: "num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F64_mk_relop__1_F64_NE (mk_num__1 Fnn_F64 f_1) (mk_num__1 Fnn_F64 f_2) = (fne_underscore (sizenn (numtype_Fnn Fnn_F64)) f_1 f_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F64_mk_relop__1_F64_LT :: "num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F64_mk_relop__1_F64_LT (mk_num__1 Fnn_F64 f_1) (mk_num__1 Fnn_F64 f_2) = (flt_underscore (sizenn (numtype_Fnn Fnn_F64)) f_1 f_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F64_mk_relop__1_F64_LE :: "num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F64_mk_relop__1_F64_LE (mk_num__1 Fnn_F64 f_1) (mk_num__1 Fnn_F64 f_2) = (fle_underscore (sizenn (numtype_Fnn Fnn_F64)) f_1 f_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F64_mk_relop__1_F64_GT :: "num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F64_mk_relop__1_F64_GT (mk_num__1 Fnn_F64 f_1) (mk_num__1 Fnn_F64 f_2) = (fgt_underscore (sizenn (numtype_Fnn Fnn_F64)) f_1 f_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F64_mk_relop__1_F64_GE :: "num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F64_mk_relop__1_F64_GE (mk_num__1 Fnn_F64 f_1) (mk_num__1 Fnn_F64 f_2) = (fge_underscore (sizenn (numtype_Fnn Fnn_F64)) f_1 f_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F64_mk_relop__1_F64_EQ :: "num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F64_mk_relop__1_F64_EQ (mk_num__1 Fnn_F64 f_1) (mk_num__1 Fnn_F64 f_2) = (feq_underscore (sizenn (numtype_Fnn Fnn_F64)) f_1 f_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F64_mk_relop__1_F64 :: "relop_Fnn ⇒ num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F64_mk_relop__1_F64 relop_Fnn_NE v_num_underscore v_num__0 = (fun_relop__F64_mk_relop__1_F64_NE v_num_underscore v_num__0)"
		| "fun_relop__F64_mk_relop__1_F64 relop_Fnn_LT v_num_underscore v_num__0 = (fun_relop__F64_mk_relop__1_F64_LT v_num_underscore v_num__0)"
		| "fun_relop__F64_mk_relop__1_F64 relop_Fnn_LE v_num_underscore v_num__0 = (fun_relop__F64_mk_relop__1_F64_LE v_num_underscore v_num__0)"
		| "fun_relop__F64_mk_relop__1_F64 relop_Fnn_GT v_num_underscore v_num__0 = (fun_relop__F64_mk_relop__1_F64_GT v_num_underscore v_num__0)"
		| "fun_relop__F64_mk_relop__1_F64 relop_Fnn_GE v_num_underscore v_num__0 = (fun_relop__F64_mk_relop__1_F64_GE v_num_underscore v_num__0)"
		| "fun_relop__F64_mk_relop__1_F64 relop_Fnn_EQ v_num_underscore v_num__0 = (fun_relop__F64_mk_relop__1_F64_EQ v_num_underscore v_num__0)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F64_mk_relop__1 :: "Fnn ⇒ relop_Fnn ⇒ num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F64_mk_relop__1 Fnn_F64 mk_relop__1_argument_1 v_num_underscore v_num__0 = (fun_relop__F64_mk_relop__1_F64 mk_relop__1_argument_1 v_num_underscore v_num__0)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F64 :: "relop_underscore ⇒ num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F64 (mk_relop__1 constructor_parameter_0 constructor_parameter_1) v_num_underscore v_num__0 = (fun_relop__F64_mk_relop__1 constructor_parameter_0 constructor_parameter_1 v_num_underscore v_num__0)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F32_mk_relop__1_F32_NE :: "num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F32_mk_relop__1_F32_NE (mk_num__1 Fnn_F32 f_1) (mk_num__1 Fnn_F32 f_2) = (fne_underscore (sizenn (numtype_Fnn Fnn_F32)) f_1 f_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F32_mk_relop__1_F32_LT :: "num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F32_mk_relop__1_F32_LT (mk_num__1 Fnn_F32 f_1) (mk_num__1 Fnn_F32 f_2) = (flt_underscore (sizenn (numtype_Fnn Fnn_F32)) f_1 f_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F32_mk_relop__1_F32_LE :: "num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F32_mk_relop__1_F32_LE (mk_num__1 Fnn_F32 f_1) (mk_num__1 Fnn_F32 f_2) = (fle_underscore (sizenn (numtype_Fnn Fnn_F32)) f_1 f_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F32_mk_relop__1_F32_GT :: "num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F32_mk_relop__1_F32_GT (mk_num__1 Fnn_F32 f_1) (mk_num__1 Fnn_F32 f_2) = (fgt_underscore (sizenn (numtype_Fnn Fnn_F32)) f_1 f_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F32_mk_relop__1_F32_GE :: "num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F32_mk_relop__1_F32_GE (mk_num__1 Fnn_F32 f_1) (mk_num__1 Fnn_F32 f_2) = (fge_underscore (sizenn (numtype_Fnn Fnn_F32)) f_1 f_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F32_mk_relop__1_F32_EQ :: "num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F32_mk_relop__1_F32_EQ (mk_num__1 Fnn_F32 f_1) (mk_num__1 Fnn_F32 f_2) = (feq_underscore (sizenn (numtype_Fnn Fnn_F32)) f_1 f_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F32_mk_relop__1_F32 :: "relop_Fnn ⇒ num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F32_mk_relop__1_F32 relop_Fnn_NE v_num_underscore v_num__0 = (fun_relop__F32_mk_relop__1_F32_NE v_num_underscore v_num__0)"
		| "fun_relop__F32_mk_relop__1_F32 relop_Fnn_LT v_num_underscore v_num__0 = (fun_relop__F32_mk_relop__1_F32_LT v_num_underscore v_num__0)"
		| "fun_relop__F32_mk_relop__1_F32 relop_Fnn_LE v_num_underscore v_num__0 = (fun_relop__F32_mk_relop__1_F32_LE v_num_underscore v_num__0)"
		| "fun_relop__F32_mk_relop__1_F32 relop_Fnn_GT v_num_underscore v_num__0 = (fun_relop__F32_mk_relop__1_F32_GT v_num_underscore v_num__0)"
		| "fun_relop__F32_mk_relop__1_F32 relop_Fnn_GE v_num_underscore v_num__0 = (fun_relop__F32_mk_relop__1_F32_GE v_num_underscore v_num__0)"
		| "fun_relop__F32_mk_relop__1_F32 relop_Fnn_EQ v_num_underscore v_num__0 = (fun_relop__F32_mk_relop__1_F32_EQ v_num_underscore v_num__0)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F32_mk_relop__1 :: "Fnn ⇒ relop_Fnn ⇒ num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F32_mk_relop__1 Fnn_F32 mk_relop__1_argument_1 v_num_underscore v_num__0 = (fun_relop__F32_mk_relop__1_F32 mk_relop__1_argument_1 v_num_underscore v_num__0)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop__F32 :: "relop_underscore ⇒ num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop__F32 (mk_relop__1 constructor_parameter_0 constructor_parameter_1) v_num_underscore v_num__0 = (fun_relop__F32_mk_relop__1 constructor_parameter_0 constructor_parameter_1 v_num_underscore v_num__0)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 *)
function (sequential) fun_relop_underscore :: "numtype ⇒ relop_underscore ⇒ num_underscore ⇒ num_underscore ⇒ u32" where
		  "fun_relop_underscore numtype_I64 v_relop_underscore v_num_underscore v_num__0 = (fun_relop__I64 v_relop_underscore v_num_underscore v_num__0)"
		| "fun_relop_underscore numtype_I32 v_relop_underscore v_num_underscore v_num__0 = (fun_relop__I32 v_relop_underscore v_num_underscore v_num__0)"
		| "fun_relop_underscore F64 v_relop_underscore v_num_underscore v_num__0 = (fun_relop__F64 v_relop_underscore v_num_underscore v_num__0)"
		| "fun_relop_underscore F32 v_relop_underscore v_num_underscore v_num__0 = (fun_relop__F32 v_relop_underscore v_num_underscore v_num__0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:372.6-372.14 *)
inductive fun_cvtop__underscore :: "numtype ⇒ numtype ⇒ cvtop__underscore ⇒ num_underscore ⇒ (num_underscore list) ⇒ bool" where
	  fun_cvtop___case_0 :
		"fun_cvtop__underscore numtype_I32 numtype_I32 (mk_cvtop___0 I32 I32 (cvtop__Inn_1_Inn_2_EXTEND v_sx)) (mk_num__0 I32 i_1) [(mk_num__0 I32 (extend__underscore (sizenn1 (numtype_addrtype I32)) (sizenn2 (numtype_addrtype I32)) v_sx i_1))]"
	| fun_cvtop___case_1 :
		"fun_cvtop__underscore numtype_I64 numtype_I32 (mk_cvtop___0 I64 I32 (cvtop__Inn_1_Inn_2_EXTEND v_sx)) (mk_num__0 I64 i_1) [(mk_num__0 I32 (extend__underscore (sizenn1 (numtype_addrtype I64)) (sizenn2 (numtype_addrtype I32)) v_sx i_1))]"
	| fun_cvtop___case_2 :
		"fun_cvtop__underscore numtype_I32 numtype_I64 (mk_cvtop___0 I32 I64 (cvtop__Inn_1_Inn_2_EXTEND v_sx)) (mk_num__0 I32 i_1) [(mk_num__0 I64 (extend__underscore (sizenn1 (numtype_addrtype I32)) (sizenn2 (numtype_addrtype I64)) v_sx i_1))]"
	| fun_cvtop___case_3 :
		"fun_cvtop__underscore numtype_I64 numtype_I64 (mk_cvtop___0 I64 I64 (cvtop__Inn_1_Inn_2_EXTEND v_sx)) (mk_num__0 I64 i_1) [(mk_num__0 I64 (extend__underscore (sizenn1 (numtype_addrtype I64)) (sizenn2 (numtype_addrtype I64)) v_sx i_1))]"
	| fun_cvtop___case_4 :
		"fun_cvtop__underscore numtype_I32 numtype_I32 (mk_cvtop___0 I32 I32 WRAP) (mk_num__0 I32 i_1) [(mk_num__0 I32 (wrap__underscore (sizenn1 (numtype_addrtype I32)) (sizenn2 (numtype_addrtype I32)) i_1))]"
	| fun_cvtop___case_5 :
		"fun_cvtop__underscore numtype_I64 numtype_I32 (mk_cvtop___0 I64 I32 WRAP) (mk_num__0 I64 i_1) [(mk_num__0 I32 (wrap__underscore (sizenn1 (numtype_addrtype I64)) (sizenn2 (numtype_addrtype I32)) i_1))]"
	| fun_cvtop___case_6 :
		"fun_cvtop__underscore numtype_I32 numtype_I64 (mk_cvtop___0 I32 I64 WRAP) (mk_num__0 I32 i_1) [(mk_num__0 I64 (wrap__underscore (sizenn1 (numtype_addrtype I32)) (sizenn2 (numtype_addrtype I64)) i_1))]"
	| fun_cvtop___case_7 :
		"fun_cvtop__underscore numtype_I64 numtype_I64 (mk_cvtop___0 I64 I64 WRAP) (mk_num__0 I64 i_1) [(mk_num__0 I64 (wrap__underscore (sizenn1 (numtype_addrtype I64)) (sizenn2 (numtype_addrtype I64)) i_1))]"
	| fun_cvtop___case_8 :
		"fun_cvtop__underscore F32 numtype_I32 (mk_cvtop___2 Fnn_F32 I32 (cvtop__Fnn_1_Inn_2_TRUNC v_sx)) (mk_num__1 Fnn_F32 f_1) (map (λ (iter_0_33 :: iN). (mk_num__0 I32 iter_0_33)) (option_to_list (trunc__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_addrtype I32)) v_sx f_1)))"
	| fun_cvtop___case_9 :
		"fun_cvtop__underscore F64 numtype_I32 (mk_cvtop___2 Fnn_F64 I32 (cvtop__Fnn_1_Inn_2_TRUNC v_sx)) (mk_num__1 Fnn_F64 f_1) (map (λ (iter_0_34 :: iN). (mk_num__0 I32 iter_0_34)) (option_to_list (trunc__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_addrtype I32)) v_sx f_1)))"
	| fun_cvtop___case_10 :
		"fun_cvtop__underscore F32 numtype_I64 (mk_cvtop___2 Fnn_F32 I64 (cvtop__Fnn_1_Inn_2_TRUNC v_sx)) (mk_num__1 Fnn_F32 f_1) (map (λ (iter_0_35 :: iN). (mk_num__0 I64 iter_0_35)) (option_to_list (trunc__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_addrtype I64)) v_sx f_1)))"
	| fun_cvtop___case_11 :
		"fun_cvtop__underscore F64 numtype_I64 (mk_cvtop___2 Fnn_F64 I64 (cvtop__Fnn_1_Inn_2_TRUNC v_sx)) (mk_num__1 Fnn_F64 f_1) (map (λ (iter_0_36 :: iN). (mk_num__0 I64 iter_0_36)) (option_to_list (trunc__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_addrtype I64)) v_sx f_1)))"
	| fun_cvtop___case_12 :
		"fun_cvtop__underscore F32 numtype_I32 (mk_cvtop___2 Fnn_F32 I32 (TRUNC_SAT v_sx)) (mk_num__1 Fnn_F32 f_1) (map (λ (iter_0_37 :: iN). (mk_num__0 I32 iter_0_37)) (option_to_list (trunc_sat__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_addrtype I32)) v_sx f_1)))"
	| fun_cvtop___case_13 :
		"fun_cvtop__underscore F64 numtype_I32 (mk_cvtop___2 Fnn_F64 I32 (TRUNC_SAT v_sx)) (mk_num__1 Fnn_F64 f_1) (map (λ (iter_0_38 :: iN). (mk_num__0 I32 iter_0_38)) (option_to_list (trunc_sat__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_addrtype I32)) v_sx f_1)))"
	| fun_cvtop___case_14 :
		"fun_cvtop__underscore F32 numtype_I64 (mk_cvtop___2 Fnn_F32 I64 (TRUNC_SAT v_sx)) (mk_num__1 Fnn_F32 f_1) (map (λ (iter_0_39 :: iN). (mk_num__0 I64 iter_0_39)) (option_to_list (trunc_sat__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_addrtype I64)) v_sx f_1)))"
	| fun_cvtop___case_15 :
		"fun_cvtop__underscore F64 numtype_I64 (mk_cvtop___2 Fnn_F64 I64 (TRUNC_SAT v_sx)) (mk_num__1 Fnn_F64 f_1) (map (λ (iter_0_40 :: iN). (mk_num__0 I64 iter_0_40)) (option_to_list (trunc_sat__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_addrtype I64)) v_sx f_1)))"
	| fun_cvtop___case_16 :
		"fun_cvtop__underscore numtype_I32 F32 (mk_cvtop___1 I32 Fnn_F32 (CONVERT v_sx)) (mk_num__0 I32 i_1) [(mk_num__1 Fnn_F32 (convert__underscore (sizenn1 (numtype_addrtype I32)) (sizenn2 (numtype_Fnn Fnn_F32)) v_sx i_1))]"
	| fun_cvtop___case_17 :
		"fun_cvtop__underscore numtype_I64 F32 (mk_cvtop___1 I64 Fnn_F32 (CONVERT v_sx)) (mk_num__0 I64 i_1) [(mk_num__1 Fnn_F32 (convert__underscore (sizenn1 (numtype_addrtype I64)) (sizenn2 (numtype_Fnn Fnn_F32)) v_sx i_1))]"
	| fun_cvtop___case_18 :
		"fun_cvtop__underscore numtype_I32 F64 (mk_cvtop___1 I32 Fnn_F64 (CONVERT v_sx)) (mk_num__0 I32 i_1) [(mk_num__1 Fnn_F64 (convert__underscore (sizenn1 (numtype_addrtype I32)) (sizenn2 (numtype_Fnn Fnn_F64)) v_sx i_1))]"
	| fun_cvtop___case_19 :
		"fun_cvtop__underscore numtype_I64 F64 (mk_cvtop___1 I64 Fnn_F64 (CONVERT v_sx)) (mk_num__0 I64 i_1) [(mk_num__1 Fnn_F64 (convert__underscore (sizenn1 (numtype_addrtype I64)) (sizenn2 (numtype_Fnn Fnn_F64)) v_sx i_1))]"
	| fun_cvtop___case_20 :
		"fun_cvtop__underscore F32 F32 (mk_cvtop___3 Fnn_F32 Fnn_F32 PROMOTE) (mk_num__1 Fnn_F32 f_1) (map (λ (iter_0_41 :: fN). (mk_num__1 Fnn_F32 iter_0_41)) (promote__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F32)) f_1))"
	| fun_cvtop___case_21 :
		"fun_cvtop__underscore F64 F32 (mk_cvtop___3 Fnn_F64 Fnn_F32 PROMOTE) (mk_num__1 Fnn_F64 f_1) (map (λ (iter_0_42 :: fN). (mk_num__1 Fnn_F32 iter_0_42)) (promote__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F32)) f_1))"
	| fun_cvtop___case_22 :
		"fun_cvtop__underscore F32 F64 (mk_cvtop___3 Fnn_F32 Fnn_F64 PROMOTE) (mk_num__1 Fnn_F32 f_1) (map (λ (iter_0_43 :: fN). (mk_num__1 Fnn_F64 iter_0_43)) (promote__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F64)) f_1))"
	| fun_cvtop___case_23 :
		"fun_cvtop__underscore F64 F64 (mk_cvtop___3 Fnn_F64 Fnn_F64 PROMOTE) (mk_num__1 Fnn_F64 f_1) (map (λ (iter_0_44 :: fN). (mk_num__1 Fnn_F64 iter_0_44)) (promote__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F64)) f_1))"
	| fun_cvtop___case_24 :
		"fun_cvtop__underscore F32 F32 (mk_cvtop___3 Fnn_F32 Fnn_F32 DEMOTE) (mk_num__1 Fnn_F32 f_1) (map (λ (iter_0_45 :: fN). (mk_num__1 Fnn_F32 iter_0_45)) (demote__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F32)) f_1))"
	| fun_cvtop___case_25 :
		"fun_cvtop__underscore F64 F32 (mk_cvtop___3 Fnn_F64 Fnn_F32 DEMOTE) (mk_num__1 Fnn_F64 f_1) (map (λ (iter_0_46 :: fN). (mk_num__1 Fnn_F32 iter_0_46)) (demote__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F32)) f_1))"
	| fun_cvtop___case_26 :
		"fun_cvtop__underscore F32 F64 (mk_cvtop___3 Fnn_F32 Fnn_F64 DEMOTE) (mk_num__1 Fnn_F32 f_1) (map (λ (iter_0_47 :: fN). (mk_num__1 Fnn_F64 iter_0_47)) (demote__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F64)) f_1))"
	| fun_cvtop___case_27 :
		"fun_cvtop__underscore F64 F64 (mk_cvtop___3 Fnn_F64 Fnn_F64 DEMOTE) (mk_num__1 Fnn_F64 f_1) (map (λ (iter_0_48 :: fN). (mk_num__1 Fnn_F64 iter_0_48)) (demote__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F64)) f_1))"
	| fun_cvtop___case_28 :
		"((size (numtype_addrtype I32)) = (size (numtype_Fnn Fnn_F32))) ⟹
		 fun_cvtop__underscore numtype_I32 F32 (mk_cvtop___1 I32 Fnn_F32 REINTERPRET) (mk_num__0 I32 i_1) [(reinterpret__underscore (numtype_addrtype I32) (numtype_Fnn Fnn_F32) (mk_num__0 I32 i_1))]"
	| fun_cvtop___case_29 :
		"((size (numtype_addrtype I64)) = (size (numtype_Fnn Fnn_F32))) ⟹
		 fun_cvtop__underscore numtype_I64 F32 (mk_cvtop___1 I64 Fnn_F32 REINTERPRET) (mk_num__0 I64 i_1) [(reinterpret__underscore (numtype_addrtype I64) (numtype_Fnn Fnn_F32) (mk_num__0 I64 i_1))]"
	| fun_cvtop___case_30 :
		"((size (numtype_addrtype I32)) = (size (numtype_Fnn Fnn_F64))) ⟹
		 fun_cvtop__underscore numtype_I32 F64 (mk_cvtop___1 I32 Fnn_F64 REINTERPRET) (mk_num__0 I32 i_1) [(reinterpret__underscore (numtype_addrtype I32) (numtype_Fnn Fnn_F64) (mk_num__0 I32 i_1))]"
	| fun_cvtop___case_31 :
		"((size (numtype_addrtype I64)) = (size (numtype_Fnn Fnn_F64))) ⟹
		 fun_cvtop__underscore numtype_I64 F64 (mk_cvtop___1 I64 Fnn_F64 REINTERPRET) (mk_num__0 I64 i_1) [(reinterpret__underscore (numtype_addrtype I64) (numtype_Fnn Fnn_F64) (mk_num__0 I64 i_1))]"
	| fun_cvtop___case_32 :
		"((size (numtype_Fnn Fnn_F32)) = (size (numtype_addrtype I32))) ⟹
		 fun_cvtop__underscore F32 numtype_I32 (mk_cvtop___2 Fnn_F32 I32 cvtop__Fnn_1_Inn_2_REINTERPRET) (mk_num__1 Fnn_F32 f_1) [(reinterpret__underscore (numtype_Fnn Fnn_F32) (numtype_addrtype I32) (mk_num__1 Fnn_F32 f_1))]"
	| fun_cvtop___case_33 :
		"((size (numtype_Fnn Fnn_F64)) = (size (numtype_addrtype I32))) ⟹
		 fun_cvtop__underscore F64 numtype_I32 (mk_cvtop___2 Fnn_F64 I32 cvtop__Fnn_1_Inn_2_REINTERPRET) (mk_num__1 Fnn_F64 f_1) [(reinterpret__underscore (numtype_Fnn Fnn_F64) (numtype_addrtype I32) (mk_num__1 Fnn_F64 f_1))]"
	| fun_cvtop___case_34 :
		"((size (numtype_Fnn Fnn_F32)) = (size (numtype_addrtype I64))) ⟹
		 fun_cvtop__underscore F32 numtype_I64 (mk_cvtop___2 Fnn_F32 I64 cvtop__Fnn_1_Inn_2_REINTERPRET) (mk_num__1 Fnn_F32 f_1) [(reinterpret__underscore (numtype_Fnn Fnn_F32) (numtype_addrtype I64) (mk_num__1 Fnn_F32 f_1))]"
	| fun_cvtop___case_35 :
		"((size (numtype_Fnn Fnn_F64)) = (size (numtype_addrtype I64))) ⟹
		 fun_cvtop__underscore F64 numtype_I64 (mk_cvtop___2 Fnn_F64 I64 cvtop__Fnn_1_Inn_2_REINTERPRET) (mk_num__1 Fnn_F64 f_1) [(reinterpret__underscore (numtype_Fnn Fnn_F64) (numtype_addrtype I64) (mk_num__1 Fnn_F64 f_1))]"

(* Axiom Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:10.1-10.84 *)
axiomatization lanes_underscore :: "shape ⇒ vec_underscore ⇒ (lane_underscore list)"

(* Axiom Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:12.1-13.37 *)
axiomatization inv_lanes_underscore :: "shape ⇒ (lane_underscore list) ⇒ vec_underscore"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:19.6-19.13 *)
inductive fun_zeroop :: "shape ⇒ shape ⇒ vcvtop__underscore ⇒ (zero option) ⇒ bool" where
	  fun_zeroop_case_0 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I32 M_1_0 Jnn_I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_1 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I64 M_1_0 Jnn_I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_2 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I8 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I8 M_1_0 Jnn_I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_3 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I16 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I16 M_1_0 Jnn_I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_4 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I32 M_1_0 Jnn_I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_5 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I64 M_1_0 Jnn_I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_6 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I8 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I8 M_1_0 Jnn_I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_7 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I16 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I16 M_1_0 Jnn_I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_8 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I32 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I32 M_1_0 Jnn_I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_9 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I64 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I64 M_1_0 Jnn_I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_10 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I8 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I8 M_1_0 Jnn_I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_11 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I16 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I16 M_1_0 Jnn_I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_12 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I32 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I32 M_1_0 Jnn_I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_13 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I64 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I64 M_1_0 Jnn_I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_14 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I8 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I8 M_1_0 Jnn_I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_15 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I16 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I16 M_1_0 Jnn_I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) None"
	| fun_zeroop_case_16 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I32 M_1_0 Fnn_F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) None"
	| fun_zeroop_case_17 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I64 M_1_0 Fnn_F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) None"
	| fun_zeroop_case_18 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I8 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I8 M_1_0 Fnn_F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) None"
	| fun_zeroop_case_19 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I16 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I16 M_1_0 Fnn_F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) None"
	| fun_zeroop_case_20 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I32 M_1_0 Fnn_F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) None"
	| fun_zeroop_case_21 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I64 M_1_0 Fnn_F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) None"
	| fun_zeroop_case_22 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I8 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I8 M_1_0 Fnn_F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) None"
	| fun_zeroop_case_23 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_I16 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I16 M_1_0 Fnn_F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) None"
	| fun_zeroop_case_24 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_25 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_26 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_27 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_28 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I8 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_29 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I8 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_30 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I16 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_31 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I16 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_32 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I32 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_33 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I32 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_34 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I64 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_35 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I64 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_36 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I8 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_37 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I8 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_38 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I16 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_39 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I16 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) zero_opt"
	| fun_zeroop_case_40 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F32 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE v_zero)) (Some v_zero)"
	| fun_zeroop_case_41 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F32 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE v_zero)) (Some v_zero)"
	| fun_zeroop_case_42 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F64 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE v_zero)) (Some v_zero)"
	| fun_zeroop_case_43 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F64 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE v_zero)) (Some v_zero)"
	| fun_zeroop_case_44 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F32 M_2_0 PROMOTELOW) None"
	| fun_zeroop_case_45 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F32 M_2_0 PROMOTELOW) None"
	| fun_zeroop_case_46 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F64 M_2_0 PROMOTELOW) None"
	| fun_zeroop_case_47 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_zeroop (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F64 M_2_0 PROMOTELOW) None"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:27.6-27.13 *)
inductive fun_halfop :: "shape ⇒ shape ⇒ vcvtop__underscore ⇒ (half option) ⇒ bool" where
	  fun_halfop_case_0 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I32 M_1_0 Jnn_I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_1 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I64 M_1_0 Jnn_I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_2 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I8 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I8 M_1_0 Jnn_I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_3 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I16 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I16 M_1_0 Jnn_I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_4 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I32 M_1_0 Jnn_I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_5 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I64 M_1_0 Jnn_I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_6 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I8 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I8 M_1_0 Jnn_I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_7 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I16 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I16 M_1_0 Jnn_I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_8 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I32 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I32 M_1_0 Jnn_I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_9 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I64 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I64 M_1_0 Jnn_I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_10 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I8 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I8 M_1_0 Jnn_I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_11 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I16 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I16 M_1_0 Jnn_I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_12 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I32 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I32 M_1_0 Jnn_I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_13 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I64 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I64 M_1_0 Jnn_I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_14 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I8 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I8 M_1_0 Jnn_I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_15 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I16 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I16 M_1_0 Jnn_I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (Some v_half)"
	| fun_halfop_case_16 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I32 M_1_0 Fnn_F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) half_opt"
	| fun_halfop_case_17 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I64 M_1_0 Fnn_F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) half_opt"
	| fun_halfop_case_18 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I8 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I8 M_1_0 Fnn_F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) half_opt"
	| fun_halfop_case_19 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I16 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I16 M_1_0 Fnn_F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) half_opt"
	| fun_halfop_case_20 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I32 M_1_0 Fnn_F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) half_opt"
	| fun_halfop_case_21 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I64 M_1_0 Fnn_F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) half_opt"
	| fun_halfop_case_22 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I8 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I8 M_1_0 Fnn_F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) half_opt"
	| fun_halfop_case_23 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_I16 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I16 M_1_0 Fnn_F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) half_opt"
	| fun_halfop_case_24 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) None"
	| fun_halfop_case_25 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) None"
	| fun_halfop_case_26 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) None"
	| fun_halfop_case_27 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) None"
	| fun_halfop_case_28 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I8 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) None"
	| fun_halfop_case_29 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I8 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) None"
	| fun_halfop_case_30 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I16 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) None"
	| fun_halfop_case_31 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I16 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) None"
	| fun_halfop_case_32 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I32 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) None"
	| fun_halfop_case_33 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I32 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) None"
	| fun_halfop_case_34 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I64 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) None"
	| fun_halfop_case_35 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I64 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) None"
	| fun_halfop_case_36 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I8 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) None"
	| fun_halfop_case_37 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I8 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) None"
	| fun_halfop_case_38 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F32 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I16 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) None"
	| fun_halfop_case_39 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F64 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I16 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) None"
	| fun_halfop_case_40 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F32 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE v_zero)) None"
	| fun_halfop_case_41 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F32 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE v_zero)) None"
	| fun_halfop_case_42 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F64 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE v_zero)) None"
	| fun_halfop_case_43 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F64 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE v_zero)) None"
	| fun_halfop_case_44 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F32 M_2_0 PROMOTELOW) (Some LOW)"
	| fun_halfop_case_45 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F32 M_2_0 PROMOTELOW) (Some LOW)"
	| fun_halfop_case_46 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F64 M_2_0 PROMOTELOW) (Some LOW)"
	| fun_halfop_case_47 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_halfop (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F64 M_2_0 PROMOTELOW) (Some LOW)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:35.1-35.32 *)
function (sequential) fun_half :: "half ⇒ nat ⇒ nat ⇒ nat" where
		  "fun_half LOW i j = i"
		| "fun_half HIGH i j = j"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:40.1-40.46 *)
function (sequential) iswizzle_lane_underscore :: "N ⇒ (iN list) ⇒ iN ⇒ iN" where
		  "iswizzle_lane_underscore v_N c_lst i = (if ((proj_uN_0 i) < (length c_lst)) then (c_lst ! (proj_uN_0 i)) else (mk_uN 0))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:41.1-41.54 *)
axiomatization irelaxed_swizzle_lane_underscore :: "N ⇒ (iN list) ⇒ iN ⇒ iN"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:54.1-54.73 *)
axiomatization ivunop_underscore :: "shape ⇒ (N ⇒ iN ⇒ iN) ⇒ vec_underscore ⇒ (vec_underscore list)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:55.1-55.74 *)
axiomatization fvunop_underscore :: "shape ⇒ (N ⇒ fN ⇒ (fN list)) ⇒ vec_underscore ⇒ (vec_underscore list)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:57.1-57.93 *)
axiomatization ivbinop_underscore :: "shape ⇒ (N ⇒ iN ⇒ iN ⇒ iN) ⇒ vec_underscore ⇒ vec_underscore ⇒ (vec_underscore list)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:58.1-58.103 *)
axiomatization ivbinopsx_underscore :: "shape ⇒ (N ⇒ sx ⇒ iN ⇒ iN ⇒ iN) ⇒ sx ⇒ vec_underscore ⇒ vec_underscore ⇒ (vec_underscore list)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:59.1-59.106 *)
axiomatization ivbinopsxnd_underscore :: "shape ⇒ (N ⇒ sx ⇒ iN ⇒ iN ⇒ (iN list)) ⇒ sx ⇒ vec_underscore ⇒ vec_underscore ⇒ (vec_underscore list)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:60.1-60.94 *)
axiomatization fvbinop_underscore :: "shape ⇒ (N ⇒ fN ⇒ fN ⇒ (fN list)) ⇒ vec_underscore ⇒ vec_underscore ⇒ (vec_underscore list)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:62.1-62.116 *)
axiomatization ivternopnd_underscore :: "shape ⇒ (N ⇒ iN ⇒ iN ⇒ iN ⇒ (iN list)) ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ (vec_underscore list)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:63.1-63.114 *)
axiomatization fvternop_underscore :: "shape ⇒ (N ⇒ fN ⇒ fN ⇒ fN ⇒ (fN list)) ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ (vec_underscore list)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:65.1-65.90 *)
axiomatization ivrelop_underscore :: "shape ⇒ (N ⇒ iN ⇒ iN ⇒ u32) ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:66.1-66.100 *)
axiomatization ivrelopsx_underscore :: "shape ⇒ (N ⇒ sx ⇒ iN ⇒ iN ⇒ u32) ⇒ sx ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:67.1-67.90 *)
axiomatization fvrelop_underscore :: "shape ⇒ (N ⇒ fN ⇒ fN ⇒ u32) ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:69.1-69.85 *)
axiomatization ivshiftop_underscore :: "shape ⇒ (N ⇒ iN ⇒ u32 ⇒ iN) ⇒ vec_underscore ⇒ u32 ⇒ vec_underscore"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:70.1-70.95 *)
axiomatization ivshiftopsx_underscore :: "shape ⇒ (N ⇒ sx ⇒ iN ⇒ u32 ⇒ iN) ⇒ sx ⇒ vec_underscore ⇒ u32 ⇒ vec_underscore"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:72.6-72.19 *)
inductive fun_ivbitmaskop_underscore :: "shape ⇒ vec_underscore ⇒ u32 ⇒ bool" where
	  fun_ivbitmaskop__case_0 :
		"list_all (λ (iter_123 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_123)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v_1) ⟹
		 list_all (λ (iter_124 :: bit). (wf_bit iter_124)) (ibits_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) c) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 list_all (λ (c_1_191 :: lane_underscore). ((proj_lane__2 c_1_191) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_191 :: lane_underscore). (wf_bit (mk_bit (proj_uN_0 (ilt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) S (the ((proj_lane__2 c_1_191))) (mk_uN 0)))))) c_1_lst ⟹
		 (wf_bit (mk_bit 0)) ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v_1)) ⟹
		 list_all (λ (c_1_193 :: lane_underscore). ((proj_lane__2 c_1_193) ≠ None)) c_1_lst ⟹
		 ((ibits_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) c) = ((map (λ (c_1_193 :: lane_underscore). (mk_bit (proj_uN_0 (ilt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) S (the ((proj_lane__2 c_1_193))) (mk_uN 0))))) c_1_lst) @ (repeat (((32 :: nat) - (v_M :: nat)) :: nat) (mk_bit 0)))) ⟹
		 fun_ivbitmaskop_underscore (X lanetype_I32 (mk_dim v_M)) v_1 (irev_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) c)"
	| fun_ivbitmaskop__case_1 :
		"list_all (λ (iter_125 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_125)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v_1) ⟹
		 list_all (λ (iter_126 :: bit). (wf_bit iter_126)) (ibits_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) c) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 list_all (λ (c_1_194 :: lane_underscore). ((proj_lane__2 c_1_194) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_194 :: lane_underscore). (wf_bit (mk_bit (proj_uN_0 (ilt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) S (the ((proj_lane__2 c_1_194))) (mk_uN 0)))))) c_1_lst ⟹
		 (wf_bit (mk_bit 0)) ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v_1)) ⟹
		 list_all (λ (c_1_196 :: lane_underscore). ((proj_lane__2 c_1_196) ≠ None)) c_1_lst ⟹
		 ((ibits_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) c) = ((map (λ (c_1_196 :: lane_underscore). (mk_bit (proj_uN_0 (ilt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) S (the ((proj_lane__2 c_1_196))) (mk_uN 0))))) c_1_lst) @ (repeat (((32 :: nat) - (v_M :: nat)) :: nat) (mk_bit 0)))) ⟹
		 fun_ivbitmaskop_underscore (X lanetype_I64 (mk_dim v_M)) v_1 (irev_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) c)"
	| fun_ivbitmaskop__case_2 :
		"list_all (λ (iter_127 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_127)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v_1) ⟹
		 list_all (λ (iter_128 :: bit). (wf_bit iter_128)) (ibits_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) c) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 list_all (λ (c_1_197 :: lane_underscore). ((proj_lane__2 c_1_197) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_197 :: lane_underscore). (wf_bit (mk_bit (proj_uN_0 (ilt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) S (the ((proj_lane__2 c_1_197))) (mk_uN 0)))))) c_1_lst ⟹
		 (wf_bit (mk_bit 0)) ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v_1)) ⟹
		 list_all (λ (c_1_199 :: lane_underscore). ((proj_lane__2 c_1_199) ≠ None)) c_1_lst ⟹
		 ((ibits_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) c) = ((map (λ (c_1_199 :: lane_underscore). (mk_bit (proj_uN_0 (ilt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) S (the ((proj_lane__2 c_1_199))) (mk_uN 0))))) c_1_lst) @ (repeat (((32 :: nat) - (v_M :: nat)) :: nat) (mk_bit 0)))) ⟹
		 fun_ivbitmaskop_underscore (X lanetype_I8 (mk_dim v_M)) v_1 (irev_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) c)"
	| fun_ivbitmaskop__case_3 :
		"list_all (λ (iter_129 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_129)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v_1) ⟹
		 list_all (λ (iter_130 :: bit). (wf_bit iter_130)) (ibits_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) c) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 list_all (λ (c_1_200 :: lane_underscore). ((proj_lane__2 c_1_200) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_200 :: lane_underscore). (wf_bit (mk_bit (proj_uN_0 (ilt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) S (the ((proj_lane__2 c_1_200))) (mk_uN 0)))))) c_1_lst ⟹
		 (wf_bit (mk_bit 0)) ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v_1)) ⟹
		 list_all (λ (c_1_202 :: lane_underscore). ((proj_lane__2 c_1_202) ≠ None)) c_1_lst ⟹
		 ((ibits_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) c) = ((map (λ (c_1_202 :: lane_underscore). (mk_bit (proj_uN_0 (ilt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) S (the ((proj_lane__2 c_1_202))) (mk_uN 0))))) c_1_lst) @ (repeat (((32 :: nat) - (v_M :: nat)) :: nat) (mk_bit 0)))) ⟹
		 fun_ivbitmaskop_underscore (X lanetype_I16 (mk_dim v_M)) v_1 (irev_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) c)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:73.1-73.96 *)
axiomatization ivswizzlop_underscore :: "shape ⇒ (N ⇒ (iN list) ⇒ iN ⇒ iN) ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:74.6-74.18 *)
inductive fun_ivshufflop_underscore :: "shape ⇒ (laneidx list) ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ bool" where
	  fun_ivshufflop__case_0 :
		"list_all (λ (c_1_219 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) c_1_219)) c_1_lst ⟹
		 list_all (λ (c_2_149 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) c_2_149)) c_2_lst ⟹
		 list_all (λ (iter_139 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_139)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v_1) ⟹
		 list_all (λ (iter_140 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_140)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v_2) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v_2)) ⟹
		 list_all (λ (i_117183 :: laneidx). ((proj_uN_0 i_117183) < (length (c_1_lst @ c_2_lst)))) i_lst ⟹
		 (c_lst = (map (λ (i_117183 :: laneidx). ((c_1_lst @ c_2_lst) ! (proj_uN_0 i_117183))) i_lst)) ⟹
		 fun_ivshufflop_underscore (X lanetype_I32 (mk_dim v_M)) i_lst v_1 v_2 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) c_lst)"
	| fun_ivshufflop__case_1 :
		"list_all (λ (c_1_222 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) c_1_222)) c_1_lst ⟹
		 list_all (λ (c_2_152 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) c_2_152)) c_2_lst ⟹
		 list_all (λ (iter_141 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_141)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v_1) ⟹
		 list_all (λ (iter_142 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_142)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v_2) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v_2)) ⟹
		 list_all (λ (i_117196 :: laneidx). ((proj_uN_0 i_117196) < (length (c_1_lst @ c_2_lst)))) i_lst ⟹
		 (c_lst = (map (λ (i_117196 :: laneidx). ((c_1_lst @ c_2_lst) ! (proj_uN_0 i_117196))) i_lst)) ⟹
		 fun_ivshufflop_underscore (X lanetype_I64 (mk_dim v_M)) i_lst v_1 v_2 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) c_lst)"
	| fun_ivshufflop__case_2 :
		"list_all (λ (c_1_225 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) c_1_225)) c_1_lst ⟹
		 list_all (λ (c_2_155 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) c_2_155)) c_2_lst ⟹
		 list_all (λ (iter_143 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_143)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v_1) ⟹
		 list_all (λ (iter_144 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_144)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v_2) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v_2)) ⟹
		 list_all (λ (i_117209 :: laneidx). ((proj_uN_0 i_117209) < (length (c_1_lst @ c_2_lst)))) i_lst ⟹
		 (c_lst = (map (λ (i_117209 :: laneidx). ((c_1_lst @ c_2_lst) ! (proj_uN_0 i_117209))) i_lst)) ⟹
		 fun_ivshufflop_underscore (X lanetype_I8 (mk_dim v_M)) i_lst v_1 v_2 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) c_lst)"
	| fun_ivshufflop__case_3 :
		"list_all (λ (c_1_228 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) c_1_228)) c_1_lst ⟹
		 list_all (λ (c_2_158 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) c_2_158)) c_2_lst ⟹
		 list_all (λ (iter_145 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_145)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v_1) ⟹
		 list_all (λ (iter_146 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_146)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v_2) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v_2)) ⟹
		 list_all (λ (i_117222 :: laneidx). ((proj_uN_0 i_117222) < (length (c_1_lst @ c_2_lst)))) i_lst ⟹
		 (c_lst = (map (λ (i_117222 :: laneidx). ((c_1_lst @ c_2_lst) ! (proj_uN_0 i_117222))) i_lst)) ⟹
		 fun_ivshufflop_underscore (X lanetype_I16 (mk_dim v_M)) i_lst v_1 v_2 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) c_lst)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:165.1-166.28 *)
function (sequential) vvunop_underscore :: "vectype ⇒ vvunop ⇒ vec_underscore ⇒ (vec_underscore list)" where
		  "vvunop_underscore v_Vnn NOT v = [(inot_underscore (vsizenn v_Vnn) v)]"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:167.1-168.31 *)
function (sequential) vvbinop_underscore :: "vectype ⇒ vvbinop ⇒ vec_underscore ⇒ vec_underscore ⇒ (vec_underscore list)" where
		  "vvbinop_underscore v_Vnn vvbinop_AND v_1 v_2 = [(iand_underscore (vsizenn v_Vnn) v_1 v_2)]"
		| "vvbinop_underscore v_Vnn ANDNOT v_1 v_2 = [(iandnot_underscore (vsizenn v_Vnn) v_1 v_2)]"
		| "vvbinop_underscore v_Vnn vvbinop_OR v_1 v_2 = [(ior_underscore (vsizenn v_Vnn) v_1 v_2)]"
		| "vvbinop_underscore v_Vnn vvbinop_XOR v_1 v_2 = [(ixor_underscore (vsizenn v_Vnn) v_1 v_2)]"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:169.1-170.34 *)
function (sequential) vvternop_underscore :: "vectype ⇒ vvternop ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ (vec_underscore list)" where
		  "vvternop_underscore v_Vnn BITSELECT v_1 v_2 v_3 = [(ibitselect_underscore (vsizenn v_Vnn) v_1 v_2 v_3)]"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:172.6-172.13 *)
inductive fun_vunop_underscore :: "shape ⇒ vunop_underscore ⇒ vec_underscore ⇒ (vec_underscore list) ⇒ bool" where
	  fun_vunop__case_0 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_M_ABS) v (fvunop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fabs_underscore v)"
	| fun_vunop__case_1 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_M_ABS) v (fvunop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fabs_underscore v)"
	| fun_vunop__case_2 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_M_NEG) v (fvunop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fneg_underscore v)"
	| fun_vunop__case_3 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_M_NEG) v (fvunop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fneg_underscore v)"
	| fun_vunop__case_4 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_M_SQRT) v (fvunop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fsqrt_underscore v)"
	| fun_vunop__case_5 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_M_SQRT) v (fvunop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fsqrt_underscore v)"
	| fun_vunop__case_6 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_M_CEIL) v (fvunop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fceil_underscore v)"
	| fun_vunop__case_7 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_M_CEIL) v (fvunop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fceil_underscore v)"
	| fun_vunop__case_8 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_M_FLOOR) v (fvunop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) ffloor_underscore v)"
	| fun_vunop__case_9 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_M_FLOOR) v (fvunop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) ffloor_underscore v)"
	| fun_vunop__case_10 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_M_TRUNC) v (fvunop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) ftrunc_underscore v)"
	| fun_vunop__case_11 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_M_TRUNC) v (fvunop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) ftrunc_underscore v)"
	| fun_vunop__case_12 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_M_NEAREST) v (fvunop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fnearest_underscore v)"
	| fun_vunop__case_13 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_M_NEAREST) v (fvunop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fnearest_underscore v)"
	| fun_vunop__case_14 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 M_0 vunop_Jnn_M_ABS) v (ivunop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) iabs_underscore v)"
	| fun_vunop__case_15 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 M_0 vunop_Jnn_M_ABS) v (ivunop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) iabs_underscore v)"
	| fun_vunop__case_16 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 M_0 vunop_Jnn_M_ABS) v (ivunop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) iabs_underscore v)"
	| fun_vunop__case_17 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 M_0 vunop_Jnn_M_ABS) v (ivunop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) iabs_underscore v)"
	| fun_vunop__case_18 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 M_0 vunop_Jnn_M_NEG) v (ivunop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) ineg_underscore v)"
	| fun_vunop__case_19 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 M_0 vunop_Jnn_M_NEG) v (ivunop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) ineg_underscore v)"
	| fun_vunop__case_20 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 M_0 vunop_Jnn_M_NEG) v (ivunop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) ineg_underscore v)"
	| fun_vunop__case_21 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 M_0 vunop_Jnn_M_NEG) v (ivunop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) ineg_underscore v)"
	| fun_vunop__case_22 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 M_0 vunop_Jnn_M_POPCNT) v (ivunop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) ipopcnt_underscore v)"
	| fun_vunop__case_23 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 M_0 vunop_Jnn_M_POPCNT) v (ivunop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) ipopcnt_underscore v)"
	| fun_vunop__case_24 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 M_0 vunop_Jnn_M_POPCNT) v (ivunop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) ipopcnt_underscore v)"
	| fun_vunop__case_25 :
		"(v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 M_0 vunop_Jnn_M_POPCNT) v (ivunop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) ipopcnt_underscore v)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:174.6-174.14 *)
inductive fun_vbinop_underscore :: "shape ⇒ vbinop_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ (vec_underscore list) ⇒ bool" where
	  fun_vbinop__case_0 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 vbinop_Jnn_M_ADD) v_1 v_2 (ivbinop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) iadd_underscore v_1 v_2)"
	| fun_vbinop__case_1 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 vbinop_Jnn_M_ADD) v_1 v_2 (ivbinop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) iadd_underscore v_1 v_2)"
	| fun_vbinop__case_2 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 vbinop_Jnn_M_ADD) v_1 v_2 (ivbinop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) iadd_underscore v_1 v_2)"
	| fun_vbinop__case_3 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 vbinop_Jnn_M_ADD) v_1 v_2 (ivbinop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) iadd_underscore v_1 v_2)"
	| fun_vbinop__case_4 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 vbinop_Jnn_M_SUB) v_1 v_2 (ivbinop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) isub_underscore v_1 v_2)"
	| fun_vbinop__case_5 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 vbinop_Jnn_M_SUB) v_1 v_2 (ivbinop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) isub_underscore v_1 v_2)"
	| fun_vbinop__case_6 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 vbinop_Jnn_M_SUB) v_1 v_2 (ivbinop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) isub_underscore v_1 v_2)"
	| fun_vbinop__case_7 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 vbinop_Jnn_M_SUB) v_1 v_2 (ivbinop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) isub_underscore v_1 v_2)"
	| fun_vbinop__case_8 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 vbinop_Jnn_M_MUL) v_1 v_2 (ivbinop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) imul_underscore v_1 v_2)"
	| fun_vbinop__case_9 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 vbinop_Jnn_M_MUL) v_1 v_2 (ivbinop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) imul_underscore v_1 v_2)"
	| fun_vbinop__case_10 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 vbinop_Jnn_M_MUL) v_1 v_2 (ivbinop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) imul_underscore v_1 v_2)"
	| fun_vbinop__case_11 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 vbinop_Jnn_M_MUL) v_1 v_2 (ivbinop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) imul_underscore v_1 v_2)"
	| fun_vbinop__case_12 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (ADD_SAT v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) iadd_sat_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_13 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (ADD_SAT v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) iadd_sat_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_14 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (ADD_SAT v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) iadd_sat_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_15 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (ADD_SAT v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) iadd_sat_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_16 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (SUB_SAT v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) isub_sat_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_17 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (SUB_SAT v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) isub_sat_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_18 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (SUB_SAT v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) isub_sat_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_19 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (SUB_SAT v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) isub_sat_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_20 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (vbinop_Jnn_M_MIN v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) imin_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_21 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (vbinop_Jnn_M_MIN v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) imin_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_22 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (vbinop_Jnn_M_MIN v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) imin_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_23 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (vbinop_Jnn_M_MIN v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) imin_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_24 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (vbinop_Jnn_M_MAX v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) imax_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_25 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (vbinop_Jnn_M_MAX v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) imax_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_26 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (vbinop_Jnn_M_MAX v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) imax_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_27 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (vbinop_Jnn_M_MAX v_sx)) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) imax_underscore v_sx v_1 v_2)"
	| fun_vbinop__case_28 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 AVGRU) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) iavgr_underscore U v_1 v_2)"
	| fun_vbinop__case_29 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 AVGRU) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) iavgr_underscore U v_1 v_2)"
	| fun_vbinop__case_30 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 AVGRU) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) iavgr_underscore U v_1 v_2)"
	| fun_vbinop__case_31 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 AVGRU) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) iavgr_underscore U v_1 v_2)"
	| fun_vbinop__case_32 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 Q15MULR_SATS) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) iq15mulr_sat_underscore S v_1 v_2)"
	| fun_vbinop__case_33 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 Q15MULR_SATS) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) iq15mulr_sat_underscore S v_1 v_2)"
	| fun_vbinop__case_34 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 Q15MULR_SATS) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) iq15mulr_sat_underscore S v_1 v_2)"
	| fun_vbinop__case_35 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 Q15MULR_SATS) v_1 v_2 (ivbinopsx_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) iq15mulr_sat_underscore S v_1 v_2)"
	| fun_vbinop__case_36 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 RELAXED_Q15MULRS) v_1 v_2 (ivbinopsxnd_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) irelaxed_q15mulr_underscore S v_1 v_2)"
	| fun_vbinop__case_37 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 RELAXED_Q15MULRS) v_1 v_2 (ivbinopsxnd_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) irelaxed_q15mulr_underscore S v_1 v_2)"
	| fun_vbinop__case_38 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 RELAXED_Q15MULRS) v_1 v_2 (ivbinopsxnd_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) irelaxed_q15mulr_underscore S v_1 v_2)"
	| fun_vbinop__case_39 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 RELAXED_Q15MULRS) v_1 v_2 (ivbinopsxnd_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) irelaxed_q15mulr_underscore S v_1 v_2)"
	| fun_vbinop__case_40 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_M_ADD) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fadd_underscore v_1 v_2)"
	| fun_vbinop__case_41 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_M_ADD) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fadd_underscore v_1 v_2)"
	| fun_vbinop__case_42 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_M_SUB) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fsub_underscore v_1 v_2)"
	| fun_vbinop__case_43 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_M_SUB) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fsub_underscore v_1 v_2)"
	| fun_vbinop__case_44 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_M_MUL) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fmul_underscore v_1 v_2)"
	| fun_vbinop__case_45 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_M_MUL) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fmul_underscore v_1 v_2)"
	| fun_vbinop__case_46 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_M_DIV) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fdiv_underscore v_1 v_2)"
	| fun_vbinop__case_47 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_M_DIV) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fdiv_underscore v_1 v_2)"
	| fun_vbinop__case_48 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_M_MIN) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fmin_underscore v_1 v_2)"
	| fun_vbinop__case_49 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_M_MIN) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fmin_underscore v_1 v_2)"
	| fun_vbinop__case_50 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_M_MAX) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fmax_underscore v_1 v_2)"
	| fun_vbinop__case_51 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_M_MAX) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fmax_underscore v_1 v_2)"
	| fun_vbinop__case_52 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 PMIN) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fpmin_underscore v_1 v_2)"
	| fun_vbinop__case_53 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 PMIN) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fpmin_underscore v_1 v_2)"
	| fun_vbinop__case_54 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 PMAX) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fpmax_underscore v_1 v_2)"
	| fun_vbinop__case_55 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 PMAX) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fpmax_underscore v_1 v_2)"
	| fun_vbinop__case_56 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 RELAXED_MIN) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) frelaxed_min_underscore v_1 v_2)"
	| fun_vbinop__case_57 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 RELAXED_MIN) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) frelaxed_min_underscore v_1 v_2)"
	| fun_vbinop__case_58 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 RELAXED_MAX) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) frelaxed_max_underscore v_1 v_2)"
	| fun_vbinop__case_59 :
		"(v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 RELAXED_MAX) v_1 v_2 (fvbinop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) frelaxed_max_underscore v_1 v_2)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:176.6-176.15 *)
inductive fun_vternop_underscore :: "shape ⇒ vternop_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ (vec_underscore list) ⇒ bool" where
	  fun_vternop__case_0 :
		"(v_M = M_0) ⟹
		 fun_vternop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vternop__0 Jnn_I32 M_0 RELAXED_LANESELECT) v_1 v_2 v_3 (ivternopnd_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) irelaxed_laneselect_underscore v_1 v_2 v_3)"
	| fun_vternop__case_1 :
		"(v_M = M_0) ⟹
		 fun_vternop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vternop__0 Jnn_I64 M_0 RELAXED_LANESELECT) v_1 v_2 v_3 (ivternopnd_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) irelaxed_laneselect_underscore v_1 v_2 v_3)"
	| fun_vternop__case_2 :
		"(v_M = M_0) ⟹
		 fun_vternop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vternop__0 Jnn_I8 M_0 RELAXED_LANESELECT) v_1 v_2 v_3 (ivternopnd_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) irelaxed_laneselect_underscore v_1 v_2 v_3)"
	| fun_vternop__case_3 :
		"(v_M = M_0) ⟹
		 fun_vternop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vternop__0 Jnn_I16 M_0 RELAXED_LANESELECT) v_1 v_2 v_3 (ivternopnd_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) irelaxed_laneselect_underscore v_1 v_2 v_3)"
	| fun_vternop__case_4 :
		"(v_M = M_0) ⟹
		 fun_vternop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vternop__1 Fnn_F32 M_0 RELAXED_MADD) v_1 v_2 v_3 (fvternop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) frelaxed_madd_underscore v_1 v_2 v_3)"
	| fun_vternop__case_5 :
		"(v_M = M_0) ⟹
		 fun_vternop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vternop__1 Fnn_F64 M_0 RELAXED_MADD) v_1 v_2 v_3 (fvternop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) frelaxed_madd_underscore v_1 v_2 v_3)"
	| fun_vternop__case_6 :
		"(v_M = M_0) ⟹
		 fun_vternop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vternop__1 Fnn_F32 M_0 RELAXED_NMADD) v_1 v_2 v_3 (fvternop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) frelaxed_nmadd_underscore v_1 v_2 v_3)"
	| fun_vternop__case_7 :
		"(v_M = M_0) ⟹
		 fun_vternop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vternop__1 Fnn_F64 M_0 RELAXED_NMADD) v_1 v_2 v_3 (fvternop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) frelaxed_nmadd_underscore v_1 v_2 v_3)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:178.6-178.14 *)
inductive fun_vrelop_underscore :: "shape ⇒ vrelop_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ bool" where
	  fun_vrelop__case_0 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 vrelop_Jnn_M_EQ) v_1 v_2 (ivrelop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) ieq_underscore v_1 v_2)"
	| fun_vrelop__case_1 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 vrelop_Jnn_M_EQ) v_1 v_2 (ivrelop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) ieq_underscore v_1 v_2)"
	| fun_vrelop__case_2 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 vrelop_Jnn_M_EQ) v_1 v_2 (ivrelop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) ieq_underscore v_1 v_2)"
	| fun_vrelop__case_3 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 vrelop_Jnn_M_EQ) v_1 v_2 (ivrelop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) ieq_underscore v_1 v_2)"
	| fun_vrelop__case_4 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 vrelop_Jnn_M_NE) v_1 v_2 (ivrelop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) ine_underscore v_1 v_2)"
	| fun_vrelop__case_5 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 vrelop_Jnn_M_NE) v_1 v_2 (ivrelop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) ine_underscore v_1 v_2)"
	| fun_vrelop__case_6 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 vrelop_Jnn_M_NE) v_1 v_2 (ivrelop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) ine_underscore v_1 v_2)"
	| fun_vrelop__case_7 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 vrelop_Jnn_M_NE) v_1 v_2 (ivrelop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) ine_underscore v_1 v_2)"
	| fun_vrelop__case_8 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_M_LT v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) ilt_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_9 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_M_LT v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) ilt_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_10 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_M_LT v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) ilt_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_11 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_M_LT v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) ilt_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_12 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_M_GT v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) igt_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_13 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_M_GT v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) igt_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_14 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_M_GT v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) igt_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_15 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_M_GT v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) igt_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_16 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_M_LE v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) ile_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_17 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_M_LE v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) ile_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_18 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_M_LE v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) ile_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_19 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_M_LE v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) ile_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_20 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_M_GE v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) ige_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_21 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_M_GE v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) ige_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_22 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_M_GE v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) ige_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_23 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_M_GE v_sx)) v_1 v_2 (ivrelopsx_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) ige_underscore v_sx v_1 v_2)"
	| fun_vrelop__case_24 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_M_EQ) v_1 v_2 (fvrelop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) feq_underscore v_1 v_2)"
	| fun_vrelop__case_25 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_M_EQ) v_1 v_2 (fvrelop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) feq_underscore v_1 v_2)"
	| fun_vrelop__case_26 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_M_NE) v_1 v_2 (fvrelop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fne_underscore v_1 v_2)"
	| fun_vrelop__case_27 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_M_NE) v_1 v_2 (fvrelop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fne_underscore v_1 v_2)"
	| fun_vrelop__case_28 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_M_LT) v_1 v_2 (fvrelop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) flt_underscore v_1 v_2)"
	| fun_vrelop__case_29 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_M_LT) v_1 v_2 (fvrelop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) flt_underscore v_1 v_2)"
	| fun_vrelop__case_30 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_M_GT) v_1 v_2 (fvrelop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fgt_underscore v_1 v_2)"
	| fun_vrelop__case_31 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_M_GT) v_1 v_2 (fvrelop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fgt_underscore v_1 v_2)"
	| fun_vrelop__case_32 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_M_LE) v_1 v_2 (fvrelop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fle_underscore v_1 v_2)"
	| fun_vrelop__case_33 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_M_LE) v_1 v_2 (fvrelop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fle_underscore v_1 v_2)"
	| fun_vrelop__case_34 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_M_GE) v_1 v_2 (fvrelop_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) fge_underscore v_1 v_2)"
	| fun_vrelop__case_35 :
		"(v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_M_GE) v_1 v_2 (fvrelop_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) fge_underscore v_1 v_2)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:181.6-181.15 *)
inductive fun_lcvtop__underscore :: "shape ⇒ shape ⇒ vcvtop__underscore ⇒ lane_underscore ⇒ (lane_underscore list) ⇒ bool" where
	  fun_lcvtop___case_0 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I32)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I32 M_1_0 Jnn_I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I32 c_1) [(mk_lane__2 Jnn_I32 c)]"
	| fun_lcvtop___case_1 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I32)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I64 M_1_0 Jnn_I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I64 c_1) [(mk_lane__2 Jnn_I32 c)]"
	| fun_lcvtop___case_2 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I32)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I8 M_1_0 Jnn_I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I8 c_1) [(mk_lane__2 Jnn_I32 c)]"
	| fun_lcvtop___case_3 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I32)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I16 M_1_0 Jnn_I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I16 c_1) [(mk_lane__2 Jnn_I32 c)]"
	| fun_lcvtop___case_4 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I64)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I32 M_1_0 Jnn_I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I32 c_1) [(mk_lane__2 Jnn_I64 c)]"
	| fun_lcvtop___case_5 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I64)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I64 M_1_0 Jnn_I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I64 c_1) [(mk_lane__2 Jnn_I64 c)]"
	| fun_lcvtop___case_6 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I64)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I8 M_1_0 Jnn_I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I8 c_1) [(mk_lane__2 Jnn_I64 c)]"
	| fun_lcvtop___case_7 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I64)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I16 M_1_0 Jnn_I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I16 c_1) [(mk_lane__2 Jnn_I64 c)]"
	| fun_lcvtop___case_8 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I8)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I32 M_1_0 Jnn_I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I32 c_1) [(mk_lane__2 Jnn_I8 c)]"
	| fun_lcvtop___case_9 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I8)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I64 M_1_0 Jnn_I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I64 c_1) [(mk_lane__2 Jnn_I8 c)]"
	| fun_lcvtop___case_10 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I8)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I8 M_1_0 Jnn_I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I8 c_1) [(mk_lane__2 Jnn_I8 c)]"
	| fun_lcvtop___case_11 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I8)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I16 M_1_0 Jnn_I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I16 c_1) [(mk_lane__2 Jnn_I8 c)]"
	| fun_lcvtop___case_12 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I16)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I32 M_1_0 Jnn_I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I32 c_1) [(mk_lane__2 Jnn_I16 c)]"
	| fun_lcvtop___case_13 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I16)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I64 M_1_0 Jnn_I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I64 c_1) [(mk_lane__2 Jnn_I16 c)]"
	| fun_lcvtop___case_14 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I16)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I8 M_1_0 Jnn_I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I8 c_1) [(mk_lane__2 Jnn_I16 c)]"
	| fun_lcvtop___case_15 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I16)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx c_1)) ⟹
		 (c = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (mk_vcvtop___0 Jnn_I16 M_1_0 Jnn_I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2_EXTEND v_half v_sx)) (mk_lane__2 Jnn_I16 c_1) [(mk_lane__2 Jnn_I16 c)]"
	| fun_lcvtop___case_16 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx c_1)) ⟹
		 (c = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I32 M_1_0 Fnn_F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) (mk_lane__2 Jnn_I32 c_1) [(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 c))]"
	| fun_lcvtop___case_17 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx c_1)) ⟹
		 (c = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I64 M_1_0 Fnn_F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) (mk_lane__2 Jnn_I64 c_1) [(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 c))]"
	| fun_lcvtop___case_18 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx c_1)) ⟹
		 (c = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I8 M_1_0 Fnn_F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) (mk_lane__2 Jnn_I8 c_1) [(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 c))]"
	| fun_lcvtop___case_19 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx c_1)) ⟹
		 (c = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I16 M_1_0 Fnn_F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) (mk_lane__2 Jnn_I16 c_1) [(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 c))]"
	| fun_lcvtop___case_20 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx c_1)) ⟹
		 (c = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I32 M_1_0 Fnn_F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) (mk_lane__2 Jnn_I32 c_1) [(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 c))]"
	| fun_lcvtop___case_21 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx c_1)) ⟹
		 (c = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I64 M_1_0 Fnn_F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) (mk_lane__2 Jnn_I64 c_1) [(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 c))]"
	| fun_lcvtop___case_22 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx c_1)) ⟹
		 (c = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I8 M_1_0 Fnn_F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) (mk_lane__2 Jnn_I8 c_1) [(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 c))]"
	| fun_lcvtop___case_23 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx c_1)) ⟹
		 (c = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___1 Jnn_I16 M_1_0 Fnn_F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2_CONVERT half_opt v_sx)) (mk_lane__2 Jnn_I16 c_1) [(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 c))]"
	| fun_lcvtop___case_24 :
		"list_all (λ (iter_147 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_147)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_108 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_108))) c_opt))"
	| fun_lcvtop___case_25 :
		"list_all (λ (iter_148 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_148)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_110 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_110))) c_opt))"
	| fun_lcvtop___case_26 :
		"list_all (λ (iter_149 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_149)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_112 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_112))) c_opt))"
	| fun_lcvtop___case_27 :
		"list_all (λ (iter_150 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_150)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_114 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_114))) c_opt))"
	| fun_lcvtop___case_28 :
		"list_all (λ (iter_151 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_151)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_116 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_116))) c_opt))"
	| fun_lcvtop___case_29 :
		"list_all (λ (iter_152 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_152)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_118 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_118))) c_opt))"
	| fun_lcvtop___case_30 :
		"list_all (λ (iter_153 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_153)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_120 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_120))) c_opt))"
	| fun_lcvtop___case_31 :
		"list_all (λ (iter_154 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_154)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_122 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_122))) c_opt))"
	| fun_lcvtop___case_32 :
		"list_all (λ (iter_155 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_155)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_124 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_124))) c_opt))"
	| fun_lcvtop___case_33 :
		"list_all (λ (iter_156 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_156)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_126 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_126))) c_opt))"
	| fun_lcvtop___case_34 :
		"list_all (λ (iter_157 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_157)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_128 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_128))) c_opt))"
	| fun_lcvtop___case_35 :
		"list_all (λ (iter_158 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_158)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_130 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_130))) c_opt))"
	| fun_lcvtop___case_36 :
		"list_all (λ (iter_159 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_159)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_132 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_132))) c_opt))"
	| fun_lcvtop___case_37 :
		"list_all (λ (iter_160 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_160)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_134 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_134))) c_opt))"
	| fun_lcvtop___case_38 :
		"list_all (λ (iter_161 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_161)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_136 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_136))) c_opt))"
	| fun_lcvtop___case_39 :
		"list_all (λ (iter_162 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_162)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2_TRUNC_SAT v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_138 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_138))) c_opt))"
	| fun_lcvtop___case_40 :
		"list_all (λ (iter_163 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_163)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I32 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_140 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_140))) c_opt))"
	| fun_lcvtop___case_41 :
		"list_all (λ (iter_164 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_164)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I32 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_142 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_142))) c_opt))"
	| fun_lcvtop___case_42 :
		"list_all (λ (iter_165 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_165)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I32 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_144 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_144))) c_opt))"
	| fun_lcvtop___case_43 :
		"list_all (λ (iter_166 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_166)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I32 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_146 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_146))) c_opt))"
	| fun_lcvtop___case_44 :
		"list_all (λ (iter_167 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_167)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I64 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_148 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_148))) c_opt))"
	| fun_lcvtop___case_45 :
		"list_all (λ (iter_168 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_168)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I64 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_150 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_150))) c_opt))"
	| fun_lcvtop___case_46 :
		"list_all (λ (iter_169 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_169)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I64 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_152 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_152))) c_opt))"
	| fun_lcvtop___case_47 :
		"list_all (λ (iter_170 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_170)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F32 M_1_0 Jnn_I64 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (option_to_list (map_option (λ (c_154 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_154))) c_opt))"
	| fun_lcvtop___case_48 :
		"list_all (λ (iter_171 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_171)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I32 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_156 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_156))) c_opt))"
	| fun_lcvtop___case_49 :
		"list_all (λ (iter_172 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_172)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I32 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_158 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_158))) c_opt))"
	| fun_lcvtop___case_50 :
		"list_all (λ (iter_173 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_173)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I32 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_160 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_160))) c_opt))"
	| fun_lcvtop___case_51 :
		"list_all (λ (iter_174 :: iN). (wf_uN (size (numtype_addrtype I32)) iter_174)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I32)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I32 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_162 :: iN). (mk_lane__0 (numtype_addrtype I32) (mk_num__0 I32 c_162))) c_opt))"
	| fun_lcvtop___case_52 :
		"list_all (λ (iter_175 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_175)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I64 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_164 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_164))) c_opt))"
	| fun_lcvtop___case_53 :
		"list_all (λ (iter_176 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_176)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I64 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_166 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_166))) c_opt))"
	| fun_lcvtop___case_54 :
		"list_all (λ (iter_177 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_177)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I64 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_168 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_168))) c_opt))"
	| fun_lcvtop___case_55 :
		"list_all (λ (iter_178 :: iN). (wf_uN (size (numtype_addrtype I64)) iter_178)) (option_to_list (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (c_opt = (relaxed_trunc__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_addrtype I64)) v_sx c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (mk_vcvtop___2 Fnn_F64 M_1_0 Jnn_I64 M_2_0 (RELAXED_TRUNC v_sx zero_opt)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (option_to_list (map_option (λ (c_170 :: iN). (mk_lane__0 (numtype_addrtype I64) (mk_num__0 I64 c_170))) c_opt))"
	| fun_lcvtop___case_56 :
		"list_all (λ (iter_179 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_179)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1) ⟹
		 (c_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F32 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE ZERO)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (map (λ (c_172 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 c_172))) c_lst)"
	| fun_lcvtop___case_57 :
		"list_all (λ (iter_180 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_180)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1) ⟹
		 (c_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F32 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE ZERO)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (map (λ (c_174 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 c_174))) c_lst)"
	| fun_lcvtop___case_58 :
		"list_all (λ (iter_181 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_181)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1) ⟹
		 (c_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F64 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE ZERO)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (map (λ (c_176 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 c_176))) c_lst)"
	| fun_lcvtop___case_59 :
		"list_all (λ (iter_182 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_182)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1) ⟹
		 (c_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F64 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE ZERO)) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (map (λ (c_178 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 c_178))) c_lst)"
	| fun_lcvtop___case_60 :
		"list_all (λ (iter_183 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_183)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1) ⟹
		 (c_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F32 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE ZERO)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (map (λ (c_180 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 c_180))) c_lst)"
	| fun_lcvtop___case_61 :
		"list_all (λ (iter_184 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_184)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1) ⟹
		 (c_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F32 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE ZERO)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (map (λ (c_182 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 c_182))) c_lst)"
	| fun_lcvtop___case_62 :
		"list_all (λ (iter_185 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_185)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1) ⟹
		 (c_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F64 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE ZERO)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (map (λ (c_184 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 c_184))) c_lst)"
	| fun_lcvtop___case_63 :
		"list_all (λ (iter_186 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_186)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1) ⟹
		 (c_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F64 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2_DEMOTE ZERO)) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (map (λ (c_186 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 c_186))) c_lst)"
	| fun_lcvtop___case_64 :
		"list_all (λ (iter_187 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_187)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1) ⟹
		 (c_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F32 M_2_0 PROMOTELOW) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (map (λ (c_188 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 c_188))) c_lst)"
	| fun_lcvtop___case_65 :
		"list_all (λ (iter_188 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_188)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1) ⟹
		 (c_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F32 M_2_0 PROMOTELOW) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (map (λ (c_190 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 c_190))) c_lst)"
	| fun_lcvtop___case_66 :
		"list_all (λ (iter_189 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_189)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1) ⟹
		 (c_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F64 M_2_0 PROMOTELOW) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (map (λ (c_192 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 c_192))) c_lst)"
	| fun_lcvtop___case_67 :
		"list_all (λ (iter_190 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_190)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1) ⟹
		 (c_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F32 M_1_0 Fnn_F64 M_2_0 PROMOTELOW) (mk_lane__0 F32 (mk_num__1 Fnn_F32 c_1)) (map (λ (c_194 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 c_194))) c_lst)"
	| fun_lcvtop___case_68 :
		"list_all (λ (iter_191 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_191)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1) ⟹
		 (c_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F32 M_2_0 PROMOTELOW) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (map (λ (c_196 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 c_196))) c_lst)"
	| fun_lcvtop___case_69 :
		"list_all (λ (iter_192 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_192)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1) ⟹
		 (c_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F32 M_2_0 PROMOTELOW) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (map (λ (c_198 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 c_198))) c_lst)"
	| fun_lcvtop___case_70 :
		"list_all (λ (iter_193 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_193)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1) ⟹
		 (c_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F64 M_2_0 PROMOTELOW) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (map (λ (c_200 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 c_200))) c_lst)"
	| fun_lcvtop___case_71 :
		"list_all (λ (iter_194 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_194)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1) ⟹
		 (c_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) c_1)) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_lcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (mk_vcvtop___3 Fnn_F64 M_1_0 Fnn_F64 M_2_0 PROMOTELOW) (mk_lane__0 F64 (mk_num__1 Fnn_F64 c_1)) (map (λ (c_202 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 c_202))) c_lst)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:183.6-183.15 *)
inductive fun_vcvtop__underscore :: "shape ⇒ shape ⇒ vcvtop__underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ bool" where
	  fun_vcvtop___case_0 :
		"(fun_zeroop (X Lnn_1 (mk_dim v_M)) (X Lnn_2 (mk_dim v_M)) vcvtop var_2) ⟹
		 (fun_halfop (X Lnn_1 (mk_dim v_M)) (X Lnn_2 (mk_dim v_M)) vcvtop var_1) ⟹
		 ((length var_0_lst) = (length c_1_lst)) ⟹
		 list_all2 (λ (var_0 :: (lane_underscore list)) (c_1 :: lane_underscore). (fun_lcvtop__underscore (X Lnn_1 (mk_dim v_M)) (X Lnn_2 (mk_dim v_M)) vcvtop c_1 var_0)) var_0_lst c_1_lst ⟹
		 list_all (λ (c_1 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X Lnn_1 (mk_dim v_M))) c_1)) c_1_lst ⟹
		 list_all (λ (c_lst :: (lane_underscore list)). list_all (λ (c :: lane_underscore). (wf_lane_underscore Lnn_2 c)) c_lst) c_lst_lst ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X Lnn_1 (mk_dim v_M))) iter)) (lanes_underscore (X Lnn_1 (mk_dim v_M)) v_1) ⟹
		 list_all (λ (iter :: (lane_underscore list)). list_all (λ (iter :: lane_underscore). (wf_lane_underscore Lnn_2 iter)) iter) (setproduct_underscore  var_0_lst) ⟹
		 list_all (λ (var_0 :: (lane_underscore list)). list_all (λ (iter :: lane_underscore). (wf_lane_underscore Lnn_2 iter)) var_0) var_0_lst ⟹
		 list_all (λ (c_lst :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X Lnn_2 (mk_dim v_M)) c_lst))) c_lst_lst ⟹
		 (wf_shape (X Lnn_1 (mk_dim v_M))) ⟹
		 (wf_shape (X Lnn_2 (mk_dim v_M))) ⟹
		 ((var_1 = None) ∧ (var_2 = None)) ⟹
		 (c_1_lst = (lanes_underscore (X Lnn_1 (mk_dim v_M)) v_1)) ⟹
		 (c_lst_lst = (setproduct_underscore  var_0_lst)) ⟹
		 ((length (map (λ (c_lst :: (lane_underscore list)). (inv_lanes_underscore (X Lnn_2 (mk_dim v_M)) c_lst)) c_lst_lst)) > 0) ⟹
		 (v ∈ set (map (λ (c_lst :: (lane_underscore list)). (inv_lanes_underscore (X Lnn_2 (mk_dim v_M)) c_lst)) c_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vcvtop__underscore (X Lnn_1 (mk_dim v_M)) (X Lnn_2 (mk_dim M_0)) vcvtop v_1 v"
	| fun_vcvtop___case_1 :
		"(fun_halfop (X Lnn_1 (mk_dim M_1)) (X Lnn_2 (mk_dim M_2)) vcvtop var_1) ⟹
		 ((length var_0_lst) = (length c_1_lst)) ⟹
		 list_all2 (λ (var_0 :: (lane_underscore list)) (c_1 :: lane_underscore). (fun_lcvtop__underscore (X Lnn_1 (mk_dim M_1)) (X Lnn_2 (mk_dim M_2)) vcvtop c_1 var_0)) var_0_lst c_1_lst ⟹
		 list_all (λ (c_1 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X Lnn_1 (mk_dim M_1))) c_1)) c_1_lst ⟹
		 list_all (λ (c_lst :: (lane_underscore list)). list_all (λ (c :: lane_underscore). (wf_lane_underscore Lnn_2 c)) c_lst) c_lst_lst ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X Lnn_1 (mk_dim M_1))) iter)) (lanes_underscore (X Lnn_1 (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter :: (lane_underscore list)). list_all (λ (iter :: lane_underscore). (wf_lane_underscore Lnn_2 iter)) iter) (setproduct_underscore  var_0_lst) ⟹
		 list_all (λ (var_0 :: (lane_underscore list)). list_all (λ (iter :: lane_underscore). (wf_lane_underscore Lnn_2 iter)) var_0) var_0_lst ⟹
		 list_all (λ (c_lst :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X Lnn_2 (mk_dim M_2)) c_lst))) c_lst_lst ⟹
		 (wf_shape (X Lnn_1 (mk_dim M_1))) ⟹
		 (wf_shape (X Lnn_2 (mk_dim M_2))) ⟹
		 (var_1 = (Some v_half)) ⟹
		 (c_1_lst = (list_slice (lanes_underscore (X Lnn_1 (mk_dim M_1)) v_1) (fun_half v_half 0 M_2) M_2)) ⟹
		 (c_lst_lst = (setproduct_underscore  var_0_lst)) ⟹
		 ((length (map (λ (c_lst :: (lane_underscore list)). (inv_lanes_underscore (X Lnn_2 (mk_dim M_2)) c_lst)) c_lst_lst)) > 0) ⟹
		 (v ∈ set (map (λ (c_lst :: (lane_underscore list)). (inv_lanes_underscore (X Lnn_2 (mk_dim M_2)) c_lst)) c_lst_lst)) ⟹
		 fun_vcvtop__underscore (X Lnn_1 (mk_dim M_1)) (X Lnn_2 (mk_dim M_2)) vcvtop v_1 v"
	| fun_vcvtop___case_2 :
		"(fun_zeroop (X Lnn_1 (mk_dim M_1)) (X Lnn_2 (mk_dim M_2)) vcvtop var_1) ⟹
		 ((length var_0_lst) = (length c_1_lst)) ⟹
		 list_all2 (λ (var_0 :: (lane_underscore list)) (c_1 :: lane_underscore). (fun_lcvtop__underscore (X Lnn_1 (mk_dim M_1)) (X Lnn_2 (mk_dim M_2)) vcvtop c_1 var_0)) var_0_lst c_1_lst ⟹
		 list_all (λ (c_1 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X Lnn_1 (mk_dim M_1))) c_1)) c_1_lst ⟹
		 list_all (λ (c_lst :: (lane_underscore list)). list_all (λ (c :: lane_underscore). (wf_lane_underscore Lnn_2 c)) c_lst) c_lst_lst ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X Lnn_1 (mk_dim M_1))) iter)) (lanes_underscore (X Lnn_1 (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter :: (lane_underscore list)). list_all (λ (iter :: lane_underscore). (wf_lane_underscore Lnn_2 iter)) iter) (setproduct_underscore  (var_0_lst @ (repeat M_1 [(fun_zero Lnn_2)]))) ⟹
		 list_all (λ (var_0 :: (lane_underscore list)). list_all (λ (iter :: lane_underscore). (wf_lane_underscore Lnn_2 iter)) var_0) var_0_lst ⟹
		 (wf_lane_underscore Lnn_2 (fun_zero Lnn_2)) ⟹
		 list_all (λ (c_lst :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X Lnn_2 (mk_dim M_2)) c_lst))) c_lst_lst ⟹
		 (wf_shape (X Lnn_1 (mk_dim M_1))) ⟹
		 (wf_shape (X Lnn_2 (mk_dim M_2))) ⟹
		 (var_1 = (Some ZERO)) ⟹
		 (c_1_lst = (lanes_underscore (X Lnn_1 (mk_dim M_1)) v_1)) ⟹
		 (c_lst_lst = (setproduct_underscore  (var_0_lst @ (repeat M_1 [(fun_zero Lnn_2)])))) ⟹
		 ((length (map (λ (c_lst :: (lane_underscore list)). (inv_lanes_underscore (X Lnn_2 (mk_dim M_2)) c_lst)) c_lst_lst)) > 0) ⟹
		 (v ∈ set (map (λ (c_lst :: (lane_underscore list)). (inv_lanes_underscore (X Lnn_2 (mk_dim M_2)) c_lst)) c_lst_lst)) ⟹
		 fun_vcvtop__underscore (X Lnn_1 (mk_dim M_1)) (X Lnn_2 (mk_dim M_2)) vcvtop v_1 v"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:186.6-186.16 *)
inductive fun_vshiftop_underscore :: "ishape ⇒ vshiftop_underscore ⇒ vec_underscore ⇒ u32 ⇒ vec_underscore ⇒ bool" where
	  fun_vshiftop__case_0 :
		"(v_M = M_0) ⟹
		 fun_vshiftop_underscore (mk_ishape (X lanetype_I32 (mk_dim v_M))) (mk_vshiftop__0 Jnn_I32 M_0 vshiftop_Jnn_M_SHL) v i (ivshiftop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) ishl_underscore v i)"
	| fun_vshiftop__case_1 :
		"(v_M = M_0) ⟹
		 fun_vshiftop_underscore (mk_ishape (X lanetype_I64 (mk_dim v_M))) (mk_vshiftop__0 Jnn_I64 M_0 vshiftop_Jnn_M_SHL) v i (ivshiftop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) ishl_underscore v i)"
	| fun_vshiftop__case_2 :
		"(v_M = M_0) ⟹
		 fun_vshiftop_underscore (mk_ishape (X lanetype_I8 (mk_dim v_M))) (mk_vshiftop__0 Jnn_I8 M_0 vshiftop_Jnn_M_SHL) v i (ivshiftop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) ishl_underscore v i)"
	| fun_vshiftop__case_3 :
		"(v_M = M_0) ⟹
		 fun_vshiftop_underscore (mk_ishape (X lanetype_I16 (mk_dim v_M))) (mk_vshiftop__0 Jnn_I16 M_0 vshiftop_Jnn_M_SHL) v i (ivshiftop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) ishl_underscore v i)"
	| fun_vshiftop__case_4 :
		"(v_M = M_0) ⟹
		 fun_vshiftop_underscore (mk_ishape (X lanetype_I32 (mk_dim v_M))) (mk_vshiftop__0 Jnn_I32 M_0 (vshiftop_Jnn_M_SHR v_sx)) v i (ivshiftopsx_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) ishr_underscore v_sx v i)"
	| fun_vshiftop__case_5 :
		"(v_M = M_0) ⟹
		 fun_vshiftop_underscore (mk_ishape (X lanetype_I64 (mk_dim v_M))) (mk_vshiftop__0 Jnn_I64 M_0 (vshiftop_Jnn_M_SHR v_sx)) v i (ivshiftopsx_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) ishr_underscore v_sx v i)"
	| fun_vshiftop__case_6 :
		"(v_M = M_0) ⟹
		 fun_vshiftop_underscore (mk_ishape (X lanetype_I8 (mk_dim v_M))) (mk_vshiftop__0 Jnn_I8 M_0 (vshiftop_Jnn_M_SHR v_sx)) v i (ivshiftopsx_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) ishr_underscore v_sx v i)"
	| fun_vshiftop__case_7 :
		"(v_M = M_0) ⟹
		 fun_vshiftop_underscore (mk_ishape (X lanetype_I16 (mk_dim v_M))) (mk_vshiftop__0 Jnn_I16 M_0 (vshiftop_Jnn_M_SHR v_sx)) v i (ivshiftopsx_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) ishr_underscore v_sx v i)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:188.6-188.18 *)
inductive fun_vbitmaskop_underscore :: "ishape ⇒ vec_underscore ⇒ u32 ⇒ bool" where
	  fun_vbitmaskop__case_0 :
		"(fun_ivbitmaskop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v var_0) ⟹
		 fun_vbitmaskop_underscore (mk_ishape (X lanetype_I32 (mk_dim v_M))) v var_0"
	| fun_vbitmaskop__case_1 :
		"(fun_ivbitmaskop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v var_0) ⟹
		 fun_vbitmaskop_underscore (mk_ishape (X lanetype_I64 (mk_dim v_M))) v var_0"
	| fun_vbitmaskop__case_2 :
		"(fun_ivbitmaskop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v var_0) ⟹
		 fun_vbitmaskop_underscore (mk_ishape (X lanetype_I8 (mk_dim v_M))) v var_0"
	| fun_vbitmaskop__case_3 :
		"(fun_ivbitmaskop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v var_0) ⟹
		 fun_vbitmaskop_underscore (mk_ishape (X lanetype_I16 (mk_dim v_M))) v var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:190.6-190.17 *)
inductive fun_vswizzlop_underscore :: "bshape ⇒ vswizzlop_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ bool" where
	  fun_vswizzlop__case_0 :
		"(v_M = M_0) ⟹
		 fun_vswizzlop_underscore (mk_bshape (X lanetype_I8 (mk_dim v_M))) (mk_vswizzlop__0 M_0 SWIZZLE) v_1 v_2 (ivswizzlop_underscore (X lanetype_I8 (mk_dim v_M)) iswizzle_lane_underscore v_1 v_2)"
	| fun_vswizzlop__case_1 :
		"(v_M = M_0) ⟹
		 fun_vswizzlop_underscore (mk_bshape (X lanetype_I8 (mk_dim v_M))) (mk_vswizzlop__0 M_0 RELAXED_SWIZZLE) v_1 v_2 (ivswizzlop_underscore (X lanetype_I8 (mk_dim v_M)) irelaxed_swizzle_lane_underscore v_1 v_2)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:192.6-192.17 *)
inductive fun_vshufflop_underscore :: "bshape ⇒ (laneidx list) ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ bool" where
	  fun_vshufflop__case_0 :
		"(fun_ivshufflop_underscore (X lanetype_I8 (mk_dim v_M)) i_lst v_1 v_2 var_0) ⟹
		 fun_vshufflop_underscore (mk_bshape (X lanetype_I8 (mk_dim v_M))) i_lst v_1 v_2 var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:195.6-195.18 *)
inductive fun_vnarrowop__underscore :: "shape ⇒ shape ⇒ sx ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ bool" where
	  fun_vnarrowop___case_0 :
		"list_all (λ (c_1_231 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) c_1_231)) c_1_lst ⟹
		 list_all (λ (c_2_161 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) c_2_161)) c_2_lst ⟹
		 list_all (λ (iter_195 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) iter_195)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_196 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) iter_196)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_232 :: lane_underscore). ((proj_lane__2 c_1_232) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_232 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I32)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_1_232)))))) c_1_lst ⟹
		 list_all (λ (c_2_162 :: lane_underscore). ((proj_lane__2 c_2_162) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_162 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I32)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_2_162)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ((map (λ (c'_1_1 :: iN). (mk_lane__2 Jnn_I32 c'_1_1)) c'_1_lst) @ (map (λ (c'_2_1 :: iN). (mk_lane__2 Jnn_I32 c'_2_1)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_2 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_lane__2 Jnn_I32 c'_1_2))) c'_1_lst ⟹
		 list_all (λ (c'_2_2 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_lane__2 Jnn_I32 c'_2_2))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_234 :: lane_underscore). ((proj_lane__2 c_1_234) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_234 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_1_234))))) c_1_lst)) ⟹
		 list_all (λ (c_2_164 :: lane_underscore). ((proj_lane__2 c_2_164) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_164 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_2_164))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ((map (λ (c'_1_4 :: iN). (mk_lane__2 Jnn_I32 c'_1_4)) c'_1_lst) @ (map (λ (c'_2_4 :: iN). (mk_lane__2 Jnn_I32 c'_2_4)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_1 :
		"list_all (λ (c_1_235 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) c_1_235)) c_1_lst ⟹
		 list_all (λ (c_2_165 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) c_2_165)) c_2_lst ⟹
		 list_all (λ (iter_197 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) iter_197)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_198 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) iter_198)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_236 :: lane_underscore). ((proj_lane__2 c_1_236) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_236 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I32)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_1_236)))))) c_1_lst ⟹
		 list_all (λ (c_2_166 :: lane_underscore). ((proj_lane__2 c_2_166) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_166 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I32)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_2_166)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ((map (λ (c'_1_5 :: iN). (mk_lane__2 Jnn_I32 c'_1_5)) c'_1_lst) @ (map (λ (c'_2_5 :: iN). (mk_lane__2 Jnn_I32 c'_2_5)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_6 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_lane__2 Jnn_I32 c'_1_6))) c'_1_lst ⟹
		 list_all (λ (c'_2_6 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_lane__2 Jnn_I32 c'_2_6))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_238 :: lane_underscore). ((proj_lane__2 c_1_238) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_238 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_1_238))))) c_1_lst)) ⟹
		 list_all (λ (c_2_168 :: lane_underscore). ((proj_lane__2 c_2_168) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_168 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_2_168))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ((map (λ (c'_1_8 :: iN). (mk_lane__2 Jnn_I32 c'_1_8)) c'_1_lst) @ (map (λ (c'_2_8 :: iN). (mk_lane__2 Jnn_I32 c'_2_8)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_2 :
		"list_all (λ (c_1_239 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) c_1_239)) c_1_lst ⟹
		 list_all (λ (c_2_169 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) c_2_169)) c_2_lst ⟹
		 list_all (λ (iter_199 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) iter_199)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_200 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) iter_200)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_240 :: lane_underscore). ((proj_lane__2 c_1_240) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_240 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I32)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_1_240)))))) c_1_lst ⟹
		 list_all (λ (c_2_170 :: lane_underscore). ((proj_lane__2 c_2_170) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_170 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I32)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_2_170)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ((map (λ (c'_1_9 :: iN). (mk_lane__2 Jnn_I32 c'_1_9)) c'_1_lst) @ (map (λ (c'_2_9 :: iN). (mk_lane__2 Jnn_I32 c'_2_9)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_10 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_lane__2 Jnn_I32 c'_1_10))) c'_1_lst ⟹
		 list_all (λ (c'_2_10 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_lane__2 Jnn_I32 c'_2_10))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_242 :: lane_underscore). ((proj_lane__2 c_1_242) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_242 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_1_242))))) c_1_lst)) ⟹
		 list_all (λ (c_2_172 :: lane_underscore). ((proj_lane__2 c_2_172) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_172 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_2_172))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ((map (λ (c'_1_12 :: iN). (mk_lane__2 Jnn_I32 c'_1_12)) c'_1_lst) @ (map (λ (c'_2_12 :: iN). (mk_lane__2 Jnn_I32 c'_2_12)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_3 :
		"list_all (λ (c_1_243 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) c_1_243)) c_1_lst ⟹
		 list_all (λ (c_2_173 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) c_2_173)) c_2_lst ⟹
		 list_all (λ (iter_201 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) iter_201)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_202 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) iter_202)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_244 :: lane_underscore). ((proj_lane__2 c_1_244) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_244 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I32)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_1_244)))))) c_1_lst ⟹
		 list_all (λ (c_2_174 :: lane_underscore). ((proj_lane__2 c_2_174) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_174 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I32)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_2_174)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ((map (λ (c'_1_13 :: iN). (mk_lane__2 Jnn_I32 c'_1_13)) c'_1_lst) @ (map (λ (c'_2_13 :: iN). (mk_lane__2 Jnn_I32 c'_2_13)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_14 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_lane__2 Jnn_I32 c'_1_14))) c'_1_lst ⟹
		 list_all (λ (c'_2_14 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_lane__2 Jnn_I32 c'_2_14))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_246 :: lane_underscore). ((proj_lane__2 c_1_246) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_246 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_1_246))))) c_1_lst)) ⟹
		 list_all (λ (c_2_176 :: lane_underscore). ((proj_lane__2 c_2_176) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_176 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 c_2_176))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ((map (λ (c'_1_16 :: iN). (mk_lane__2 Jnn_I32 c'_1_16)) c'_1_lst) @ (map (λ (c'_2_16 :: iN). (mk_lane__2 Jnn_I32 c'_2_16)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_4 :
		"list_all (λ (c_1_247 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) c_1_247)) c_1_lst ⟹
		 list_all (λ (c_2_177 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) c_2_177)) c_2_lst ⟹
		 list_all (λ (iter_203 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) iter_203)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_204 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) iter_204)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_248 :: lane_underscore). ((proj_lane__2 c_1_248) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_248 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I64)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_1_248)))))) c_1_lst ⟹
		 list_all (λ (c_2_178 :: lane_underscore). ((proj_lane__2 c_2_178) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_178 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I64)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_2_178)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ((map (λ (c'_1_17 :: iN). (mk_lane__2 Jnn_I64 c'_1_17)) c'_1_lst) @ (map (λ (c'_2_17 :: iN). (mk_lane__2 Jnn_I64 c'_2_17)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_18 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_lane__2 Jnn_I64 c'_1_18))) c'_1_lst ⟹
		 list_all (λ (c'_2_18 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_lane__2 Jnn_I64 c'_2_18))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_250 :: lane_underscore). ((proj_lane__2 c_1_250) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_250 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_1_250))))) c_1_lst)) ⟹
		 list_all (λ (c_2_180 :: lane_underscore). ((proj_lane__2 c_2_180) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_180 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_2_180))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ((map (λ (c'_1_20 :: iN). (mk_lane__2 Jnn_I64 c'_1_20)) c'_1_lst) @ (map (λ (c'_2_20 :: iN). (mk_lane__2 Jnn_I64 c'_2_20)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_5 :
		"list_all (λ (c_1_251 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) c_1_251)) c_1_lst ⟹
		 list_all (λ (c_2_181 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) c_2_181)) c_2_lst ⟹
		 list_all (λ (iter_205 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) iter_205)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_206 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) iter_206)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_252 :: lane_underscore). ((proj_lane__2 c_1_252) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_252 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I64)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_1_252)))))) c_1_lst ⟹
		 list_all (λ (c_2_182 :: lane_underscore). ((proj_lane__2 c_2_182) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_182 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I64)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_2_182)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ((map (λ (c'_1_21 :: iN). (mk_lane__2 Jnn_I64 c'_1_21)) c'_1_lst) @ (map (λ (c'_2_21 :: iN). (mk_lane__2 Jnn_I64 c'_2_21)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_22 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_lane__2 Jnn_I64 c'_1_22))) c'_1_lst ⟹
		 list_all (λ (c'_2_22 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_lane__2 Jnn_I64 c'_2_22))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_254 :: lane_underscore). ((proj_lane__2 c_1_254) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_254 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_1_254))))) c_1_lst)) ⟹
		 list_all (λ (c_2_184 :: lane_underscore). ((proj_lane__2 c_2_184) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_184 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_2_184))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ((map (λ (c'_1_24 :: iN). (mk_lane__2 Jnn_I64 c'_1_24)) c'_1_lst) @ (map (λ (c'_2_24 :: iN). (mk_lane__2 Jnn_I64 c'_2_24)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_6 :
		"list_all (λ (c_1_255 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) c_1_255)) c_1_lst ⟹
		 list_all (λ (c_2_185 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) c_2_185)) c_2_lst ⟹
		 list_all (λ (iter_207 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) iter_207)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_208 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) iter_208)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_256 :: lane_underscore). ((proj_lane__2 c_1_256) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_256 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I64)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_1_256)))))) c_1_lst ⟹
		 list_all (λ (c_2_186 :: lane_underscore). ((proj_lane__2 c_2_186) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_186 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I64)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_2_186)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ((map (λ (c'_1_25 :: iN). (mk_lane__2 Jnn_I64 c'_1_25)) c'_1_lst) @ (map (λ (c'_2_25 :: iN). (mk_lane__2 Jnn_I64 c'_2_25)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_26 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_lane__2 Jnn_I64 c'_1_26))) c'_1_lst ⟹
		 list_all (λ (c'_2_26 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_lane__2 Jnn_I64 c'_2_26))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_258 :: lane_underscore). ((proj_lane__2 c_1_258) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_258 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_1_258))))) c_1_lst)) ⟹
		 list_all (λ (c_2_188 :: lane_underscore). ((proj_lane__2 c_2_188) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_188 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_2_188))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ((map (λ (c'_1_28 :: iN). (mk_lane__2 Jnn_I64 c'_1_28)) c'_1_lst) @ (map (λ (c'_2_28 :: iN). (mk_lane__2 Jnn_I64 c'_2_28)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_7 :
		"list_all (λ (c_1_259 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) c_1_259)) c_1_lst ⟹
		 list_all (λ (c_2_189 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) c_2_189)) c_2_lst ⟹
		 list_all (λ (iter_209 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) iter_209)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_210 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) iter_210)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_260 :: lane_underscore). ((proj_lane__2 c_1_260) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_260 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I64)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_1_260)))))) c_1_lst ⟹
		 list_all (λ (c_2_190 :: lane_underscore). ((proj_lane__2 c_2_190) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_190 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I64)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_2_190)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ((map (λ (c'_1_29 :: iN). (mk_lane__2 Jnn_I64 c'_1_29)) c'_1_lst) @ (map (λ (c'_2_29 :: iN). (mk_lane__2 Jnn_I64 c'_2_29)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_30 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_lane__2 Jnn_I64 c'_1_30))) c'_1_lst ⟹
		 list_all (λ (c'_2_30 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_lane__2 Jnn_I64 c'_2_30))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_262 :: lane_underscore). ((proj_lane__2 c_1_262) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_262 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_1_262))))) c_1_lst)) ⟹
		 list_all (λ (c_2_192 :: lane_underscore). ((proj_lane__2 c_2_192) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_192 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 c_2_192))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ((map (λ (c'_1_32 :: iN). (mk_lane__2 Jnn_I64 c'_1_32)) c'_1_lst) @ (map (λ (c'_2_32 :: iN). (mk_lane__2 Jnn_I64 c'_2_32)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_8 :
		"list_all (λ (c_1_263 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) c_1_263)) c_1_lst ⟹
		 list_all (λ (c_2_193 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) c_2_193)) c_2_lst ⟹
		 list_all (λ (iter_211 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) iter_211)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_212 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) iter_212)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_264 :: lane_underscore). ((proj_lane__2 c_1_264) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_264 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I8)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_1_264)))))) c_1_lst ⟹
		 list_all (λ (c_2_194 :: lane_underscore). ((proj_lane__2 c_2_194) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_194 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I8)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_2_194)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ((map (λ (c'_1_33 :: iN). (mk_lane__2 Jnn_I8 c'_1_33)) c'_1_lst) @ (map (λ (c'_2_33 :: iN). (mk_lane__2 Jnn_I8 c'_2_33)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_34 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_lane__2 Jnn_I8 c'_1_34))) c'_1_lst ⟹
		 list_all (λ (c'_2_34 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_lane__2 Jnn_I8 c'_2_34))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_266 :: lane_underscore). ((proj_lane__2 c_1_266) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_266 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_1_266))))) c_1_lst)) ⟹
		 list_all (λ (c_2_196 :: lane_underscore). ((proj_lane__2 c_2_196) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_196 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_2_196))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ((map (λ (c'_1_36 :: iN). (mk_lane__2 Jnn_I8 c'_1_36)) c'_1_lst) @ (map (λ (c'_2_36 :: iN). (mk_lane__2 Jnn_I8 c'_2_36)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_9 :
		"list_all (λ (c_1_267 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) c_1_267)) c_1_lst ⟹
		 list_all (λ (c_2_197 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) c_2_197)) c_2_lst ⟹
		 list_all (λ (iter_213 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) iter_213)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_214 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) iter_214)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_268 :: lane_underscore). ((proj_lane__2 c_1_268) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_268 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I8)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_1_268)))))) c_1_lst ⟹
		 list_all (λ (c_2_198 :: lane_underscore). ((proj_lane__2 c_2_198) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_198 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I8)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_2_198)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ((map (λ (c'_1_37 :: iN). (mk_lane__2 Jnn_I8 c'_1_37)) c'_1_lst) @ (map (λ (c'_2_37 :: iN). (mk_lane__2 Jnn_I8 c'_2_37)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_38 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_lane__2 Jnn_I8 c'_1_38))) c'_1_lst ⟹
		 list_all (λ (c'_2_38 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_lane__2 Jnn_I8 c'_2_38))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_270 :: lane_underscore). ((proj_lane__2 c_1_270) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_270 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_1_270))))) c_1_lst)) ⟹
		 list_all (λ (c_2_200 :: lane_underscore). ((proj_lane__2 c_2_200) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_200 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_2_200))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ((map (λ (c'_1_40 :: iN). (mk_lane__2 Jnn_I8 c'_1_40)) c'_1_lst) @ (map (λ (c'_2_40 :: iN). (mk_lane__2 Jnn_I8 c'_2_40)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_10 :
		"list_all (λ (c_1_271 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) c_1_271)) c_1_lst ⟹
		 list_all (λ (c_2_201 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) c_2_201)) c_2_lst ⟹
		 list_all (λ (iter_215 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) iter_215)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_216 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) iter_216)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_272 :: lane_underscore). ((proj_lane__2 c_1_272) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_272 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I8)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_1_272)))))) c_1_lst ⟹
		 list_all (λ (c_2_202 :: lane_underscore). ((proj_lane__2 c_2_202) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_202 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I8)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_2_202)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ((map (λ (c'_1_41 :: iN). (mk_lane__2 Jnn_I8 c'_1_41)) c'_1_lst) @ (map (λ (c'_2_41 :: iN). (mk_lane__2 Jnn_I8 c'_2_41)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_42 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_lane__2 Jnn_I8 c'_1_42))) c'_1_lst ⟹
		 list_all (λ (c'_2_42 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_lane__2 Jnn_I8 c'_2_42))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_274 :: lane_underscore). ((proj_lane__2 c_1_274) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_274 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_1_274))))) c_1_lst)) ⟹
		 list_all (λ (c_2_204 :: lane_underscore). ((proj_lane__2 c_2_204) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_204 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_2_204))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ((map (λ (c'_1_44 :: iN). (mk_lane__2 Jnn_I8 c'_1_44)) c'_1_lst) @ (map (λ (c'_2_44 :: iN). (mk_lane__2 Jnn_I8 c'_2_44)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_11 :
		"list_all (λ (c_1_275 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) c_1_275)) c_1_lst ⟹
		 list_all (λ (c_2_205 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) c_2_205)) c_2_lst ⟹
		 list_all (λ (iter_217 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) iter_217)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_218 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) iter_218)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_276 :: lane_underscore). ((proj_lane__2 c_1_276) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_276 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I8)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_1_276)))))) c_1_lst ⟹
		 list_all (λ (c_2_206 :: lane_underscore). ((proj_lane__2 c_2_206) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_206 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I8)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_2_206)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ((map (λ (c'_1_45 :: iN). (mk_lane__2 Jnn_I8 c'_1_45)) c'_1_lst) @ (map (λ (c'_2_45 :: iN). (mk_lane__2 Jnn_I8 c'_2_45)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_46 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_lane__2 Jnn_I8 c'_1_46))) c'_1_lst ⟹
		 list_all (λ (c'_2_46 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_lane__2 Jnn_I8 c'_2_46))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_278 :: lane_underscore). ((proj_lane__2 c_1_278) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_278 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_1_278))))) c_1_lst)) ⟹
		 list_all (λ (c_2_208 :: lane_underscore). ((proj_lane__2 c_2_208) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_208 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 c_2_208))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ((map (λ (c'_1_48 :: iN). (mk_lane__2 Jnn_I8 c'_1_48)) c'_1_lst) @ (map (λ (c'_2_48 :: iN). (mk_lane__2 Jnn_I8 c'_2_48)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_12 :
		"list_all (λ (c_1_279 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) c_1_279)) c_1_lst ⟹
		 list_all (λ (c_2_209 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) c_2_209)) c_2_lst ⟹
		 list_all (λ (iter_219 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) iter_219)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_220 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) iter_220)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_280 :: lane_underscore). ((proj_lane__2 c_1_280) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_280 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I16)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_1_280)))))) c_1_lst ⟹
		 list_all (λ (c_2_210 :: lane_underscore). ((proj_lane__2 c_2_210) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_210 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I16)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_2_210)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ((map (λ (c'_1_49 :: iN). (mk_lane__2 Jnn_I16 c'_1_49)) c'_1_lst) @ (map (λ (c'_2_49 :: iN). (mk_lane__2 Jnn_I16 c'_2_49)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_50 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_lane__2 Jnn_I16 c'_1_50))) c'_1_lst ⟹
		 list_all (λ (c'_2_50 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_lane__2 Jnn_I16 c'_2_50))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_282 :: lane_underscore). ((proj_lane__2 c_1_282) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_282 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_1_282))))) c_1_lst)) ⟹
		 list_all (λ (c_2_212 :: lane_underscore). ((proj_lane__2 c_2_212) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_212 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I32)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_2_212))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ((map (λ (c'_1_52 :: iN). (mk_lane__2 Jnn_I16 c'_1_52)) c'_1_lst) @ (map (λ (c'_2_52 :: iN). (mk_lane__2 Jnn_I16 c'_2_52)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_13 :
		"list_all (λ (c_1_283 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) c_1_283)) c_1_lst ⟹
		 list_all (λ (c_2_213 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) c_2_213)) c_2_lst ⟹
		 list_all (λ (iter_221 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) iter_221)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_222 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) iter_222)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_284 :: lane_underscore). ((proj_lane__2 c_1_284) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_284 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I16)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_1_284)))))) c_1_lst ⟹
		 list_all (λ (c_2_214 :: lane_underscore). ((proj_lane__2 c_2_214) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_214 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I16)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_2_214)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ((map (λ (c'_1_53 :: iN). (mk_lane__2 Jnn_I16 c'_1_53)) c'_1_lst) @ (map (λ (c'_2_53 :: iN). (mk_lane__2 Jnn_I16 c'_2_53)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_54 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_lane__2 Jnn_I16 c'_1_54))) c'_1_lst ⟹
		 list_all (λ (c'_2_54 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_lane__2 Jnn_I16 c'_2_54))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_286 :: lane_underscore). ((proj_lane__2 c_1_286) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_286 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_1_286))))) c_1_lst)) ⟹
		 list_all (λ (c_2_216 :: lane_underscore). ((proj_lane__2 c_2_216) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_216 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I64)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_2_216))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ((map (λ (c'_1_56 :: iN). (mk_lane__2 Jnn_I16 c'_1_56)) c'_1_lst) @ (map (λ (c'_2_56 :: iN). (mk_lane__2 Jnn_I16 c'_2_56)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_14 :
		"list_all (λ (c_1_287 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) c_1_287)) c_1_lst ⟹
		 list_all (λ (c_2_217 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) c_2_217)) c_2_lst ⟹
		 list_all (λ (iter_223 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) iter_223)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_224 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) iter_224)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_288 :: lane_underscore). ((proj_lane__2 c_1_288) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_288 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I16)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_1_288)))))) c_1_lst ⟹
		 list_all (λ (c_2_218 :: lane_underscore). ((proj_lane__2 c_2_218) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_218 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I16)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_2_218)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ((map (λ (c'_1_57 :: iN). (mk_lane__2 Jnn_I16 c'_1_57)) c'_1_lst) @ (map (λ (c'_2_57 :: iN). (mk_lane__2 Jnn_I16 c'_2_57)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_58 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_lane__2 Jnn_I16 c'_1_58))) c'_1_lst ⟹
		 list_all (λ (c'_2_58 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_lane__2 Jnn_I16 c'_2_58))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_290 :: lane_underscore). ((proj_lane__2 c_1_290) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_290 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_1_290))))) c_1_lst)) ⟹
		 list_all (λ (c_2_220 :: lane_underscore). ((proj_lane__2 c_2_220) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_220 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I8)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_2_220))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ((map (λ (c'_1_60 :: iN). (mk_lane__2 Jnn_I16 c'_1_60)) c'_1_lst) @ (map (λ (c'_2_60 :: iN). (mk_lane__2 Jnn_I16 c'_2_60)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) v_sx v_1 v_2 v"
	| fun_vnarrowop___case_15 :
		"list_all (λ (c_1_291 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) c_1_291)) c_1_lst ⟹
		 list_all (λ (c_2_221 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) c_2_221)) c_2_lst ⟹
		 list_all (λ (iter_225 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) iter_225)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_1) ⟹
		 list_all (λ (iter_226 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) iter_226)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_2) ⟹
		 list_all (λ (c_1_292 :: lane_underscore). ((proj_lane__2 c_1_292) ≠ None)) c_1_lst ⟹
		 list_all (λ (c_1_292 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I16)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_1_292)))))) c_1_lst ⟹
		 list_all (λ (c_2_222 :: lane_underscore). ((proj_lane__2 c_2_222) ≠ None)) c_2_lst ⟹
		 list_all (λ (c_2_222 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I16)) (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_2_222)))))) c_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ((map (λ (c'_1_61 :: iN). (mk_lane__2 Jnn_I16 c'_1_61)) c'_1_lst) @ (map (λ (c'_2_61 :: iN). (mk_lane__2 Jnn_I16 c'_2_61)) c'_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) ⟹
		 list_all (λ (c'_1_62 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_lane__2 Jnn_I16 c'_1_62))) c'_1_lst ⟹
		 list_all (λ (c'_2_62 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_lane__2 Jnn_I16 c'_2_62))) c'_2_lst ⟹
		 (c_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_1)) ⟹
		 (c_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) v_2)) ⟹
		 list_all (λ (c_1_294 :: lane_underscore). ((proj_lane__2 c_1_294) ≠ None)) c_1_lst ⟹
		 (c'_1_lst = (map (λ (c_1_294 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_1_294))))) c_1_lst)) ⟹
		 list_all (λ (c_2_224 :: lane_underscore). ((proj_lane__2 c_2_224) ≠ None)) c_2_lst ⟹
		 (c'_2_lst = (map (λ (c_2_224 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_I16)) (lsize (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 c_2_224))))) c_2_lst)) ⟹
		 (v = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ((map (λ (c'_1_64 :: iN). (mk_lane__2 Jnn_I16 c'_1_64)) c'_1_lst) @ (map (λ (c'_2_64 :: iN). (mk_lane__2 Jnn_I16 c'_2_64)) c'_2_lst)))) ⟹
		 fun_vnarrowop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) v_sx v_1 v_2 v"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:356.1-356.76 *)
axiomatization ivadd_pairwise_underscore :: "N ⇒ (iN list) ⇒ (iN list)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:342.1-342.93 *)
axiomatization ivextunop__underscore :: "shape ⇒ shape ⇒ (N ⇒ (iN list) ⇒ (iN list)) ⇒ sx ⇒ vec_underscore ⇒ vec_underscore"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:198.6-198.17 *)
inductive fun_vextunop__underscore :: "ishape ⇒ ishape ⇒ vextunop__underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ bool" where
	  fun_vextunop___case_0 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextunop___0 Jnn_I32 M_1_0 Jnn_I32 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_1 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextunop___0 Jnn_I64 M_1_0 Jnn_I32 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_2 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextunop___0 Jnn_I8 M_1_0 Jnn_I32 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_3 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextunop___0 Jnn_I16 M_1_0 Jnn_I32 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_4 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextunop___0 Jnn_I32 M_1_0 Jnn_I64 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_5 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextunop___0 Jnn_I64 M_1_0 Jnn_I64 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_6 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextunop___0 Jnn_I8 M_1_0 Jnn_I64 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_7 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextunop___0 Jnn_I16 M_1_0 Jnn_I64 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_8 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextunop___0 Jnn_I32 M_1_0 Jnn_I8 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_9 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextunop___0 Jnn_I64 M_1_0 Jnn_I8 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_10 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextunop___0 Jnn_I8 M_1_0 Jnn_I8 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_11 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextunop___0 Jnn_I16 M_1_0 Jnn_I8 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_12 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextunop___0 Jnn_I32 M_1_0 Jnn_I16 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_13 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextunop___0 Jnn_I64 M_1_0 Jnn_I16 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_14 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextunop___0 Jnn_I8 M_1_0 Jnn_I16 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"
	| fun_vextunop___case_15 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextunop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextunop___0 Jnn_I16 M_1_0 Jnn_I16 M_2_0 (EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivadd_pairwise_underscore v_sx v_1)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:363.1-363.40 *)
axiomatization ivdot_underscore :: "N ⇒ (iN list) ⇒ (iN list) ⇒ (iN list)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:367.1-367.76 *)
axiomatization ivdot_sat_underscore :: "N ⇒ (iN list) ⇒ (iN list) ⇒ (iN list)"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:348.1-348.136 *)
axiomatization ivextbinop__underscore :: "shape ⇒ shape ⇒ (N ⇒ (iN list) ⇒ (iN list) ⇒ (iN list)) ⇒ sx ⇒ sx ⇒ laneidx ⇒ laneidx ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore"

(* Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:360.1-360.40 *)
function (sequential) ivmul_underscore :: "N ⇒ (iN list) ⇒ (iN list) ⇒ (iN list)" where
		  "ivmul_underscore v_N i_1_lst i_2_lst = (list_zipWith (λ (i_1 :: iN) (i_2 :: iN). (imul_underscore v_N i_1 i_2)) i_1_lst i_2_lst)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:200.6-200.18 *)
inductive fun_vextbinop__underscore :: "ishape ⇒ ishape ⇒ vextbinop__underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ bool" where
	  fun_vextbinop___case_0 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I32 M_1_0 Jnn_I32 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_1 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I64 M_1_0 Jnn_I32 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_2 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I8 M_1_0 Jnn_I32 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_3 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I16 M_1_0 Jnn_I32 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_4 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I32 M_1_0 Jnn_I64 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_5 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I64 M_1_0 Jnn_I64 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_6 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I8 M_1_0 Jnn_I64 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_7 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I16 M_1_0 Jnn_I64 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_8 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I32 M_1_0 Jnn_I8 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_9 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I64 M_1_0 Jnn_I8 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_10 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I8 M_1_0 Jnn_I8 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_11 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I16 M_1_0 Jnn_I8 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_12 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I32 M_1_0 Jnn_I16 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_13 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I64 M_1_0 Jnn_I16 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_14 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I8 M_1_0 Jnn_I16 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_15 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I16 M_1_0 Jnn_I16 M_2_0 (EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivmul_underscore v_sx v_sx (mk_uN (fun_half v_half 0 M_2)) (mk_uN M_2) v_1 v_2)"
	| fun_vextbinop___case_16 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I32 M_1_0 Jnn_I32 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_17 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I64 M_1_0 Jnn_I32 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_18 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I8 M_1_0 Jnn_I32 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_19 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I16 M_1_0 Jnn_I32 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_20 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I32 M_1_0 Jnn_I64 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_21 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I64 M_1_0 Jnn_I64 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_22 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I8 M_1_0 Jnn_I64 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_23 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I16 M_1_0 Jnn_I64 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_24 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I32 M_1_0 Jnn_I8 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_25 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I64 M_1_0 Jnn_I8 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_26 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I8 M_1_0 Jnn_I8 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_27 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I16 M_1_0 Jnn_I8 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_28 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I32 M_1_0 Jnn_I16 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_29 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I64 M_1_0 Jnn_I16 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_30 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I8 M_1_0 Jnn_I16 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_31 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I16 M_1_0 Jnn_I16 M_2_0 DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivdot_underscore S S (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_32 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I32 M_1_0 Jnn_I32 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_33 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I64 M_1_0 Jnn_I32 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_34 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I8 M_1_0 Jnn_I32 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_35 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I16 M_1_0 Jnn_I32 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_36 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I32 M_1_0 Jnn_I64 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_37 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I64 M_1_0 Jnn_I64 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_38 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I8 M_1_0 Jnn_I64 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_39 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I16 M_1_0 Jnn_I64 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_40 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I32 M_1_0 Jnn_I8 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_41 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I64 M_1_0 Jnn_I8 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_42 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I8 M_1_0 Jnn_I8 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_43 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I16 M_1_0 Jnn_I8 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_44 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I32 M_1_0 Jnn_I16 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_45 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I64 M_1_0 Jnn_I16 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_46 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I8 M_1_0 Jnn_I16 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"
	| fun_vextbinop___case_47 :
		"(M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextbinop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextbinop___0 Jnn_I16 M_1_0 Jnn_I16 M_2_0 RELAXED_DOTS) v_1 v_2 (ivextbinop__underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)) (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) ivdot_sat_underscore S (fun_relaxed2 (R_idot )  S U) (mk_uN 0) (mk_uN M_1) v_1 v_2)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:202.6-202.19 *)
inductive fun_vextternop__underscore :: "ishape ⇒ ishape ⇒ vextternop__underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ bool" where
	  fun_vextternop___case_0 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) (mk_vbinop__0 Jnn_I32 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I32 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I32 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_307 :: vec_underscore). (wf_uN 128 iter_307)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I32 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I32 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) (mk_vbinop__0 Jnn_I32 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I32)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextternop___0 Jnn_I32 M_1_0 Jnn_I32 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_1 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) (mk_vbinop__0 Jnn_I32 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I32 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I64 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_308 :: vec_underscore). (wf_uN 128 iter_308)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I64 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I32 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) (mk_vbinop__0 Jnn_I32 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I64)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextternop___0 Jnn_I64 M_1_0 Jnn_I32 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_2 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) (mk_vbinop__0 Jnn_I32 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I32 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I8 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_309 :: vec_underscore). (wf_uN 128 iter_309)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I8 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I32 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) (mk_vbinop__0 Jnn_I32 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I8)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextternop___0 Jnn_I8 M_1_0 Jnn_I32 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_3 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) (mk_vbinop__0 Jnn_I32 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I32 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I16 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_310 :: vec_underscore). (wf_uN 128 iter_310)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I16 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I32 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim M_2)) (mk_vbinop__0 Jnn_I32 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I16)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I32 (mk_dim M_2))) (mk_vextternop___0 Jnn_I16 M_1_0 Jnn_I32 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_4 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) (mk_vbinop__0 Jnn_I64 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I64 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I32 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_311 :: vec_underscore). (wf_uN 128 iter_311)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I32 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I64 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) (mk_vbinop__0 Jnn_I64 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I32)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextternop___0 Jnn_I32 M_1_0 Jnn_I64 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_5 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) (mk_vbinop__0 Jnn_I64 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I64 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I64 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_312 :: vec_underscore). (wf_uN 128 iter_312)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I64 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I64 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) (mk_vbinop__0 Jnn_I64 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I64)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextternop___0 Jnn_I64 M_1_0 Jnn_I64 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_6 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) (mk_vbinop__0 Jnn_I64 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I64 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I8 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_313 :: vec_underscore). (wf_uN 128 iter_313)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I8 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I64 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) (mk_vbinop__0 Jnn_I64 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I8)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextternop___0 Jnn_I8 M_1_0 Jnn_I64 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_7 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) (mk_vbinop__0 Jnn_I64 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I64 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I16 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_314 :: vec_underscore). (wf_uN 128 iter_314)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I16 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I64 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim M_2)) (mk_vbinop__0 Jnn_I64 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I16)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I64 (mk_dim M_2))) (mk_vextternop___0 Jnn_I16 M_1_0 Jnn_I64 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_8 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) (mk_vbinop__0 Jnn_I8 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I8 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I32 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_315 :: vec_underscore). (wf_uN 128 iter_315)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I32 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I8 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) (mk_vbinop__0 Jnn_I8 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I32)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextternop___0 Jnn_I32 M_1_0 Jnn_I8 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_9 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) (mk_vbinop__0 Jnn_I8 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I8 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I64 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_316 :: vec_underscore). (wf_uN 128 iter_316)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I64 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I8 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) (mk_vbinop__0 Jnn_I8 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I64)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextternop___0 Jnn_I64 M_1_0 Jnn_I8 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_10 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) (mk_vbinop__0 Jnn_I8 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I8 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I8 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_317 :: vec_underscore). (wf_uN 128 iter_317)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I8 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I8 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) (mk_vbinop__0 Jnn_I8 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I8)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextternop___0 Jnn_I8 M_1_0 Jnn_I8 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_11 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) (mk_vbinop__0 Jnn_I8 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I8 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I16 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_318 :: vec_underscore). (wf_uN 128 iter_318)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I16 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I8 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim M_2)) (mk_vbinop__0 Jnn_I8 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I16)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I8 (mk_dim M_2))) (mk_vextternop___0 Jnn_I16 M_1_0 Jnn_I8 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_12 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) (mk_vbinop__0 Jnn_I16 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I16 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I32 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_319 :: vec_underscore). (wf_uN 128 iter_319)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I32) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I32 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I16 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) (mk_vbinop__0 Jnn_I16 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I32)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I32 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextternop___0 Jnn_I32 M_1_0 Jnn_I16 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_13 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) (mk_vbinop__0 Jnn_I16 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I16 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I64 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_320 :: vec_underscore). (wf_uN 128 iter_320)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I64) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I64 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I16 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) (mk_vbinop__0 Jnn_I16 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I64)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I64 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextternop___0 Jnn_I64 M_1_0 Jnn_I16 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_14 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) (mk_vbinop__0 Jnn_I16 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I16 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I8 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_321 :: vec_underscore). (wf_uN 128 iter_321)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I8) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I8 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I16 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) (mk_vbinop__0 Jnn_I16 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I8)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I8 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextternop___0 Jnn_I8 M_1_0 Jnn_I16 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"
	| fun_vextternop___case_15 :
		"(fun_vbinop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) (mk_vbinop__0 Jnn_I16 M_2 vbinop_Jnn_M_ADD) c'' c_3 var_2) ⟹
		 (fun_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I16 M_2 (EXTADD_PAIRWISE S)) c' var_1) ⟹
		 (fun_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I16 M_1 v_Jnn v_M RELAXED_DOTS) c_1 c_2 var_0) ⟹
		 (wf_uN 128 c') ⟹
		 (wf_uN 128 c'') ⟹
		 (wf_uN 128 var_0) ⟹
		 (wf_uN 128 var_1) ⟹
		 list_all (λ (iter_322 :: vec_underscore). (wf_uN 128 iter_322)) var_2 ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1)))) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M)))) ⟹
		 (wf_vextbinop__underscore (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_1))) (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_vextbinop___0 Jnn_I16 M_1 v_Jnn v_M RELAXED_DOTS)) ⟹
		 (wf_ishape (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)))) ⟹
		 (wf_vextunop__underscore (mk_ishape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_ishape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) (mk_vextunop___0 v_Jnn v_M Jnn_I16 M_2 (EXTADD_PAIRWISE S))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim M_2))) ⟹
		 (wf_vbinop_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim M_2)) (mk_vbinop__0 Jnn_I16 M_2 vbinop_Jnn_M_ADD)) ⟹
		 ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn_I16)))) ⟹
		 (v_M = (2 * M_2)) ⟹
		 (c' = var_0) ⟹
		 (c'' = var_1) ⟹
		 ((length var_2) > 0) ⟹
		 (c ∈ set var_2) ⟹
		 (M_1 = M_1_0) ⟹
		 (M_2 = M_2_0) ⟹
		 fun_vextternop__underscore (mk_ishape (X lanetype_I16 (mk_dim M_1))) (mk_ishape (X lanetype_I16 (mk_dim M_2))) (mk_vextternop___0 Jnn_I16 M_1_0 Jnn_I16 M_2_0 RELAXED_DOT_ADDS) c_1 c_2 c_3 c"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:29.1-30.63 *)
datatype num =
	  num_CONST "numtype" "num_underscore"
	

(* Auxiliary Definition at:  *)
function (sequential) val_num :: "num ⇒ val" where
		  "val_num (num_CONST x0 x1) = (res_CONST x0 x1)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:29.8-29.11 *)
inductive wf_num :: "num ⇒ bool" where
	  num_case_0 :
		"(wf_num_underscore v_numtype var_0) ⟹
		 wf_num (num_CONST v_numtype var_0)"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:32.1-33.87 *)
datatype vec =
	  vec_VCONST "vectype" "vec_underscore"
	

(* Auxiliary Definition at:  *)
function (sequential) val_vec :: "vec ⇒ val" where
		  "val_vec (vec_VCONST x0 x1) = (VCONST x0 x1)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:32.8-32.11 *)
inductive wf_vec :: "vec ⇒ bool" where
	  vec_case_0 :
		"(wf_uN (vsize v_vectype) var_0) ⟹
		 wf_vec (vec_VCONST v_vectype var_0)"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:44.1-46.22 *)
datatype ref =
	  ref_REF_I31_NUM "u31"
	| ref_REF_STRUCT_ADDR "structaddr"
	| ref_REF_ARRAY_ADDR "arrayaddr"
	| ref_REF_FUNC_ADDR "funcaddr"
	| ref_REF_EXN_ADDR "exnaddr"
	| ref_REF_HOST_ADDR "hostaddr"
	| ref_REF_EXTERN "addrref"
	| ref_REF_NULL "heaptype"

(* Auxiliary Definition at:  *)
function (sequential) ref_addrref :: "addrref ⇒ ref" where
		  "ref_addrref (REF_I31_NUM x0) = (ref_REF_I31_NUM x0)"
		| "ref_addrref (REF_STRUCT_ADDR x0) = (ref_REF_STRUCT_ADDR x0)"
		| "ref_addrref (REF_ARRAY_ADDR x0) = (ref_REF_ARRAY_ADDR x0)"
		| "ref_addrref (REF_FUNC_ADDR x0) = (ref_REF_FUNC_ADDR x0)"
		| "ref_addrref (REF_EXN_ADDR x0) = (ref_REF_EXN_ADDR x0)"
		| "ref_addrref (REF_HOST_ADDR x0) = (ref_REF_HOST_ADDR x0)"
		| "ref_addrref (REF_EXTERN x0) = (ref_REF_EXTERN x0)"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) instr_ref :: "ref ⇒ instr" where
		  "instr_ref (ref_REF_I31_NUM x0) = (instr_sc9 (instr_st9_REF_I31_NUM x0))"
		| "instr_ref (ref_REF_STRUCT_ADDR x0) = (instr_sc9 (instr_st9_REF_STRUCT_ADDR x0))"
		| "instr_ref (ref_REF_ARRAY_ADDR x0) = (instr_sc9 (instr_st9_REF_ARRAY_ADDR x0))"
		| "instr_ref (ref_REF_FUNC_ADDR x0) = (instr_sc9 (instr_st9_REF_FUNC_ADDR x0))"
		| "instr_ref (ref_REF_EXN_ADDR x0) = (instr_sc9 (instr_st9_REF_EXN_ADDR x0))"
		| "instr_ref (ref_REF_HOST_ADDR x0) = (instr_sc9 (instr_st9_REF_HOST_ADDR x0))"
		| "instr_ref (ref_REF_EXTERN x0) = (instr_sc9 (instr_st9_REF_EXTERN x0))"
		| "instr_ref (ref_REF_NULL x0) = (instr_sc4 (instr_st4_REF_NULL x0))"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) val_ref :: "ref ⇒ val" where
		  "val_ref (ref_REF_I31_NUM x0) = (val_REF_I31_NUM x0)"
		| "val_ref (ref_REF_STRUCT_ADDR x0) = (val_REF_STRUCT_ADDR x0)"
		| "val_ref (ref_REF_ARRAY_ADDR x0) = (val_REF_ARRAY_ADDR x0)"
		| "val_ref (ref_REF_FUNC_ADDR x0) = (val_REF_FUNC_ADDR x0)"
		| "val_ref (ref_REF_EXN_ADDR x0) = (val_REF_EXN_ADDR x0)"
		| "val_ref (ref_REF_HOST_ADDR x0) = (val_REF_HOST_ADDR x0)"
		| "val_ref (ref_REF_EXTERN x0) = (val_REF_EXTERN x0)"
		| "val_ref (ref_REF_NULL x0) = (REF_NULL x0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:44.8-44.11 *)
inductive wf_ref :: "ref ⇒ bool" where
	  ref_case_0 :
		"(wf_uN 31 v_u31) ⟹
		 wf_ref (ref_REF_I31_NUM v_u31)"
	| ref_case_1 :
		"wf_ref (ref_REF_STRUCT_ADDR v_structaddr)"
	| ref_case_2 :
		"wf_ref (ref_REF_ARRAY_ADDR v_arrayaddr)"
	| ref_case_3 :
		"wf_ref (ref_REF_FUNC_ADDR v_funcaddr)"
	| ref_case_4 :
		"wf_ref (ref_REF_EXN_ADDR v_exnaddr)"
	| ref_case_5 :
		"wf_ref (ref_REF_HOST_ADDR v_hostaddr)"
	| ref_case_6 :
		"(wf_addrref v_addrref) ⟹
		 wf_ref (ref_REF_EXTERN v_addrref)"
	| ref_case_7 :
		"(wf_heaptype v_heaptype) ⟹
		 wf_ref (ref_REF_NULL v_heaptype)"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:51.1-52.58 *)
datatype result =
	  underscore_VALS "(val list)"
	| REF_EXN_ADDRTHROW_REF "exnaddr"
	| result_TRAP

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:51.8-51.14 *)
inductive wf_result :: "result ⇒ bool" where
	  result_case_0 :
		"list_all (λ (v_val :: val). (wf_val v_val)) val_lst ⟹
		 wf_result (underscore_VALS val_lst)"
	| result_case_1 :
		"wf_result (REF_EXN_ADDRTHROW_REF v_exnaddr)"
	| result_case_2 :
		"wf_result result_TRAP"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:60.1-60.72 *)
datatype hostfunc =
	  mk_hostfunc
	

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:61.1-61.73 *)
datatype funccode =
	  funccode_FUNC "typeidx" "(local list)" "expr"
	| mk_funccode

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:61.8-61.16 *)
inductive wf_funccode :: "funccode ⇒ bool" where
	  funccode_case_0 :
		"(wf_uN 32 v_typeidx) ⟹
		 list_all (λ (v_local :: local). (wf_local v_local)) local_lst ⟹
		 list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_funccode (funccode_FUNC v_typeidx local_lst v_expr)"
	| funccode_case_1 :
		"wf_funccode mk_funccode"

(* Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:63.1-64.19 *)
record taginst =
	taginst_TYPE :: "tagtype"

definition append_taginst :: "taginst ⇒ taginst ⇒ taginst" where
	"append_taginst arg1 arg2 = ⦇
		taginst_TYPE = taginst_TYPE arg1
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:63.8-63.15 *)
inductive wf_taginst :: "taginst ⇒ bool" where
	  taginst_case_underscore :
		"(wf_typeuse var_0) ⟹
		 wf_taginst ⦇ taginst_TYPE = var_0 ⦈"

(* Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:66.1-67.33 *)
record globalinst =
	globalinst_TYPE :: "globaltype"
	VALUE :: "val"

definition append_globalinst :: "globalinst ⇒ globalinst ⇒ globalinst" where
	"append_globalinst arg1 arg2 = ⦇
		globalinst_TYPE = globalinst_TYPE arg1,
		VALUE = VALUE arg1
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:66.8-66.18 *)
inductive wf_globalinst :: "globalinst ⇒ bool" where
	  globalinst_case_underscore :
		"(wf_globaltype var_0) ⟹
		 (wf_val var_1) ⟹
		 wf_globalinst ⦇ globalinst_TYPE = var_0, VALUE = var_1 ⦈"

(* Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:69.1-70.32 *)
record meminst =
	meminst_TYPE :: "memtype"
	BYTES :: "(byte list)"

definition append_meminst :: "meminst ⇒ meminst ⇒ meminst" where
	"append_meminst arg1 arg2 = ⦇
		meminst_TYPE = meminst_TYPE arg1,
		BYTES = BYTES arg1 @ BYTES arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:69.8-69.15 *)
inductive wf_meminst :: "meminst ⇒ bool" where
	  meminst_case_underscore :
		"(wf_memtype var_0) ⟹
		 list_all (λ (var_1 :: byte). (wf_byte var_1)) var_1 ⟹
		 wf_meminst ⦇ meminst_TYPE = var_0, BYTES = var_1 ⦈"

(* Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:72.1-73.32 *)
record tableinst =
	tableinst_TYPE :: "tabletype"
	tableinst_REFS :: "(ref list)"

definition append_tableinst :: "tableinst ⇒ tableinst ⇒ tableinst" where
	"append_tableinst arg1 arg2 = ⦇
		tableinst_TYPE = tableinst_TYPE arg1,
		tableinst_REFS = tableinst_REFS arg1 @ tableinst_REFS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:72.8-72.17 *)
inductive wf_tableinst :: "tableinst ⇒ bool" where
	  tableinst_case_underscore :
		"(wf_tabletype var_0) ⟹
		 list_all (λ (var_1 :: ref). (wf_ref var_1)) var_1 ⟹
		 wf_tableinst ⦇ tableinst_TYPE = var_0, tableinst_REFS = var_1 ⦈"

(* Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:75.1-76.53 *)
record funcinst =
	funcinst_TYPE :: "deftype"
	funcinst_MODULE :: "moduleinst"
	CODE :: "funccode"

definition append_funcinst :: "funcinst ⇒ funcinst ⇒ funcinst" where
	"append_funcinst arg1 arg2 = ⦇
		funcinst_TYPE = funcinst_TYPE arg1,
		funcinst_MODULE = append_moduleinst (funcinst_MODULE arg1) (funcinst_MODULE arg2),
		CODE = CODE arg1
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:75.8-75.16 *)
inductive wf_funcinst :: "funcinst ⇒ bool" where
	  funcinst_case_underscore :
		"(wf_moduleinst var_1) ⟹
		 (wf_funccode var_2) ⟹
		 wf_funcinst ⦇ funcinst_TYPE = var_0, funcinst_MODULE = var_1, CODE = var_2 ⦈"

(* Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:78.1-79.18 *)
record datainst =
	datainst_BYTES :: "(byte list)"

definition append_datainst :: "datainst ⇒ datainst ⇒ datainst" where
	"append_datainst arg1 arg2 = ⦇
		datainst_BYTES = datainst_BYTES arg1 @ datainst_BYTES arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:78.8-78.16 *)
inductive wf_datainst :: "datainst ⇒ bool" where
	  datainst_case_underscore :
		"list_all (λ (var_0 :: byte). (wf_byte var_0)) var_0 ⟹
		 wf_datainst ⦇ datainst_BYTES = var_0 ⦈"

(* Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:81.1-82.31 *)
record eleminst =
	eleminst_TYPE :: "elemtype"
	eleminst_REFS :: "(ref list)"

definition append_eleminst :: "eleminst ⇒ eleminst ⇒ eleminst" where
	"append_eleminst arg1 arg2 = ⦇
		eleminst_TYPE = eleminst_TYPE arg1,
		eleminst_REFS = eleminst_REFS arg1 @ eleminst_REFS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:81.8-81.16 *)
inductive wf_eleminst :: "eleminst ⇒ bool" where
	  eleminst_case_underscore :
		"(wf_reftype var_0) ⟹
		 list_all (λ (var_1 :: ref). (wf_ref var_1)) var_1 ⟹
		 wf_eleminst ⦇ eleminst_TYPE = var_0, eleminst_REFS = var_1 ⦈"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:88.1-89.64 *)
datatype packval =
	  PACK "packtype" "iN"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:88.8-88.15 *)
inductive wf_packval :: "packval ⇒ bool" where
	  packval_case_0 :
		"(wf_uN (psize v_packtype) var_0) ⟹
		 wf_packval (PACK v_packtype var_0)"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:91.1-92.18 *)
datatype fieldval =
	  fieldval_CONST "numtype" "num_underscore"
	| fieldval_VCONST "vectype" "vec_underscore"
	| fieldval_REF_I31_NUM "u31"
	| fieldval_REF_STRUCT_ADDR "structaddr"
	| fieldval_REF_ARRAY_ADDR "arrayaddr"
	| fieldval_REF_FUNC_ADDR "funcaddr"
	| fieldval_REF_EXN_ADDR "exnaddr"
	| fieldval_REF_HOST_ADDR "hostaddr"
	| fieldval_REF_EXTERN "addrref"
	| fieldval_REF_NULL "heaptype"
	| fieldval_PACK "packtype" "iN"

(* Auxiliary Definition at:  *)
function (sequential) fieldval_val :: "val ⇒ fieldval" where
		  "fieldval_val (res_CONST x0 x1) = (fieldval_CONST x0 x1)"
		| "fieldval_val (VCONST x0 x1) = (fieldval_VCONST x0 x1)"
		| "fieldval_val (val_REF_I31_NUM x0) = (fieldval_REF_I31_NUM x0)"
		| "fieldval_val (val_REF_STRUCT_ADDR x0) = (fieldval_REF_STRUCT_ADDR x0)"
		| "fieldval_val (val_REF_ARRAY_ADDR x0) = (fieldval_REF_ARRAY_ADDR x0)"
		| "fieldval_val (val_REF_FUNC_ADDR x0) = (fieldval_REF_FUNC_ADDR x0)"
		| "fieldval_val (val_REF_EXN_ADDR x0) = (fieldval_REF_EXN_ADDR x0)"
		| "fieldval_val (val_REF_HOST_ADDR x0) = (fieldval_REF_HOST_ADDR x0)"
		| "fieldval_val (val_REF_EXTERN x0) = (fieldval_REF_EXTERN x0)"
		| "fieldval_val (REF_NULL x0) = (fieldval_REF_NULL x0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:91.8-91.16 *)
inductive wf_fieldval :: "fieldval ⇒ bool" where
	  fieldval_case_0 :
		"(wf_num_underscore v_numtype var_0) ⟹
		 wf_fieldval (fieldval_CONST v_numtype var_0)"
	| fieldval_case_1 :
		"(wf_uN (vsize v_vectype) var_0) ⟹
		 wf_fieldval (fieldval_VCONST v_vectype var_0)"
	| fieldval_case_2 :
		"(wf_uN 31 v_u31) ⟹
		 wf_fieldval (fieldval_REF_I31_NUM v_u31)"
	| fieldval_case_3 :
		"wf_fieldval (fieldval_REF_STRUCT_ADDR v_structaddr)"
	| fieldval_case_4 :
		"wf_fieldval (fieldval_REF_ARRAY_ADDR v_arrayaddr)"
	| fieldval_case_5 :
		"wf_fieldval (fieldval_REF_FUNC_ADDR v_funcaddr)"
	| fieldval_case_6 :
		"wf_fieldval (fieldval_REF_EXN_ADDR v_exnaddr)"
	| fieldval_case_7 :
		"wf_fieldval (fieldval_REF_HOST_ADDR v_hostaddr)"
	| fieldval_case_8 :
		"(wf_addrref v_addrref) ⟹
		 wf_fieldval (fieldval_REF_EXTERN v_addrref)"
	| fieldval_case_9 :
		"(wf_heaptype v_heaptype) ⟹
		 wf_fieldval (fieldval_REF_NULL v_heaptype)"
	| fieldval_case_10 :
		"(wf_uN (psize v_packtype) var_0) ⟹
		 wf_fieldval (fieldval_PACK v_packtype var_0)"

(* Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:94.1-95.37 *)
record structinst =
	structinst_TYPE :: "deftype"
	FIELDS :: "(fieldval list)"

definition append_structinst :: "structinst ⇒ structinst ⇒ structinst" where
	"append_structinst arg1 arg2 = ⦇
		structinst_TYPE = structinst_TYPE arg1,
		FIELDS = FIELDS arg1 @ FIELDS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:94.8-94.18 *)
inductive wf_structinst :: "structinst ⇒ bool" where
	  structinst_case_underscore :
		"list_all (λ (var_1 :: fieldval). (wf_fieldval var_1)) var_1 ⟹
		 wf_structinst ⦇ structinst_TYPE = var_0, FIELDS = var_1 ⦈"

(* Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:97.1-98.37 *)
record arrayinst =
	arrayinst_TYPE :: "deftype"
	arrayinst_FIELDS :: "(fieldval list)"

definition append_arrayinst :: "arrayinst ⇒ arrayinst ⇒ arrayinst" where
	"append_arrayinst arg1 arg2 = ⦇
		arrayinst_TYPE = arrayinst_TYPE arg1,
		arrayinst_FIELDS = arrayinst_FIELDS arg1 @ arrayinst_FIELDS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:97.8-97.17 *)
inductive wf_arrayinst :: "arrayinst ⇒ bool" where
	  arrayinst_case_underscore :
		"list_all (λ (var_1 :: fieldval). (wf_fieldval var_1)) var_1 ⟹
		 wf_arrayinst ⦇ arrayinst_TYPE = var_0, arrayinst_FIELDS = var_1 ⦈"

(* Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:100.1-101.31 *)
record exninst =
	exninst_TAG :: "tagaddr"
	exninst_FIELDS :: "(val list)"

definition append_exninst :: "exninst ⇒ exninst ⇒ exninst" where
	"append_exninst arg1 arg2 = ⦇
		exninst_TAG = exninst_TAG arg1,
		exninst_FIELDS = exninst_FIELDS arg1 @ exninst_FIELDS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:100.8-100.15 *)
inductive wf_exninst :: "exninst ⇒ bool" where
	  exninst_case_underscore :
		"list_all (λ (var_1 :: val). (wf_val var_1)) var_1 ⟹
		 wf_exninst ⦇ exninst_TAG = var_0, exninst_FIELDS = var_1 ⦈"

(* Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:118.1-128.20 *)
record store =
	store_TAGS :: "(taginst list)"
	store_GLOBALS :: "(globalinst list)"
	store_MEMS :: "(meminst list)"
	store_TABLES :: "(tableinst list)"
	store_FUNCS :: "(funcinst list)"
	store_DATAS :: "(datainst list)"
	store_ELEMS :: "(eleminst list)"
	STRUCTS :: "(structinst list)"
	ARRAYS :: "(arrayinst list)"
	EXNS :: "(exninst list)"

definition append_store :: "store ⇒ store ⇒ store" where
	"append_store arg1 arg2 = ⦇
		store_TAGS = store_TAGS arg1 @ store_TAGS arg2,
		store_GLOBALS = store_GLOBALS arg1 @ store_GLOBALS arg2,
		store_MEMS = store_MEMS arg1 @ store_MEMS arg2,
		store_TABLES = store_TABLES arg1 @ store_TABLES arg2,
		store_FUNCS = store_FUNCS arg1 @ store_FUNCS arg2,
		store_DATAS = store_DATAS arg1 @ store_DATAS arg2,
		store_ELEMS = store_ELEMS arg1 @ store_ELEMS arg2,
		STRUCTS = STRUCTS arg1 @ STRUCTS arg2,
		ARRAYS = ARRAYS arg1 @ ARRAYS arg2,
		EXNS = EXNS arg1 @ EXNS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:118.8-118.13 *)
inductive wf_store :: "store ⇒ bool" where
	  store_case_underscore :
		"list_all (λ (var_0 :: taginst). (wf_taginst var_0)) var_0 ⟹
		 list_all (λ (var_1 :: globalinst). (wf_globalinst var_1)) var_1 ⟹
		 list_all (λ (var_2 :: meminst). (wf_meminst var_2)) var_2 ⟹
		 list_all (λ (var_3 :: tableinst). (wf_tableinst var_3)) var_3 ⟹
		 list_all (λ (var_4 :: funcinst). (wf_funcinst var_4)) var_4 ⟹
		 list_all (λ (var_5 :: datainst). (wf_datainst var_5)) var_5 ⟹
		 list_all (λ (var_6 :: eleminst). (wf_eleminst var_6)) var_6 ⟹
		 list_all (λ (var_7 :: structinst). (wf_structinst var_7)) var_7 ⟹
		 list_all (λ (var_8 :: arrayinst). (wf_arrayinst var_8)) var_8 ⟹
		 list_all (λ (var_9 :: exninst). (wf_exninst var_9)) var_9 ⟹
		 wf_store ⦇ store_TAGS = var_0, store_GLOBALS = var_1, store_MEMS = var_2, store_TABLES = var_3, store_FUNCS = var_4, store_DATAS = var_5, store_ELEMS = var_6, STRUCTS = var_7, ARRAYS = var_8, EXNS = var_9 ⦈"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:147.1-147.47 *)
datatype state =
	  mk_state "store" "frame"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:147.8-147.13 *)
inductive wf_state :: "state ⇒ bool" where
	  state_case_0 :
		"(wf_store v_store) ⟹
		 (wf_frame v_frame) ⟹
		 wf_state (mk_state v_store v_frame)"

(* Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:148.1-148.57 *)
datatype config =
	  mk_config "state" "(instr list)"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:148.8-148.14 *)
inductive wf_config :: "config ⇒ bool" where
	  config_case_0 :
		"(wf_state v_state) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_config (mk_config v_state instr_lst)"

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:175.1-175.31 *)
definition Ki :: "nat" where
	"Ki = 1024"

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:181.1-181.114 *)
function (sequential) packfield__V128 :: "val ⇒ (fieldval option)" where
		  "packfield__V128 v_val = (Some (fieldval_val v_val))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:181.1-181.114 *)
function (sequential) packfield__REF :: "(null option) ⇒ heaptype ⇒ val ⇒ (fieldval option)" where
		  "packfield__REF null_opt v_heaptype v_val = (Some (fieldval_val v_val))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:181.1-181.114 *)
function (sequential) packfield__I8 :: "val ⇒ (fieldval option)" where
		  "packfield__I8 (res_CONST numtype_I32 (mk_num__0 I32 i)) = (Some (fieldval_PACK packtype_I8 (wrap__underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) (psize packtype_I8) i)))"
		| "packfield__I8 x1 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:181.1-181.114 *)
function (sequential) packfield__I64 :: "val ⇒ (fieldval option)" where
		  "packfield__I64 v_val = (Some (fieldval_val v_val))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:181.1-181.114 *)
function (sequential) packfield__I32 :: "val ⇒ (fieldval option)" where
		  "packfield__I32 v_val = (Some (fieldval_val v_val))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:181.1-181.114 *)
function (sequential) packfield__I16 :: "val ⇒ (fieldval option)" where
		  "packfield__I16 (res_CONST numtype_I32 (mk_num__0 I32 i)) = (Some (fieldval_PACK packtype_I16 (wrap__underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) (psize packtype_I16) i)))"
		| "packfield__I16 x1 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:181.1-181.114 *)
function (sequential) packfield__F64 :: "val ⇒ (fieldval option)" where
		  "packfield__F64 v_val = (Some (fieldval_val v_val))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:181.1-181.114 *)
function (sequential) packfield__F32 :: "val ⇒ (fieldval option)" where
		  "packfield__F32 v_val = (Some (fieldval_val v_val))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:181.1-181.114 *)
function (sequential) packfield__BOT :: "val ⇒ (fieldval option)" where
		  "packfield__BOT v_val = (Some (fieldval_val v_val))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:181.1-181.114 *)
function (sequential) packfield_underscore :: "storagetype ⇒ val ⇒ (fieldval option)" where
		  "packfield_underscore storagetype_V128 v_val = (packfield__V128 v_val)"
		| "packfield_underscore (storagetype_REF constructor_parameter_0 constructor_parameter_1) v_val = (packfield__REF constructor_parameter_0 constructor_parameter_1 v_val)"
		| "packfield_underscore I8 v_val = (packfield__I8 v_val)"
		| "packfield_underscore storagetype_I64 v_val = (packfield__I64 v_val)"
		| "packfield_underscore storagetype_I32 v_val = (packfield__I32 v_val)"
		| "packfield_underscore I16 v_val = (packfield__I16 v_val)"
		| "packfield_underscore storagetype_F64 v_val = (packfield__F64 v_val)"
		| "packfield_underscore storagetype_F32 v_val = (packfield__F32 v_val)"
		| "packfield_underscore storagetype_BOT v_val = (packfield__BOT v_val)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:182.1-182.126 *)
function (sequential) unpackfield__V128 :: "(sx option) ⇒ fieldval ⇒ (val option)" where
		  "unpackfield__V128 None (fieldval_REF_NULL heaptype_0) = (Some (REF_NULL heaptype_0))"
		| "unpackfield__V128 None (fieldval_REF_EXTERN v_addrref) = (Some (val_REF_EXTERN v_addrref))"
		| "unpackfield__V128 None (fieldval_REF_HOST_ADDR v_hostaddr) = (Some (val_REF_HOST_ADDR v_hostaddr))"
		| "unpackfield__V128 None (fieldval_REF_EXN_ADDR v_exnaddr) = (Some (val_REF_EXN_ADDR v_exnaddr))"
		| "unpackfield__V128 None (fieldval_REF_FUNC_ADDR v_funcaddr) = (Some (val_REF_FUNC_ADDR v_funcaddr))"
		| "unpackfield__V128 None (fieldval_REF_ARRAY_ADDR v_arrayaddr) = (Some (val_REF_ARRAY_ADDR v_arrayaddr))"
		| "unpackfield__V128 None (fieldval_REF_STRUCT_ADDR v_structaddr) = (Some (val_REF_STRUCT_ADDR v_structaddr))"
		| "unpackfield__V128 None (fieldval_REF_I31_NUM v_u31) = (Some (val_REF_I31_NUM v_u31))"
		| "unpackfield__V128 None (fieldval_VCONST v_vectype var_1) = (Some (VCONST v_vectype var_1))"
		| "unpackfield__V128 None (fieldval_CONST v_numtype var_0) = (Some (res_CONST v_numtype var_0))"
		| "unpackfield__V128 x1 x2 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:182.1-182.126 *)
function (sequential) unpackfield__REF :: "(null option) ⇒ heaptype ⇒ (sx option) ⇒ fieldval ⇒ (val option)" where
		  "unpackfield__REF null_opt v_heaptype None (fieldval_REF_NULL heaptype_0) = (Some (REF_NULL heaptype_0))"
		| "unpackfield__REF null_opt v_heaptype None (fieldval_REF_EXTERN v_addrref) = (Some (val_REF_EXTERN v_addrref))"
		| "unpackfield__REF null_opt v_heaptype None (fieldval_REF_HOST_ADDR v_hostaddr) = (Some (val_REF_HOST_ADDR v_hostaddr))"
		| "unpackfield__REF null_opt v_heaptype None (fieldval_REF_EXN_ADDR v_exnaddr) = (Some (val_REF_EXN_ADDR v_exnaddr))"
		| "unpackfield__REF null_opt v_heaptype None (fieldval_REF_FUNC_ADDR v_funcaddr) = (Some (val_REF_FUNC_ADDR v_funcaddr))"
		| "unpackfield__REF null_opt v_heaptype None (fieldval_REF_ARRAY_ADDR v_arrayaddr) = (Some (val_REF_ARRAY_ADDR v_arrayaddr))"
		| "unpackfield__REF null_opt v_heaptype None (fieldval_REF_STRUCT_ADDR v_structaddr) = (Some (val_REF_STRUCT_ADDR v_structaddr))"
		| "unpackfield__REF null_opt v_heaptype None (fieldval_REF_I31_NUM v_u31) = (Some (val_REF_I31_NUM v_u31))"
		| "unpackfield__REF null_opt v_heaptype None (fieldval_VCONST v_vectype var_1) = (Some (VCONST v_vectype var_1))"
		| "unpackfield__REF null_opt v_heaptype None (fieldval_CONST v_numtype var_0) = (Some (res_CONST v_numtype var_0))"
		| "unpackfield__REF constructor_parameter_0 constructor_parameter_1 x1 x2 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:182.1-182.126 *)
function (sequential) unpackfield__I8 :: "(sx option) ⇒ fieldval ⇒ (val option)" where
		  "unpackfield__I8 (Some v_sx) (fieldval_PACK packtype_I8 i) = (Some (res_CONST numtype_I32 (mk_num__0 I32 (extend__underscore (psize packtype_I8) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) v_sx i))))"
		| "unpackfield__I8 x1 x2 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:182.1-182.126 *)
function (sequential) unpackfield__I64 :: "(sx option) ⇒ fieldval ⇒ (val option)" where
		  "unpackfield__I64 None (fieldval_REF_NULL heaptype_0) = (Some (REF_NULL heaptype_0))"
		| "unpackfield__I64 None (fieldval_REF_EXTERN v_addrref) = (Some (val_REF_EXTERN v_addrref))"
		| "unpackfield__I64 None (fieldval_REF_HOST_ADDR v_hostaddr) = (Some (val_REF_HOST_ADDR v_hostaddr))"
		| "unpackfield__I64 None (fieldval_REF_EXN_ADDR v_exnaddr) = (Some (val_REF_EXN_ADDR v_exnaddr))"
		| "unpackfield__I64 None (fieldval_REF_FUNC_ADDR v_funcaddr) = (Some (val_REF_FUNC_ADDR v_funcaddr))"
		| "unpackfield__I64 None (fieldval_REF_ARRAY_ADDR v_arrayaddr) = (Some (val_REF_ARRAY_ADDR v_arrayaddr))"
		| "unpackfield__I64 None (fieldval_REF_STRUCT_ADDR v_structaddr) = (Some (val_REF_STRUCT_ADDR v_structaddr))"
		| "unpackfield__I64 None (fieldval_REF_I31_NUM v_u31) = (Some (val_REF_I31_NUM v_u31))"
		| "unpackfield__I64 None (fieldval_VCONST v_vectype var_1) = (Some (VCONST v_vectype var_1))"
		| "unpackfield__I64 None (fieldval_CONST v_numtype var_0) = (Some (res_CONST v_numtype var_0))"
		| "unpackfield__I64 x1 x2 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:182.1-182.126 *)
function (sequential) unpackfield__I32 :: "(sx option) ⇒ fieldval ⇒ (val option)" where
		  "unpackfield__I32 None (fieldval_REF_NULL heaptype_0) = (Some (REF_NULL heaptype_0))"
		| "unpackfield__I32 None (fieldval_REF_EXTERN v_addrref) = (Some (val_REF_EXTERN v_addrref))"
		| "unpackfield__I32 None (fieldval_REF_HOST_ADDR v_hostaddr) = (Some (val_REF_HOST_ADDR v_hostaddr))"
		| "unpackfield__I32 None (fieldval_REF_EXN_ADDR v_exnaddr) = (Some (val_REF_EXN_ADDR v_exnaddr))"
		| "unpackfield__I32 None (fieldval_REF_FUNC_ADDR v_funcaddr) = (Some (val_REF_FUNC_ADDR v_funcaddr))"
		| "unpackfield__I32 None (fieldval_REF_ARRAY_ADDR v_arrayaddr) = (Some (val_REF_ARRAY_ADDR v_arrayaddr))"
		| "unpackfield__I32 None (fieldval_REF_STRUCT_ADDR v_structaddr) = (Some (val_REF_STRUCT_ADDR v_structaddr))"
		| "unpackfield__I32 None (fieldval_REF_I31_NUM v_u31) = (Some (val_REF_I31_NUM v_u31))"
		| "unpackfield__I32 None (fieldval_VCONST v_vectype var_1) = (Some (VCONST v_vectype var_1))"
		| "unpackfield__I32 None (fieldval_CONST v_numtype var_0) = (Some (res_CONST v_numtype var_0))"
		| "unpackfield__I32 x1 x2 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:182.1-182.126 *)
function (sequential) unpackfield__I16 :: "(sx option) ⇒ fieldval ⇒ (val option)" where
		  "unpackfield__I16 (Some v_sx) (fieldval_PACK packtype_I16 i) = (Some (res_CONST numtype_I32 (mk_num__0 I32 (extend__underscore (psize packtype_I16) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) v_sx i))))"
		| "unpackfield__I16 x1 x2 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:182.1-182.126 *)
function (sequential) unpackfield__F64 :: "(sx option) ⇒ fieldval ⇒ (val option)" where
		  "unpackfield__F64 None (fieldval_REF_NULL heaptype_0) = (Some (REF_NULL heaptype_0))"
		| "unpackfield__F64 None (fieldval_REF_EXTERN v_addrref) = (Some (val_REF_EXTERN v_addrref))"
		| "unpackfield__F64 None (fieldval_REF_HOST_ADDR v_hostaddr) = (Some (val_REF_HOST_ADDR v_hostaddr))"
		| "unpackfield__F64 None (fieldval_REF_EXN_ADDR v_exnaddr) = (Some (val_REF_EXN_ADDR v_exnaddr))"
		| "unpackfield__F64 None (fieldval_REF_FUNC_ADDR v_funcaddr) = (Some (val_REF_FUNC_ADDR v_funcaddr))"
		| "unpackfield__F64 None (fieldval_REF_ARRAY_ADDR v_arrayaddr) = (Some (val_REF_ARRAY_ADDR v_arrayaddr))"
		| "unpackfield__F64 None (fieldval_REF_STRUCT_ADDR v_structaddr) = (Some (val_REF_STRUCT_ADDR v_structaddr))"
		| "unpackfield__F64 None (fieldval_REF_I31_NUM v_u31) = (Some (val_REF_I31_NUM v_u31))"
		| "unpackfield__F64 None (fieldval_VCONST v_vectype var_1) = (Some (VCONST v_vectype var_1))"
		| "unpackfield__F64 None (fieldval_CONST v_numtype var_0) = (Some (res_CONST v_numtype var_0))"
		| "unpackfield__F64 x1 x2 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:182.1-182.126 *)
function (sequential) unpackfield__F32 :: "(sx option) ⇒ fieldval ⇒ (val option)" where
		  "unpackfield__F32 None (fieldval_REF_NULL heaptype_0) = (Some (REF_NULL heaptype_0))"
		| "unpackfield__F32 None (fieldval_REF_EXTERN v_addrref) = (Some (val_REF_EXTERN v_addrref))"
		| "unpackfield__F32 None (fieldval_REF_HOST_ADDR v_hostaddr) = (Some (val_REF_HOST_ADDR v_hostaddr))"
		| "unpackfield__F32 None (fieldval_REF_EXN_ADDR v_exnaddr) = (Some (val_REF_EXN_ADDR v_exnaddr))"
		| "unpackfield__F32 None (fieldval_REF_FUNC_ADDR v_funcaddr) = (Some (val_REF_FUNC_ADDR v_funcaddr))"
		| "unpackfield__F32 None (fieldval_REF_ARRAY_ADDR v_arrayaddr) = (Some (val_REF_ARRAY_ADDR v_arrayaddr))"
		| "unpackfield__F32 None (fieldval_REF_STRUCT_ADDR v_structaddr) = (Some (val_REF_STRUCT_ADDR v_structaddr))"
		| "unpackfield__F32 None (fieldval_REF_I31_NUM v_u31) = (Some (val_REF_I31_NUM v_u31))"
		| "unpackfield__F32 None (fieldval_VCONST v_vectype var_1) = (Some (VCONST v_vectype var_1))"
		| "unpackfield__F32 None (fieldval_CONST v_numtype var_0) = (Some (res_CONST v_numtype var_0))"
		| "unpackfield__F32 x1 x2 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:182.1-182.126 *)
function (sequential) unpackfield__BOT :: "(sx option) ⇒ fieldval ⇒ (val option)" where
		  "unpackfield__BOT None (fieldval_REF_NULL heaptype_0) = (Some (REF_NULL heaptype_0))"
		| "unpackfield__BOT None (fieldval_REF_EXTERN v_addrref) = (Some (val_REF_EXTERN v_addrref))"
		| "unpackfield__BOT None (fieldval_REF_HOST_ADDR v_hostaddr) = (Some (val_REF_HOST_ADDR v_hostaddr))"
		| "unpackfield__BOT None (fieldval_REF_EXN_ADDR v_exnaddr) = (Some (val_REF_EXN_ADDR v_exnaddr))"
		| "unpackfield__BOT None (fieldval_REF_FUNC_ADDR v_funcaddr) = (Some (val_REF_FUNC_ADDR v_funcaddr))"
		| "unpackfield__BOT None (fieldval_REF_ARRAY_ADDR v_arrayaddr) = (Some (val_REF_ARRAY_ADDR v_arrayaddr))"
		| "unpackfield__BOT None (fieldval_REF_STRUCT_ADDR v_structaddr) = (Some (val_REF_STRUCT_ADDR v_structaddr))"
		| "unpackfield__BOT None (fieldval_REF_I31_NUM v_u31) = (Some (val_REF_I31_NUM v_u31))"
		| "unpackfield__BOT None (fieldval_VCONST v_vectype var_1) = (Some (VCONST v_vectype var_1))"
		| "unpackfield__BOT None (fieldval_CONST v_numtype var_0) = (Some (res_CONST v_numtype var_0))"
		| "unpackfield__BOT x1 x2 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:182.1-182.126 *)
function (sequential) unpackfield_underscore :: "storagetype ⇒ (sx option) ⇒ fieldval ⇒ (val option)" where
		  "unpackfield_underscore storagetype_V128 var_0 v_fieldval = (unpackfield__V128 var_0 v_fieldval)"
		| "unpackfield_underscore (storagetype_REF constructor_parameter_0 constructor_parameter_1) var_0 v_fieldval = (unpackfield__REF constructor_parameter_0 constructor_parameter_1 var_0 v_fieldval)"
		| "unpackfield_underscore I8 var_0 v_fieldval = (unpackfield__I8 var_0 v_fieldval)"
		| "unpackfield_underscore storagetype_I64 var_0 v_fieldval = (unpackfield__I64 var_0 v_fieldval)"
		| "unpackfield_underscore storagetype_I32 var_0 v_fieldval = (unpackfield__I32 var_0 v_fieldval)"
		| "unpackfield_underscore I16 var_0 v_fieldval = (unpackfield__I16 var_0 v_fieldval)"
		| "unpackfield_underscore storagetype_F64 var_0 v_fieldval = (unpackfield__F64 var_0 v_fieldval)"
		| "unpackfield_underscore storagetype_F32 var_0 v_fieldval = (unpackfield__F32 var_0 v_fieldval)"
		| "unpackfield_underscore storagetype_BOT var_0 v_fieldval = (unpackfield__BOT var_0 v_fieldval)"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:193.1-193.86 *)
inductive fun_tagsxa :: "(externaddr list) ⇒ (tagaddr list) ⇒ bool" where
	  fun_tagsxa_case_0 :
		"fun_tagsxa [] []"
	| fun_tagsxa_case_1 :
		"(fun_tagsxa xa_lst var_0) ⟹
		 fun_tagsxa ([(externaddr_TAG a)] @ xa_lst) ([a] @ var_0)"
	| fun_tagsxa_case_2 :
		"(fun_tagsxa xa_lst var_0) ⟹
		 fun_tagsxa ([v_externaddr] @ xa_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:194.1-194.89 *)
inductive fun_globalsxa :: "(externaddr list) ⇒ (globaladdr list) ⇒ bool" where
	  fun_globalsxa_case_0 :
		"fun_globalsxa [] []"
	| fun_globalsxa_case_1 :
		"(fun_globalsxa xa_lst var_0) ⟹
		 fun_globalsxa ([(externaddr_GLOBAL a)] @ xa_lst) ([a] @ var_0)"
	| fun_globalsxa_case_2 :
		"(fun_globalsxa xa_lst var_0) ⟹
		 fun_globalsxa ([v_externaddr] @ xa_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:195.1-195.86 *)
inductive fun_memsxa :: "(externaddr list) ⇒ (memaddr list) ⇒ bool" where
	  fun_memsxa_case_0 :
		"fun_memsxa [] []"
	| fun_memsxa_case_1 :
		"(fun_memsxa xa_lst var_0) ⟹
		 fun_memsxa ([(externaddr_MEM a)] @ xa_lst) ([a] @ var_0)"
	| fun_memsxa_case_2 :
		"(fun_memsxa xa_lst var_0) ⟹
		 fun_memsxa ([v_externaddr] @ xa_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:196.1-196.88 *)
inductive fun_tablesxa :: "(externaddr list) ⇒ (tableaddr list) ⇒ bool" where
	  fun_tablesxa_case_0 :
		"fun_tablesxa [] []"
	| fun_tablesxa_case_1 :
		"(fun_tablesxa xa_lst var_0) ⟹
		 fun_tablesxa ([(externaddr_TABLE a)] @ xa_lst) ([a] @ var_0)"
	| fun_tablesxa_case_2 :
		"(fun_tablesxa xa_lst var_0) ⟹
		 fun_tablesxa ([v_externaddr] @ xa_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:197.1-197.87 *)
inductive fun_funcsxa :: "(externaddr list) ⇒ (funcaddr list) ⇒ bool" where
	  fun_funcsxa_case_0 :
		"fun_funcsxa [] []"
	| fun_funcsxa_case_1 :
		"(fun_funcsxa xa_lst var_0) ⟹
		 fun_funcsxa ([(externaddr_FUNC a)] @ xa_lst) ([a] @ var_0)"
	| fun_funcsxa_case_2 :
		"(fun_funcsxa xa_lst var_0) ⟹
		 fun_funcsxa ([v_externaddr] @ xa_lst) var_0"

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:222.1-222.74 *)
function (sequential) fun_store :: "state ⇒ store" where
		  "fun_store (mk_state s f) = s"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:223.1-223.74 *)
function (sequential) fun_frame :: "state ⇒ frame" where
		  "fun_frame (mk_state s f) = f"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:228.1-228.80 *)
function (sequential) fun_tagaddr :: "state ⇒ (tagaddr list)" where
		  "fun_tagaddr (mk_state s f) = (moduleinst_TAGS (MODULE f))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:231.1-231.76 *)
function (sequential) fun_moduleinst :: "state ⇒ moduleinst" where
		  "fun_moduleinst (mk_state s f) = (MODULE f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:232.1-232.76 *)
function (sequential) fun_taginst :: "state ⇒ (taginst list)" where
		  "fun_taginst (mk_state s f) = (store_TAGS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:233.1-233.76 *)
function (sequential) fun_globalinst :: "state ⇒ (globalinst list)" where
		  "fun_globalinst (mk_state s f) = (store_GLOBALS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:234.1-234.76 *)
function (sequential) fun_meminst :: "state ⇒ (meminst list)" where
		  "fun_meminst (mk_state s f) = (store_MEMS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:235.1-235.76 *)
function (sequential) fun_tableinst :: "state ⇒ (tableinst list)" where
		  "fun_tableinst (mk_state s f) = (store_TABLES s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:236.1-236.76 *)
function (sequential) fun_funcinst :: "state ⇒ (funcinst list)" where
		  "fun_funcinst (mk_state s f) = (store_FUNCS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:237.1-237.76 *)
function (sequential) fun_datainst :: "state ⇒ (datainst list)" where
		  "fun_datainst (mk_state s f) = (store_DATAS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:238.1-238.76 *)
function (sequential) fun_eleminst :: "state ⇒ (eleminst list)" where
		  "fun_eleminst (mk_state s f) = (store_ELEMS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:239.1-239.76 *)
function (sequential) fun_structinst :: "state ⇒ (structinst list)" where
		  "fun_structinst (mk_state s f) = (STRUCTS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:240.1-240.76 *)
function (sequential) fun_arrayinst :: "state ⇒ (arrayinst list)" where
		  "fun_arrayinst (mk_state s f) = (ARRAYS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:241.1-241.76 *)
function (sequential) fun_exninst :: "state ⇒ (exninst list)" where
		  "fun_exninst (mk_state s f) = (EXNS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:256.1-256.85 *)
function (sequential) fun_type :: "state ⇒ typeidx ⇒ deftype" where
		  "fun_type (mk_state s f) x = ((moduleinst_TYPES (MODULE f)) ! (proj_uN_0 x))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:257.1-257.85 *)
function (sequential) fun_tag :: "state ⇒ tagidx ⇒ taginst" where
		  "fun_tag (mk_state s f) x = ((store_TAGS s) ! ((moduleinst_TAGS (MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:258.1-258.85 *)
function (sequential) fun_global :: "state ⇒ globalidx ⇒ globalinst" where
		  "fun_global (mk_state s f) x = ((store_GLOBALS s) ! ((moduleinst_GLOBALS (MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:259.1-259.85 *)
function (sequential) fun_mem :: "state ⇒ memidx ⇒ meminst" where
		  "fun_mem (mk_state s f) x = ((store_MEMS s) ! ((moduleinst_MEMS (MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:260.1-260.85 *)
function (sequential) fun_table :: "state ⇒ tableidx ⇒ tableinst" where
		  "fun_table (mk_state s f) x = ((store_TABLES s) ! ((moduleinst_TABLES (MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:261.1-261.85 *)
function (sequential) fun_func :: "state ⇒ funcidx ⇒ funcinst" where
		  "fun_func (mk_state s f) x = ((store_FUNCS s) ! ((moduleinst_FUNCS (MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:262.1-262.85 *)
function (sequential) fun_data :: "state ⇒ dataidx ⇒ datainst" where
		  "fun_data (mk_state s f) x = ((store_DATAS s) ! ((moduleinst_DATAS (MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:263.1-263.85 *)
function (sequential) fun_elem :: "state ⇒ tableidx ⇒ eleminst" where
		  "fun_elem (mk_state s f) x = ((store_ELEMS s) ! ((moduleinst_ELEMS (MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:264.1-264.85 *)
function (sequential) fun_local :: "state ⇒ localidx ⇒ (val option)" where
		  "fun_local (mk_state s f) x = ((frame_LOCALS f) ! (proj_uN_0 x))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:279.1-279.165 *)
function (sequential) with_local :: "state ⇒ localidx ⇒ val ⇒ state" where
		  "with_local (mk_state s f) x v = (mk_state s (f ⦇ frame_LOCALS := (list_update_func (frame_LOCALS f) (proj_uN_0 x) (λ (underscore_underscore :: (val option)). (Some v)))  ⦈))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:280.1-280.172 *)
function (sequential) with_global :: "state ⇒ globalidx ⇒ val ⇒ state" where
		  "with_global (mk_state s f) x v = (mk_state (s ⦇ store_GLOBALS := (list_update_func (store_GLOBALS s) ((moduleinst_GLOBALS (MODULE f)) ! (proj_uN_0 x)) (λ (var_1 :: globalinst). (var_1 ⦇ VALUE := v  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:281.1-281.174 *)
function (sequential) with_table :: "state ⇒ tableidx ⇒ nat ⇒ ref ⇒ state" where
		  "with_table (mk_state s f) x i r = (mk_state (s ⦇ store_TABLES := (list_update_func (store_TABLES s) ((moduleinst_TABLES (MODULE f)) ! (proj_uN_0 x)) (λ (var_1 :: tableinst). (var_1 ⦇ tableinst_REFS := (list_update_func (tableinst_REFS var_1) i (λ (underscore_underscore :: ref). r))  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:282.1-282.165 *)
function (sequential) with_tableinst :: "state ⇒ tableidx ⇒ tableinst ⇒ state" where
		  "with_tableinst (mk_state s f) x ti = (mk_state (s ⦇ store_TABLES := (list_update_func (store_TABLES s) ((moduleinst_TABLES (MODULE f)) ! (proj_uN_0 x)) (λ (underscore_underscore :: tableinst). ti))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:283.1-283.176 *)
function (sequential) with_mem :: "state ⇒ memidx ⇒ nat ⇒ nat ⇒ (byte list) ⇒ state" where
		  "with_mem (mk_state s f) x i j b_lst = (mk_state (s ⦇ store_MEMS := (list_update_func (store_MEMS s) ((moduleinst_MEMS (MODULE f)) ! (proj_uN_0 x)) (λ (var_1 :: meminst). (var_1 ⦇ BYTES := (list_slice_update (BYTES var_1) i j b_lst)  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:284.1-284.167 *)
function (sequential) with_meminst :: "state ⇒ memidx ⇒ meminst ⇒ state" where
		  "with_meminst (mk_state s f) x mi = (mk_state (s ⦇ store_MEMS := (list_update_func (store_MEMS s) ((moduleinst_MEMS (MODULE f)) ! (proj_uN_0 x)) (λ (underscore_underscore :: meminst). mi))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:285.1-285.169 *)
function (sequential) with_elem :: "state ⇒ elemidx ⇒ (ref list) ⇒ state" where
		  "with_elem (mk_state s f) x r_lst = (mk_state (s ⦇ store_ELEMS := (list_update_func (store_ELEMS s) ((moduleinst_ELEMS (MODULE f)) ! (proj_uN_0 x)) (λ (var_1 :: eleminst). (var_1 ⦇ eleminst_REFS := r_lst  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:286.1-286.170 *)
function (sequential) with_data :: "state ⇒ dataidx ⇒ (byte list) ⇒ state" where
		  "with_data (mk_state s f) x b_lst = (mk_state (s ⦇ store_DATAS := (list_update_func (store_DATAS s) ((moduleinst_DATAS (MODULE f)) ! (proj_uN_0 x)) (λ (var_1 :: datainst). (var_1 ⦇ datainst_BYTES := b_lst  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:287.1-287.181 *)
function (sequential) with_struct :: "state ⇒ structaddr ⇒ nat ⇒ fieldval ⇒ state" where
		  "with_struct (mk_state s f) a i fv = (mk_state (s ⦇ STRUCTS := (list_update_func (STRUCTS s) a (λ (var_1 :: structinst). (var_1 ⦇ FIELDS := (list_update_func (FIELDS var_1) i (λ (underscore_underscore :: fieldval). fv))  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:288.1-288.180 *)
function (sequential) with_array :: "state ⇒ arrayaddr ⇒ nat ⇒ fieldval ⇒ state" where
		  "with_array (mk_state s f) a i fv = (mk_state (s ⦇ ARRAYS := (list_update_func (ARRAYS s) a (λ (var_1 :: arrayinst). (var_1 ⦇ arrayinst_FIELDS := (list_update_func (arrayinst_FIELDS var_1) i (λ (underscore_underscore :: fieldval). fv))  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:302.1-302.140 *)
function (sequential) add_structinst :: "state ⇒ (structinst list) ⇒ state" where
		  "add_structinst (mk_state s f) si_lst = (mk_state (s ⦇ STRUCTS := ((STRUCTS s) @ si_lst)  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:303.1-303.139 *)
function (sequential) add_arrayinst :: "state ⇒ (arrayinst list) ⇒ state" where
		  "add_arrayinst (mk_state s f) ai_lst = (mk_state (s ⦇ ARRAYS := ((ARRAYS s) @ ai_lst)  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:304.1-304.137 *)
function (sequential) add_exninst :: "state ⇒ (exninst list) ⇒ state" where
		  "add_exninst (mk_state s f) exn_lst = (mk_state (s ⦇ EXNS := ((EXNS s) @ exn_lst)  ⦈) f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:313.6-313.16 *)
inductive fun_growtable :: "tableinst ⇒ nat ⇒ ref ⇒ (tableinst option) ⇒ bool" where
	  fun_growtable_case_0 :
		"(wf_tableinst ⦇ tableinst_TYPE = (mk_tabletype at (mk_limits i j_opt) rt), tableinst_REFS = r'_lst ⦈) ⟹
		 (wf_tableinst ⦇ tableinst_TYPE = (mk_tabletype at (mk_limits i' j_opt) rt), tableinst_REFS = (r'_lst @ (repeat v_n r)) ⦈) ⟹
		 (v_tableinst = ⦇ tableinst_TYPE = (mk_tabletype at (mk_limits i j_opt) rt), tableinst_REFS = r'_lst ⦈) ⟹
		 (tableinst' = ⦇ tableinst_TYPE = (mk_tabletype at (mk_limits i' j_opt) rt), tableinst_REFS = (r'_lst @ (repeat v_n r)) ⦈) ⟹
		 ((proj_uN_0 i') = ((length r'_lst) + v_n)) ⟹
		 list_all (λ (j :: u64). ((proj_uN_0 i') ≤ (proj_uN_0 j))) (option_to_list j_opt) ⟹
		 fun_growtable v_tableinst v_n r (Some tableinst')"
	| fun_growtable_case_1 :
		"True ⟹
		 fun_growtable x0 x1 x2 None"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:314.6-314.14 *)
inductive fun_growmem :: "meminst ⇒ nat ⇒ (meminst option) ⇒ bool" where
	  fun_growmem_case_0 :
		"(wf_meminst ⦇ meminst_TYPE = (PAGE at (mk_limits i j_opt)), BYTES = b_lst ⦈) ⟹
		 (wf_meminst ⦇ meminst_TYPE = (PAGE at (mk_limits i' j_opt)), BYTES = (b_lst @ (repeat (v_n * (64 * (Ki ))) (mk_byte 0))) ⦈) ⟹
		 (v_meminst = ⦇ meminst_TYPE = (PAGE at (mk_limits i j_opt)), BYTES = b_lst ⦈) ⟹
		 (meminst' = ⦇ meminst_TYPE = (PAGE at (mk_limits i' j_opt)), BYTES = (b_lst @ (repeat (v_n * (64 * (Ki ))) (mk_byte 0))) ⦈) ⟹
		 (((proj_uN_0 i') :: nat) = ((((length b_lst) :: nat) div ((64 * (Ki )) :: nat)) + (v_n :: nat))) ⟹
		 list_all (λ (j :: u64). ((proj_uN_0 i') ≤ (proj_uN_0 j))) (option_to_list j_opt) ⟹
		 fun_growmem v_meminst v_n (Some meminst')"
	| fun_growmem_case_1 :
		"True ⟹
		 fun_growmem x0 x1 None"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.1-execution.values.spectec:23.1-23.60 *)
inductive Num_ok :: "store ⇒ num ⇒ numtype ⇒ bool" where
	  mk_Num_ok :
		"Num_ok s (num_CONST nt c) nt"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.1-execution.values.spectec:24.1-24.60 *)
inductive Vec_ok :: "store ⇒ vec ⇒ vectype ⇒ bool" where
	  mk_Vec_ok :
		"Vec_ok s (vec_VCONST vt c) vt"

(* Mutual Recursion at: ../specification/wasm-3.0/4.1-execution.values.spectec:25.1-25.60 *)
inductive Ref_ok :: "store ⇒ ref ⇒ reftype ⇒ bool" where
	  Ref_ok__null :
		"(wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (Heaptype_sub ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈ ht' ht) ⟹
		 Ref_ok s (ref_REF_NULL ht) (reftype_REF (Some NULL) ht')"
	| i31 :
		"Ref_ok s (ref_REF_I31_NUM i) (reftype_REF None heaptype_I31)"
	| Ref_ok__struct :
		"(a < (length (STRUCTS s))) ⟹
		 ((structinst_TYPE ((STRUCTS s) ! a)) = dt) ⟹
		 Ref_ok s (ref_REF_STRUCT_ADDR a) (reftype_REF None (heaptype_deftype dt))"
	| Ref_ok__array :
		"(a < (length (ARRAYS s))) ⟹
		 ((arrayinst_TYPE ((ARRAYS s) ! a)) = dt) ⟹
		 Ref_ok s (ref_REF_ARRAY_ADDR a) (reftype_REF None (heaptype_deftype dt))"
	| Ref_ok__func :
		"(a < (length (store_FUNCS s))) ⟹
		 ((funcinst_TYPE ((store_FUNCS s) ! a)) = dt) ⟹
		 Ref_ok s (ref_REF_FUNC_ADDR a) (reftype_REF None (heaptype_deftype dt))"
	| exn :
		"(wf_exninst exn) ⟹
		 (a < (length (EXNS s))) ⟹
		 (((EXNS s) ! a) = exn) ⟹
		 Ref_ok s (ref_REF_EXN_ADDR a) (reftype_REF None heaptype_EXN)"
	| host :
		"Ref_ok s (ref_REF_HOST_ADDR a) (reftype_REF None heaptype_ANY)"
	| extern :
		"(wf_reftype (reftype_REF None heaptype_ANY)) ⟹
		 (Ref_ok s (ref_addrref v_addrref) (reftype_REF None heaptype_ANY)) ⟹
		 Ref_ok s (ref_REF_EXTERN v_addrref) (reftype_REF None heaptype_EXTERN)"
	| Ref_ok__sub :
		"(wf_reftype rt') ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (Ref_ok s v_ref rt') ⟹
		 (Reftype_sub ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈ rt' rt) ⟹
		 Ref_ok s v_ref rt"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.1-execution.values.spectec:26.1-26.60 *)
inductive Val_ok :: "store ⇒ val ⇒ valtype ⇒ bool" where
	  Val_ok__num :
		"(Num_ok s v_num nt) ⟹
		 Val_ok s (val_num v_num) (valtype_numtype nt)"
	| Val_ok__vec :
		"(Vec_ok s v_vec vt) ⟹
		 Val_ok s (val_vec v_vec) (valtype_vectype vt)"
	| Val_ok__ref :
		"(Ref_ok s v_ref rt) ⟹
		 Val_ok s (val_ref v_ref) (valtype_reftype rt)"

(* Mutual Recursion at: ../specification/wasm-3.0/4.1-execution.values.spectec:86.1-86.84 *)
inductive Externaddr_ok :: "store ⇒ externaddr ⇒ externtype ⇒ bool" where
	  Externaddr_ok__tag :
		"(a < (length (store_TAGS s))) ⟹
		 (((store_TAGS s) ! a) = v_taginst) ⟹
		 Externaddr_ok s (externaddr_TAG a) (externtype_TAG (taginst_TYPE v_taginst))"
	| Externaddr_ok__global :
		"(a < (length (store_GLOBALS s))) ⟹
		 (((store_GLOBALS s) ! a) = v_globalinst) ⟹
		 Externaddr_ok s (externaddr_GLOBAL a) (externtype_GLOBAL (globalinst_TYPE v_globalinst))"
	| Externaddr_ok__mem :
		"(a < (length (store_MEMS s))) ⟹
		 (((store_MEMS s) ! a) = v_meminst) ⟹
		 Externaddr_ok s (externaddr_MEM a) (externtype_MEM (meminst_TYPE v_meminst))"
	| Externaddr_ok__table :
		"(a < (length (store_TABLES s))) ⟹
		 (((store_TABLES s) ! a) = v_tableinst) ⟹
		 Externaddr_ok s (externaddr_TABLE a) (externtype_TABLE (tableinst_TYPE v_tableinst))"
	| Externaddr_ok__func :
		"(a < (length (store_FUNCS s))) ⟹
		 (((store_FUNCS s) ! a) = v_funcinst) ⟹
		 Externaddr_ok s (externaddr_FUNC a) (externtype_FUNC (typeuse_deftype (funcinst_TYPE v_funcinst)))"
	| Externaddr_ok__sub :
		"(wf_externtype xt') ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (Externaddr_ok s v_externaddr xt') ⟹
		 (Externtype_sub ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈ xt' xt) ⟹
		 Externaddr_ok s v_externaddr xt"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.2-execution.types.spectec:5.6-5.19 *)
inductive fun_inst_valtype :: "moduleinst ⇒ valtype ⇒ valtype ⇒ bool" where
	  fun_inst_valtype_case_0 :
		"(fun_subst_all_valtype t (map (λ (dt :: deftype). (typeuse_deftype dt)) dt_lst) var_0) ⟹
		 (dt_lst = (moduleinst_TYPES v_moduleinst)) ⟹
		 fun_inst_valtype v_moduleinst t var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.2-execution.types.spectec:6.6-6.19 *)
inductive fun_inst_reftype :: "moduleinst ⇒ reftype ⇒ reftype ⇒ bool" where
	  fun_inst_reftype_case_0 :
		"(fun_subst_all_reftype rt (map (λ (dt :: deftype). (typeuse_deftype dt)) dt_lst) var_0) ⟹
		 (dt_lst = (moduleinst_TYPES v_moduleinst)) ⟹
		 fun_inst_reftype v_moduleinst rt var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.2-execution.types.spectec:7.6-7.22 *)
inductive fun_inst_globaltype :: "moduleinst ⇒ globaltype ⇒ globaltype ⇒ bool" where
	  fun_inst_globaltype_case_0 :
		"(fun_subst_all_globaltype gt (map (λ (dt :: deftype). (typeuse_deftype dt)) dt_lst) var_0) ⟹
		 (dt_lst = (moduleinst_TYPES v_moduleinst)) ⟹
		 fun_inst_globaltype v_moduleinst gt var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.2-execution.types.spectec:8.6-8.19 *)
inductive fun_inst_memtype :: "moduleinst ⇒ memtype ⇒ memtype ⇒ bool" where
	  fun_inst_memtype_case_0 :
		"(fun_subst_all_memtype mt (map (λ (dt :: deftype). (typeuse_deftype dt)) dt_lst) var_0) ⟹
		 (dt_lst = (moduleinst_TYPES v_moduleinst)) ⟹
		 fun_inst_memtype v_moduleinst mt var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.2-execution.types.spectec:9.6-9.21 *)
inductive fun_inst_tabletype :: "moduleinst ⇒ tabletype ⇒ tabletype ⇒ bool" where
	  fun_inst_tabletype_case_0 :
		"(fun_subst_all_tabletype tt (map (λ (dt :: deftype). (typeuse_deftype dt)) dt_lst) var_0) ⟹
		 (dt_lst = (moduleinst_TYPES v_moduleinst)) ⟹
		 fun_inst_tabletype v_moduleinst tt var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:657.1-660.22 *)
inductive Step_pure_before_ref_eq_true :: "(instr list) ⇒ bool" where
	  ref_eq_null_0 :
		"(wf_ref (ref_REF_NULL ht_1)) ⟹
		 (wf_ref (ref_REF_NULL ht_2)) ⟹
		 ((ref_1 = (ref_REF_NULL ht_1)) ∧ (ref_2 = (ref_REF_NULL ht_2))) ⟹
		 Step_pure_before_ref_eq_true [(instr_ref ref_1), (instr_ref ref_2), (instr_sc4 REF_EQ)]"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:6.1-6.88 *)
inductive Step_pure :: "(instr list) ⇒ (instr list) ⇒ bool" where
	  Step_pure__unreachable :
		"Step_pure [(instr_sc0 UNREACHABLE)] [(instr_sc9 TRAP)]"
	| Step_pure__nop :
		"Step_pure [(instr_sc0 NOP)] []"
	| Step_pure__drop :
		"Step_pure [(instr_val v_val), (instr_sc0 DROP)] []"
	| select_true :
		"((proj_num__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 c)))) ≠ 0) ⟹
		 Step_pure [(instr_val val_1), (instr_val val_2), (instr_sc6 (instr_st6_CONST numtype_I32 c)), (instr_sc0 (SELECT t_lst_opt))] [(instr_val val_1)]"
	| select_false :
		"((proj_num__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 c)))) = 0) ⟹
		 Step_pure [(instr_val val_1), (instr_val val_2), (instr_sc6 (instr_st6_CONST numtype_I32 c)), (instr_sc0 (SELECT t_lst_opt))] [(instr_val val_2)]"
	| if_true :
		"((proj_num__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 c)))) ≠ 0) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST numtype_I32 c)), (instr_sc10 (IFELSE bt instr_1_lst instr_2_lst))] [(instr_sc9 (BLOCK bt instr_1_lst))]"
	| if_false :
		"((proj_num__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 c)))) = 0) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST numtype_I32 c)), (instr_sc10 (IFELSE bt instr_1_lst instr_2_lst))] [(instr_sc9 (BLOCK bt instr_2_lst))]"
	| label_vals :
		"Step_pure [(instr_sc10 (LABEL_underscore v_n instr_lst (map (λ (v_val :: val). (instr_val v_val)) val_lst)))] (map (λ (v_val :: val). (instr_val v_val)) val_lst)"
	| br_label_zero :
		"((proj_uN_0 l) = 0) ⟹
		 (v_n = (length val_lst)) ⟹
		 Step_pure [(instr_sc10 (LABEL_underscore v_n instr'_lst ((((map (λ (val' :: val). (instr_val val')) val'_lst) @ (map (λ (v_val :: val). (instr_val v_val)) val_lst)) @ [(instr_sc0 (BR l))]) @ instr_lst)))] ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ instr'_lst)"
	| br_label_succ :
		"((proj_uN_0 l) > 0) ⟹
		 Step_pure [(instr_sc10 (LABEL_underscore v_n instr'_lst (((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc0 (BR l))]) @ instr_lst)))] ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc0 (BR (mk_uN ((((proj_uN_0 l) :: nat) - (1 :: nat)) :: nat))))])"
	| br_handler :
		"Step_pure [(instr_sc10 (HANDLER_underscore v_n catch_lst (((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc0 (BR l))]) @ instr_lst)))] ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc0 (BR l))])"
	| br_if_true :
		"((proj_num__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 c)))) ≠ 0) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST numtype_I32 c)), (instr_sc0 (BR_IF l))] [(instr_sc0 (BR l))]"
	| br_if_false :
		"((proj_num__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 c)))) = 0) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST numtype_I32 c)), (instr_sc0 (BR_IF l))] []"
	| br_table_lt :
		"((proj_uN_0 (the ((proj_num__0 i)))) < (length l_lst)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc0 (BR_TABLE l_lst l'))] [(instr_sc0 (BR (l_lst ! (proj_uN_0 (the ((proj_num__0 i)))))))]"
	| br_table_ge :
		"((proj_num__0 i) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i)))) ≥ (length l_lst)) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc0 (BR_TABLE l_lst l'))] [(instr_sc0 (BR l'))]"
	| br_on_null_null :
		"(wf_val (REF_NULL ht)) ⟹
		 (v_val = (REF_NULL ht)) ⟹
		 Step_pure [(instr_val v_val), (instr_sc0 (BR_ON_NULL l))] [(instr_sc0 (BR l))]"
	| br_on_null_addr :
		"(v_val ≠ (REF_NULL ht)) ⟹
		 Step_pure [(instr_val v_val), (instr_sc0 (BR_ON_NULL l))] [(instr_val v_val)]"
	| br_on_non_null_null :
		"(wf_val (REF_NULL ht)) ⟹
		 (v_val = (REF_NULL ht)) ⟹
		 Step_pure [(instr_val v_val), (instr_sc0 (BR_ON_NON_NULL l))] []"
	| br_on_non_null_addr :
		"(v_val ≠ (REF_NULL ht)) ⟹
		 Step_pure [(instr_val v_val), (instr_sc0 (BR_ON_NON_NULL l))] [(instr_val v_val), (instr_sc0 (BR l))]"
	| Step_pure__call_indirect :
		"Step_pure [(instr_sc1 (CALL_INDIRECT x yy))] [(instr_sc2 (TABLE_GET x)), (instr_sc4 (REF_CAST (reftype_REF (Some NULL) (heaptype_typeuse yy)))), (instr_sc1 (CALL_REF yy))]"
	| Step_pure__return_call_indirect :
		"Step_pure [(instr_sc1 (RETURN_CALL_INDIRECT x yy))] [(instr_sc2 (TABLE_GET x)), (instr_sc4 (REF_CAST (reftype_REF (Some NULL) (heaptype_typeuse yy)))), (instr_sc1 (RETURN_CALL_REF yy))]"
	| frame_vals :
		"(v_n = (length val_lst)) ⟹
		 Step_pure [(instr_sc10 (FRAME_underscore v_n f (map (λ (v_val :: val). (instr_val v_val)) val_lst)))] (map (λ (v_val :: val). (instr_val v_val)) val_lst)"
	| return_frame :
		"(v_n = (length val_lst)) ⟹
		 Step_pure [(instr_sc10 (FRAME_underscore v_n f ((((map (λ (val' :: val). (instr_val val')) val'_lst) @ (map (λ (v_val :: val). (instr_val v_val)) val_lst)) @ [(instr_sc1 RETURN)]) @ instr_lst)))] (map (λ (v_val :: val). (instr_val v_val)) val_lst)"
	| return_label :
		"Step_pure [(instr_sc10 (LABEL_underscore v_n instr'_lst (((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc1 RETURN)]) @ instr_lst)))] ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc1 RETURN)])"
	| return_handler :
		"Step_pure [(instr_sc10 (HANDLER_underscore v_n catch_lst (((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc1 RETURN)]) @ instr_lst)))] ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc1 RETURN)])"
	| handler_vals :
		"Step_pure [(instr_sc10 (HANDLER_underscore v_n catch_lst (map (λ (v_val :: val). (instr_val v_val)) val_lst)))] (map (λ (v_val :: val). (instr_val v_val)) val_lst)"
	| trap_instrs :
		"((val_lst ≠ []) ∨ (instr_lst ≠ [])) ⟹
		 Step_pure ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ ([(instr_sc9 TRAP)] @ instr_lst)) [(instr_sc9 TRAP)]"
	| trap_label :
		"Step_pure [(instr_sc10 (LABEL_underscore v_n instr'_lst [(instr_sc9 TRAP)]))] [(instr_sc9 TRAP)]"
	| trap_handler :
		"Step_pure [(instr_sc10 (HANDLER_underscore v_n catch_lst [(instr_sc9 TRAP)]))] [(instr_sc9 TRAP)]"
	| trap_frame :
		"Step_pure [(instr_sc10 (FRAME_underscore v_n f [(instr_sc9 TRAP)]))] [(instr_sc9 TRAP)]"
	| Step_pure__local_tee :
		"Step_pure [(instr_val v_val), (instr_sc2 (LOCAL_TEE x))] [(instr_val v_val), (instr_val v_val), (instr_sc1 (LOCAL_SET x))]"
	| Step_pure__ref_i31 :
		"((proj_num__0 i) ≠ None) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc4 REF_I31)] [(instr_sc9 (instr_st9_REF_I31_NUM (wrap__underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))))))))))))))))))))) (the ((proj_num__0 i))))))]"
	| ref_is_null_true :
		"(wf_ref (ref_REF_NULL ht)) ⟹
		 (v_ref = (ref_REF_NULL ht)) ⟹
		 Step_pure [(instr_ref v_ref), (instr_sc4 REF_IS_NULL)] [(instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN 1))))]"
	| ref_is_null_false :
		"(v_ref ≠ (ref_REF_NULL ht)) ⟹
		 Step_pure [(instr_ref v_ref), (instr_sc4 REF_IS_NULL)] [(instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN 0))))]"
	| ref_as_non_null_null :
		"(wf_ref (ref_REF_NULL ht)) ⟹
		 (v_ref = (ref_REF_NULL ht)) ⟹
		 Step_pure [(instr_ref v_ref), (instr_sc4 REF_AS_NON_NULL)] [(instr_sc9 TRAP)]"
	| ref_as_non_null_addr :
		"(v_ref ≠ (ref_REF_NULL ht)) ⟹
		 Step_pure [(instr_ref v_ref), (instr_sc4 REF_AS_NON_NULL)] [(instr_ref v_ref)]"
	| ref_eq_null :
		"(wf_ref (ref_REF_NULL ht_1)) ⟹
		 (wf_ref (ref_REF_NULL ht_2)) ⟹
		 ((ref_1 = (ref_REF_NULL ht_1)) ∧ (ref_2 = (ref_REF_NULL ht_2))) ⟹
		 Step_pure [(instr_ref ref_1), (instr_ref ref_2), (instr_sc4 REF_EQ)] [(instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN 1))))]"
	| ref_eq_true :
		"((ref_1 ≠ (ref_REF_NULL ht_1)) ∨ (ref_2 ≠ (ref_REF_NULL ht_2))) ⟹
		 (ref_1 = ref_2) ⟹
		 Step_pure [(instr_ref ref_1), (instr_ref ref_2), (instr_sc4 REF_EQ)] [(instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN 1))))]"
	| ref_eq_false :
		"(ref_1 ≠ ref_2) ⟹
		 ((ref_1 ≠ (ref_REF_NULL ht_1)) ∨ (ref_2 ≠ (ref_REF_NULL ht_2))) ⟹
		 Step_pure [(instr_ref ref_1), (instr_ref ref_2), (instr_sc4 REF_EQ)] [(instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN 0))))]"
	| i31_get_null :
		"Step_pure [(instr_sc4 (instr_st4_REF_NULL ht)), (instr_sc4 (I31_GET v_sx))] [(instr_sc9 TRAP)]"
	| i31_get_num :
		"Step_pure [(instr_sc9 (instr_st9_REF_I31_NUM i)), (instr_sc4 (I31_GET v_sx))] [(instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (extend__underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))))))))))))))))))))) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) v_sx i))))]"
	| Step_pure__array_new :
		"Step_pure [(instr_val v_val), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc5 (ARRAY_NEW x))] ((repeat v_n (instr_val v_val)) @ [(instr_sc5 (ARRAY_NEW_FIXED x (mk_uN v_n)))])"
	| extern_convert_any_null :
		"Step_pure [(instr_sc4 (instr_st4_REF_NULL ht)), (instr_sc6 EXTERN_CONVERT_ANY)] [(instr_sc4 (instr_st4_REF_NULL heaptype_EXTERN))]"
	| extern_convert_any_addr :
		"Step_pure [(instr_addrref v_addrref), (instr_sc6 EXTERN_CONVERT_ANY)] [(instr_sc9 (instr_st9_REF_EXTERN v_addrref))]"
	| any_convert_extern_null :
		"Step_pure [(instr_sc4 (instr_st4_REF_NULL ht)), (instr_sc6 ANY_CONVERT_EXTERN)] [(instr_sc4 (instr_st4_REF_NULL heaptype_ANY))]"
	| any_convert_extern_addr :
		"Step_pure [(instr_sc9 (instr_st9_REF_EXTERN v_addrref)), (instr_sc6 ANY_CONVERT_EXTERN)] [(instr_addrref v_addrref)]"
	| unop_val :
		"(fun_unop_underscore nt unop c_1 var_0) ⟹
		 list_all (λ (iter :: num_underscore). (wf_num_underscore nt iter)) var_0 ⟹
		 ((length var_0) > 0) ⟹
		 (c ∈ set var_0) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST nt c_1)), (instr_sc6 (UNOP nt unop))] [(instr_sc6 (instr_st6_CONST nt c))]"
	| unop_trap :
		"(fun_unop_underscore nt unop c_1 var_0) ⟹
		 list_all (λ (iter :: num_underscore). (wf_num_underscore nt iter)) var_0 ⟹
		 (var_0 = []) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST nt c_1)), (instr_sc6 (UNOP nt unop))] [(instr_sc9 TRAP)]"
	| binop_val :
		"(fun_binop_underscore nt binop c_1 c_2 var_0) ⟹
		 list_all (λ (iter :: num_underscore). (wf_num_underscore nt iter)) var_0 ⟹
		 ((length var_0) > 0) ⟹
		 (c ∈ set var_0) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST nt c_1)), (instr_sc6 (instr_st6_CONST nt c_2)), (instr_sc6 (BINOP nt binop))] [(instr_sc6 (instr_st6_CONST nt c))]"
	| binop_trap :
		"(fun_binop_underscore nt binop c_1 c_2 var_0) ⟹
		 list_all (λ (iter :: num_underscore). (wf_num_underscore nt iter)) var_0 ⟹
		 (var_0 = []) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST nt c_1)), (instr_sc6 (instr_st6_CONST nt c_2)), (instr_sc6 (BINOP nt binop))] [(instr_sc9 TRAP)]"
	| Step_pure__testop :
		"(wf_uN 32 (fun_testop_underscore nt testop c_1)) ⟹
		 ((proj_num__0 c) ≠ None) ⟹
		 ((the ((proj_num__0 c))) = (fun_testop_underscore nt testop c_1)) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST nt c_1)), (instr_sc6 (TESTOP nt testop))] [(instr_sc6 (instr_st6_CONST numtype_I32 c))]"
	| Step_pure__relop :
		"(wf_uN 32 (fun_relop_underscore nt relop c_1 c_2)) ⟹
		 ((proj_num__0 c) ≠ None) ⟹
		 ((the ((proj_num__0 c))) = (fun_relop_underscore nt relop c_1 c_2)) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST nt c_1)), (instr_sc6 (instr_st6_CONST nt c_2)), (instr_sc6 (RELOP nt relop))] [(instr_sc6 (instr_st6_CONST numtype_I32 c))]"
	| cvtop_val :
		"(fun_cvtop__underscore nt_1 nt_2 cvtop c_1 var_0) ⟹
		 list_all (λ (iter :: num_underscore). (wf_num_underscore nt_2 iter)) var_0 ⟹
		 ((length var_0) > 0) ⟹
		 (c ∈ set var_0) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST nt_1 c_1)), (instr_sc7 (CVTOP nt_2 nt_1 cvtop))] [(instr_sc6 (instr_st6_CONST nt_2 c))]"
	| cvtop_trap :
		"(fun_cvtop__underscore nt_1 nt_2 cvtop c_1 var_0) ⟹
		 list_all (λ (iter :: num_underscore). (wf_num_underscore nt_2 iter)) var_0 ⟹
		 (var_0 = []) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST nt_1 c_1)), (instr_sc7 (CVTOP nt_2 nt_1 cvtop))] [(instr_sc9 TRAP)]"
	| Step_pure__vvunop :
		"list_all (λ (iter :: vec_underscore). (wf_uN 128 iter)) (vvunop_underscore V128 v_vvunop c_1) ⟹
		 ((length (vvunop_underscore V128 v_vvunop c_1)) > 0) ⟹
		 (c ∈ set (vvunop_underscore V128 v_vvunop c_1)) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (VVUNOP V128 v_vvunop))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| Step_pure__vvbinop :
		"list_all (λ (iter :: vec_underscore). (wf_uN 128 iter)) (vvbinop_underscore V128 v_vvbinop c_1 c_2) ⟹
		 ((length (vvbinop_underscore V128 v_vvbinop c_1 c_2)) > 0) ⟹
		 (c ∈ set (vvbinop_underscore V128 v_vvbinop c_1 c_2)) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (instr_st7_VCONST V128 c_2)), (instr_sc7 (VVBINOP V128 v_vvbinop))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| Step_pure__vvternop :
		"list_all (λ (iter :: vec_underscore). (wf_uN 128 iter)) (vvternop_underscore V128 v_vvternop c_1 c_2 c_3) ⟹
		 ((length (vvternop_underscore V128 v_vvternop c_1 c_2 c_3)) > 0) ⟹
		 (c ∈ set (vvternop_underscore V128 v_vvternop c_1 c_2 c_3)) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (instr_st7_VCONST V128 c_2)), (instr_sc7 (instr_st7_VCONST V128 c_3)), (instr_sc7 (VVTERNOP V128 v_vvternop))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| Step_pure__vvtestop :
		"(wf_uN 32 (inez_underscore (vsize V128) c_1)) ⟹
		 ((proj_num__0 c) ≠ None) ⟹
		 ((the ((proj_num__0 c))) = (inez_underscore (vsize V128) c_1)) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (VVTESTOP V128 ANY_TRUE))] [(instr_sc6 (instr_st6_CONST numtype_I32 c))]"
	| vunop_val :
		"(fun_vunop_underscore sh vunop c_1 var_0) ⟹
		 list_all (λ (iter :: vec_underscore). (wf_uN 128 iter)) var_0 ⟹
		 ((length var_0) > 0) ⟹
		 (c ∈ set var_0) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (VUNOP sh vunop))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| vunop_trap :
		"(fun_vunop_underscore sh vunop c_1 var_0) ⟹
		 list_all (λ (iter :: vec_underscore). (wf_uN 128 iter)) var_0 ⟹
		 (var_0 = []) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (VUNOP sh vunop))] [(instr_sc9 TRAP)]"
	| vbinop_val :
		"(fun_vbinop_underscore sh vbinop c_1 c_2 var_0) ⟹
		 list_all (λ (iter :: vec_underscore). (wf_uN 128 iter)) var_0 ⟹
		 ((length var_0) > 0) ⟹
		 (c ∈ set var_0) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (instr_st7_VCONST V128 c_2)), (instr_sc7 (VBINOP sh vbinop))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| vbinop_trap :
		"(fun_vbinop_underscore sh vbinop c_1 c_2 var_0) ⟹
		 list_all (λ (iter :: vec_underscore). (wf_uN 128 iter)) var_0 ⟹
		 (var_0 = []) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (instr_st7_VCONST V128 c_2)), (instr_sc7 (VBINOP sh vbinop))] [(instr_sc9 TRAP)]"
	| vternop_val :
		"(fun_vternop_underscore sh vternop c_1 c_2 c_3 var_0) ⟹
		 list_all (λ (iter :: vec_underscore). (wf_uN 128 iter)) var_0 ⟹
		 ((length var_0) > 0) ⟹
		 (c ∈ set var_0) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (instr_st7_VCONST V128 c_2)), (instr_sc7 (instr_st7_VCONST V128 c_3)), (instr_sc7 (VTERNOP sh vternop))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| vternop_trap :
		"(fun_vternop_underscore sh vternop c_1 c_2 c_3 var_0) ⟹
		 list_all (λ (iter :: vec_underscore). (wf_uN 128 iter)) var_0 ⟹
		 (var_0 = []) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (instr_st7_VCONST V128 c_2)), (instr_sc7 (instr_st7_VCONST V128 c_3)), (instr_sc7 (VTERNOP sh vternop))] [(instr_sc9 TRAP)]"
	| Step_pure__vtestop :
		"list_all (λ (i :: lane_underscore). ((proj_lane__2 i) ≠ None)) i_lst ⟹
		 (fun_prod (map (λ (i :: lane_underscore). (proj_uN_0 (inez_underscore (jsizenn v_Jnn) (the ((proj_lane__2 i)))))) i_lst) var_0) ⟹
		 list_all (λ (i :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) i)) i_lst ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) iter)) (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c_1) ⟹
		 list_all (λ (i :: lane_underscore). (wf_uN 32 (inez_underscore (jsizenn v_Jnn) (the ((proj_lane__2 i)))))) i_lst ⟹
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) ⟹
		 (i_lst = (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c_1)) ⟹
		 ((proj_num__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 c)))) = var_0) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (mk_vtestop__0 v_Jnn v_M ALL_TRUE)))] [(instr_sc6 (instr_st6_CONST numtype_I32 c))]"
	| Step_pure__vrelop :
		"(fun_vrelop_underscore sh vrelop c_1 c_2 var_0) ⟹
		 (wf_uN 128 var_0) ⟹
		 (c = var_0) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (instr_st7_VCONST V128 c_2)), (instr_sc7 (VRELOP sh vrelop))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| Step_pure__vshiftop :
		"((proj_num__0 i) ≠ None) ⟹
		 (fun_vshiftop_underscore sh vshiftop c_1 (the ((proj_num__0 i))) var_0) ⟹
		 (wf_uN 128 var_0) ⟹
		 (c = var_0) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc8 (VSHIFTOP sh vshiftop))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| Step_pure__vbitmask :
		"(fun_vbitmaskop_underscore sh c_1 var_0) ⟹
		 (wf_uN 32 var_0) ⟹
		 ((proj_num__0 c) ≠ None) ⟹
		 ((the ((proj_num__0 c))) = var_0) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc8 (VBITMASK sh))] [(instr_sc6 (instr_st6_CONST numtype_I32 c))]"
	| Step_pure__vswizzlop :
		"(fun_vswizzlop_underscore sh swizzlop c_1 c_2 var_0) ⟹
		 (wf_uN 128 var_0) ⟹
		 (c = var_0) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (instr_st7_VCONST V128 c_2)), (instr_sc8 (VSWIZZLOP sh swizzlop))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| Step_pure__vshuffle :
		"(fun_vshufflop_underscore sh i_lst c_1 c_2 var_0) ⟹
		 (wf_uN 128 var_0) ⟹
		 (c = var_0) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (instr_st7_VCONST V128 c_2)), (instr_sc8 (VSHUFFLE sh i_lst))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| Step_pure__vsplat :
		"(wf_uN 128 (inv_lanes_underscore (X v_Lnn (mk_dim v_M)) (repeat v_M (lpacknum_underscore v_Lnn c_1)))) ⟹
		 (wf_lane_underscore (fun_lanetype (X v_Lnn (mk_dim v_M))) (lpacknum_underscore v_Lnn c_1)) ⟹
		 (wf_shape (X v_Lnn (mk_dim v_M))) ⟹
		 (c = (inv_lanes_underscore (X v_Lnn (mk_dim v_M)) (repeat v_M (lpacknum_underscore v_Lnn c_1)))) ⟹
		 Step_pure [(instr_sc6 (instr_st6_CONST (lunpack v_Lnn) c_1)), (instr_sc8 (VSPLAT (X v_Lnn (mk_dim v_M))))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| vextract_lane_num :
		"list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_numtype nt) (mk_dim v_M))) iter)) (lanes_underscore (X (lanetype_numtype nt) (mk_dim v_M)) c_1) ⟹
		 (wf_lane_underscore (fun_lanetype (X (lanetype_numtype nt) (mk_dim v_M))) (mk_lane__0 nt c_2)) ⟹
		 (wf_shape (X (lanetype_numtype nt) (mk_dim v_M))) ⟹
		 ((proj_uN_0 i) < (length (lanes_underscore (X (lanetype_numtype nt) (mk_dim v_M)) c_1))) ⟹
		 ((mk_lane__0 nt c_2) = ((lanes_underscore (X (lanetype_numtype nt) (mk_dim v_M)) c_1) ! (proj_uN_0 i))) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc8 (VEXTRACT_LANE (X (lanetype_numtype nt) (mk_dim v_M)) None i))] [(instr_sc6 (instr_st6_CONST nt c_2))]"
	| vextract_lane_pack :
		"((proj_lane__1 ((lanes_underscore (X (lanetype_packtype pt) (mk_dim v_M)) c_1) ! (proj_uN_0 i))) ≠ None) ⟹
		 ((proj_uN_0 i) < (length (lanes_underscore (X (lanetype_packtype pt) (mk_dim v_M)) c_1))) ⟹
		 (wf_uN 32 (extend__underscore (psize pt) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) v_sx (the ((proj_lane__1 ((lanes_underscore (X (lanetype_packtype pt) (mk_dim v_M)) c_1) ! (proj_uN_0 i))))))) ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_packtype pt) (mk_dim v_M))) iter)) (lanes_underscore (X (lanetype_packtype pt) (mk_dim v_M)) c_1) ⟹
		 (wf_shape (X (lanetype_packtype pt) (mk_dim v_M))) ⟹
		 ((proj_num__0 c_2) ≠ None) ⟹
		 ((the ((proj_num__0 c_2))) = (extend__underscore (psize pt) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) v_sx (the ((proj_lane__1 ((lanes_underscore (X (lanetype_packtype pt) (mk_dim v_M)) c_1) ! (proj_uN_0 i))))))) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc8 (VEXTRACT_LANE (X (lanetype_packtype pt) (mk_dim v_M)) (Some v_sx) i))] [(instr_sc6 (instr_st6_CONST numtype_I32 c_2))]"
	| Step_pure__vreplace_lane :
		"(wf_uN 128 (inv_lanes_underscore (X v_Lnn (mk_dim v_M)) (list_update_func (lanes_underscore (X v_Lnn (mk_dim v_M)) c_1) (proj_uN_0 i) (λ (underscore_underscore :: lane_underscore). (lpacknum_underscore v_Lnn c_2))))) ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X v_Lnn (mk_dim v_M))) iter)) (lanes_underscore (X v_Lnn (mk_dim v_M)) c_1) ⟹
		 (wf_lane_underscore (fun_lanetype (X v_Lnn (mk_dim v_M))) (lpacknum_underscore v_Lnn c_2)) ⟹
		 (wf_shape (X v_Lnn (mk_dim v_M))) ⟹
		 (c = (inv_lanes_underscore (X v_Lnn (mk_dim v_M)) (list_update_func (lanes_underscore (X v_Lnn (mk_dim v_M)) c_1) (proj_uN_0 i) (λ (underscore_underscore :: lane_underscore). (lpacknum_underscore v_Lnn c_2))))) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc6 (instr_st6_CONST (lunpack v_Lnn) c_2)), (instr_sc9 (VREPLACE_LANE (X v_Lnn (mk_dim v_M)) i))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| Step_pure__vextunop :
		"(fun_vextunop__underscore sh_1 sh_2 vextunop c_1 var_0) ⟹
		 (wf_uN 128 var_0) ⟹
		 (var_0 = c) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc8 (VEXTUNOP sh_2 sh_1 vextunop))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| Step_pure__vextbinop :
		"(fun_vextbinop__underscore sh_1 sh_2 vextbinop c_1 c_2 var_0) ⟹
		 (wf_uN 128 var_0) ⟹
		 (var_0 = c) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (instr_st7_VCONST V128 c_2)), (instr_sc8 (VEXTBINOP sh_2 sh_1 vextbinop))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| Step_pure__vextternop :
		"(fun_vextternop__underscore sh_1 sh_2 vextternop c_1 c_2 c_3 var_0) ⟹
		 (wf_uN 128 var_0) ⟹
		 (var_0 = c) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (instr_st7_VCONST V128 c_2)), (instr_sc7 (instr_st7_VCONST V128 c_3)), (instr_sc8 (VEXTTERNOP sh_2 sh_1 vextternop))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| Step_pure__vnarrow :
		"(fun_vnarrowop__underscore (proj_ishape_0 sh_1) (proj_ishape_0 sh_2) v_sx c_1 c_2 var_0) ⟹
		 (wf_uN 128 var_0) ⟹
		 (c = var_0) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc7 (instr_st7_VCONST V128 c_2)), (instr_sc8 (VNARROW sh_2 sh_1 v_sx))] [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| Step_pure__vcvtop :
		"(fun_vcvtop__underscore sh_1 sh_2 vcvtop c_1 var_0) ⟹
		 (wf_uN 128 var_0) ⟹
		 (c = var_0) ⟹
		 Step_pure [(instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc8 (VCVTOP sh_2 sh_1 vcvtop))] [(instr_sc7 (instr_st7_VCONST V128 c))]"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:73.6-73.17 *)
inductive fun_blocktype_underscore :: "state ⇒ blocktype ⇒ instrtype ⇒ bool" where
	  fun_blocktype__case_0 :
		"(wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (Expand (fun_type z x) (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 fun_blocktype_underscore z (blocktype__IDX x) (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))"
	| fun_blocktype__case_1 :
		"fun_blocktype_underscore z (underscore_RESULT t_opt) (mk_instrtype (mk_list []) [] (mk_list (option_to_list t_opt)))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:155.1-157.15 *)
inductive Step_read_before_br_on_cast_fail :: "config ⇒ bool" where
	  br_on_cast_succeed_0 :
		"(fun_inst_reftype (MODULE f) rt_2 var_0) ⟹
		 (wf_reftype rt) ⟹
		 (wf_reftype var_0) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (Ref_ok s v_ref rt) ⟹
		 (Reftype_sub ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈ rt var_0) ⟹
		 Step_read_before_br_on_cast_fail (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc0 (BR_ON_CAST l rt_1 rt_2))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:166.1-168.15 *)
inductive Step_read_before_br_on_cast_fail_fail :: "config ⇒ bool" where
	  br_on_cast_fail_succeed_0 :
		"(fun_inst_reftype (MODULE f) rt_2 var_0) ⟹
		 (wf_reftype rt) ⟹
		 (wf_reftype var_0) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (Ref_ok s v_ref rt) ⟹
		 (Reftype_sub ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈ rt var_0) ⟹
		 Step_read_before_br_on_cast_fail_fail (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc0 (BR_ON_CAST_FAIL l rt_1 rt_2))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:272.1-275.15 *)
inductive Step_read_before_throw_ref_handler_next :: "config ⇒ bool" where
	  throw_ref_handler_catch_all_ref_0 :
		"Step_read_before_throw_ref_handler_next (mk_config z [(instr_sc10 (HANDLER_underscore v_n ([(CATCH_ALL_REF l)] @ catch'_lst) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]))])"
	| throw_ref_handler_catch_all_0 :
		"Step_read_before_throw_ref_handler_next (mk_config z [(instr_sc10 (HANDLER_underscore v_n ([(CATCH_ALL l)] @ catch'_lst) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]))])"
	| throw_ref_handler_catch_ref_0 :
		"list_all (λ (iter :: exninst). (wf_exninst iter)) (fun_exninst z) ⟹
		 (a < (length (fun_exninst z))) ⟹
		 ((proj_uN_0 x) < (length (fun_tagaddr z))) ⟹
		 ((exninst_TAG ((fun_exninst z) ! a)) = ((fun_tagaddr z) ! (proj_uN_0 x))) ⟹
		 (val_lst = (exninst_FIELDS ((fun_exninst z) ! a))) ⟹
		 Step_read_before_throw_ref_handler_next (mk_config z [(instr_sc10 (HANDLER_underscore v_n ([(CATCH_REF x l)] @ catch'_lst) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]))])"
	| throw_ref_handler_catch_0 :
		"list_all (λ (iter :: exninst). (wf_exninst iter)) (fun_exninst z) ⟹
		 (a < (length (fun_exninst z))) ⟹
		 ((proj_uN_0 x) < (length (fun_tagaddr z))) ⟹
		 ((exninst_TAG ((fun_exninst z) ! a)) = ((fun_tagaddr z) ! (proj_uN_0 x))) ⟹
		 (val_lst = (exninst_FIELDS ((fun_exninst z) ! a))) ⟹
		 Step_read_before_throw_ref_handler_next (mk_config z [(instr_sc10 (HANDLER_underscore v_n ([(CATCH x l)] @ catch'_lst) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:364.1-367.14 *)
inductive Step_read_before_table_fill_zero :: "config ⇒ bool" where
	  table_fill_oob_0 :
		"(wf_tableinst (fun_table z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (tableinst_REFS (fun_table z x)))) ⟹
		 Step_read_before_table_fill_zero (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN v_n)))), (instr_sc2 (TABLE_FILL x))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:381.1-384.14 *)
inductive Step_read_before_table_copy_zero :: "config ⇒ bool" where
	  table_copy_oob_0 :
		"(wf_tableinst (fun_table z x_1)) ⟹
		 (wf_tableinst (fun_table z x_2)) ⟹
		 ((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) > (length (tableinst_REFS (fun_table z x_1)))) ∨ (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) > (length (tableinst_REFS (fun_table z x_2))))) ⟹
		 Step_read_before_table_copy_zero (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc2 (TABLE_COPY x_1 x_2))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:386.1-391.19 *)
inductive Step_read_before_table_copy_le :: "config ⇒ bool" where
	  table_copy_zero_0 :
		"(~(Step_read_before_table_copy_zero (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc2 (TABLE_COPY x y))]))) ⟹
		 (v_n = 0) ⟹
		 Step_read_before_table_copy_le (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc2 (TABLE_COPY x y))])"
	| table_copy_oob_1 :
		"(wf_tableinst (fun_table z x_1)) ⟹
		 (wf_tableinst (fun_table z x_2)) ⟹
		 ((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) > (length (tableinst_REFS (fun_table z x_1)))) ∨ (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) > (length (tableinst_REFS (fun_table z x_2))))) ⟹
		 Step_read_before_table_copy_le (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc2 (TABLE_COPY x_1 x_2))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:405.1-408.14 *)
inductive Step_read_before_table_init_zero :: "config ⇒ bool" where
	  table_init_oob_0 :
		"(wf_tableinst (fun_table z x)) ⟹
		 (wf_eleminst (fun_elem z y)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (tableinst_REFS (fun_table z x)))) ∨ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (eleminst_REFS (fun_elem z y))))) ⟹
		 Step_read_before_table_init_zero (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc2 (TABLE_INIT x y))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:566.1-569.14 *)
inductive Step_read_before_memory_fill_zero :: "config ⇒ bool" where
	  memory_fill_oob_0 :
		"(wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (BYTES (fun_mem z x)))) ⟹
		 Step_read_before_memory_fill_zero (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN v_n)))), (instr_sc3 (MEMORY_FILL x))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:583.1-586.14 *)
inductive Step_read_before_memory_copy_zero :: "config ⇒ bool" where
	  memory_copy_oob_0 :
		"(wf_meminst (fun_mem z x_1)) ⟹
		 (wf_meminst (fun_mem z x_2)) ⟹
		 ((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) > (length (BYTES (fun_mem z x_1)))) ∨ (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) > (length (BYTES (fun_mem z x_2))))) ⟹
		 Step_read_before_memory_copy_zero (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc3 (MEMORY_COPY x_1 x_2))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:588.1-593.19 *)
inductive Step_read_before_memory_copy_le :: "config ⇒ bool" where
	  memory_copy_zero_0 :
		"(~(Step_read_before_memory_copy_zero (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc3 (MEMORY_COPY x_1 x_2))]))) ⟹
		 (v_n = 0) ⟹
		 Step_read_before_memory_copy_le (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc3 (MEMORY_COPY x_1 x_2))])"
	| memory_copy_oob_1 :
		"(wf_meminst (fun_mem z x_1)) ⟹
		 (wf_meminst (fun_mem z x_2)) ⟹
		 ((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) > (length (BYTES (fun_mem z x_1)))) ∨ (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) > (length (BYTES (fun_mem z x_2))))) ⟹
		 Step_read_before_memory_copy_le (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc3 (MEMORY_COPY x_1 x_2))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:607.1-610.14 *)
inductive Step_read_before_memory_init_zero :: "config ⇒ bool" where
	  memory_init_oob_0 :
		"(wf_meminst (fun_mem z x)) ⟹
		 (wf_datainst (fun_data z y)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (BYTES (fun_mem z x)))) ∨ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (datainst_BYTES (fun_data z y))))) ⟹
		 Step_read_before_memory_init_zero (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc3 (MEMORY_INIT x y))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:673.1-675.15 *)
inductive Step_read_before_ref_test_false :: "config ⇒ bool" where
	  ref_test_true_0 :
		"(fun_inst_reftype (MODULE f) rt var_0) ⟹
		 (wf_reftype rt') ⟹
		 (wf_reftype var_0) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (Ref_ok s v_ref rt') ⟹
		 (Reftype_sub ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈ rt' var_0) ⟹
		 Step_read_before_ref_test_false (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc4 (REF_TEST rt))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:684.1-686.15 *)
inductive Step_read_before_ref_cast_fail :: "config ⇒ bool" where
	  ref_cast_succeed_0 :
		"(fun_inst_reftype (MODULE f) rt var_0) ⟹
		 (wf_reftype rt') ⟹
		 (wf_reftype var_0) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (Ref_ok s v_ref rt') ⟹
		 (Reftype_sub ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈ rt' var_0) ⟹
		 Step_read_before_ref_cast_fail (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc4 (REF_CAST rt))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:812.1-815.14 *)
inductive Step_read_before_array_fill_zero :: "config ⇒ bool" where
	  array_fill_oob_0 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (a < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a)))) ⟹
		 Step_read_before_array_fill_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_FILL x))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:817.1-821.15 *)
inductive Step_read_before_array_fill_succ :: "config ⇒ bool" where
	  array_fill_zero_0 :
		"(~(Step_read_before_array_fill_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_FILL x))]))) ⟹
		 (v_n = 0) ⟹
		 Step_read_before_array_fill_succ (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_FILL x))])"
	| array_fill_oob_1 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (a < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a)))) ⟹
		 Step_read_before_array_fill_succ (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_FILL x))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:839.1-843.14 *)
inductive Step_read_before_array_copy_zero :: "config ⇒ bool" where
	  array_copy_oob2_0 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 (a_2 < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a_2)))) ⟹
		 Step_read_before_array_copy_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))])"
	| array_copy_oob1_0 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i_1) ≠ None) ⟹
		 (a_1 < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a_1)))) ⟹
		 Step_read_before_array_copy_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:845.1-855.24 *)
inductive Step_read_before_array_copy_le :: "config ⇒ bool" where
	  array_copy_zero_0 :
		"(~(Step_read_before_array_copy_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))]))) ⟹
		 (v_n = 0) ⟹
		 Step_read_before_array_copy_le (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))])"
	| array_copy_oob2_1 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 (a_2 < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a_2)))) ⟹
		 Step_read_before_array_copy_le (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))])"
	| array_copy_oob1_1 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i_1) ≠ None) ⟹
		 (a_1 < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a_1)))) ⟹
		 Step_read_before_array_copy_le (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:857.1-866.24 *)
inductive Step_read_before_array_copy_gt :: "config ⇒ bool" where
	  array_copy_le_0 :
		"(wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt_2))) ⟹
		 (~(Step_read_before_array_copy_le (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))]))) ⟹
		 (Expand (fun_type z x_2) (comptype_ARRAY (mk_fieldtype mut_opt zt_2))) ⟹
		 ((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 ((fun_sx zt_2) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i_1)))) ≤ (proj_uN_0 (the ((proj_num__0 i_2))))) ∧ (sx_opt = (the ((fun_sx zt_2))))) ⟹
		 Step_read_before_array_copy_gt (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))])"
	| array_copy_zero_1 :
		"(~(Step_read_before_array_copy_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))]))) ⟹
		 (v_n = 0) ⟹
		 Step_read_before_array_copy_gt (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))])"
	| array_copy_oob2_2 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 (a_2 < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a_2)))) ⟹
		 Step_read_before_array_copy_gt (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))])"
	| array_copy_oob1_2 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i_1) ≠ None) ⟹
		 (a_1 < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a_1)))) ⟹
		 Step_read_before_array_copy_gt (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:882.1-886.14 *)
inductive Step_read_before_array_init_elem_zero :: "config ⇒ bool" where
	  array_init_elem_oob2_0 :
		"(wf_eleminst (fun_elem z y)) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (eleminst_REFS (fun_elem z y)))) ⟹
		 Step_read_before_array_init_elem_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_ELEM x y))])"
	| array_init_elem_oob1_0 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (a < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a)))) ⟹
		 Step_read_before_array_init_elem_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_ELEM x y))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:888.1-894.34 *)
inductive Step_read_before_array_init_elem_succ :: "config ⇒ bool" where
	  array_init_elem_zero_0 :
		"(~(Step_read_before_array_init_elem_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_ELEM x y))]))) ⟹
		 (v_n = 0) ⟹
		 Step_read_before_array_init_elem_succ (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_ELEM x y))])"
	| array_init_elem_oob2_1 :
		"(wf_eleminst (fun_elem z y)) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (eleminst_REFS (fun_elem z y)))) ⟹
		 Step_read_before_array_init_elem_succ (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_ELEM x y))])"
	| array_init_elem_oob1_1 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (a < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a)))) ⟹
		 Step_read_before_array_init_elem_succ (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_ELEM x y))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:911.1-915.14 *)
inductive Step_read_before_array_init_data_zero :: "config ⇒ bool" where
	  array_init_data_oob2_0 :
		"(wf_datainst (fun_data z y)) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 (Expand (fun_type z x) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((zsize zt) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 j)))) + ((((v_n * (the ((zsize zt)))) :: nat) div (8 :: nat)) :: nat)) > (length (datainst_BYTES (fun_data z y)))) ⟹
		 Step_read_before_array_init_data_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_DATA x y))])"
	| array_init_data_oob1_0 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (a < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a)))) ⟹
		 Step_read_before_array_init_data_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_DATA x y))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:918.1-925.62 *)
inductive Step_read_before_array_init_data_num :: "config ⇒ bool" where
	  array_init_data_zero_0 :
		"(~(Step_read_before_array_init_data_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_DATA x y))]))) ⟹
		 (v_n = 0) ⟹
		 Step_read_before_array_init_data_num (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_DATA x y))])"
	| array_init_data_oob2_1 :
		"(wf_datainst (fun_data z y)) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 (Expand (fun_type z x) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((zsize zt) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 j)))) + ((((v_n * (the ((zsize zt)))) :: nat) div (8 :: nat)) :: nat)) > (length (datainst_BYTES (fun_data z y)))) ⟹
		 Step_read_before_array_init_data_num (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_DATA x y))])"
	| array_init_data_oob1_1 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (a < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a)))) ⟹
		 Step_read_before_array_init_data_num (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_DATA x y))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:7.1-7.88 *)
inductive Step_read :: "config ⇒ (instr list) ⇒ bool" where
	  Step_read__block :
		"(fun_blocktype_underscore z bt var_0) ⟹
		 (wf_instrtype var_0) ⟹
		 (wf_instrtype (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (var_0 = (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (v_m = (length val_lst)) ⟹
		 (v_m = (length t_1_lst)) ⟹
		 (v_n = (length t_2_lst)) ⟹
		 Step_read (mk_config z ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc9 (BLOCK bt instr_lst))])) [(instr_sc10 (LABEL_underscore v_n [] ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ instr_lst)))]"
	| Step_read__loop :
		"(fun_blocktype_underscore z bt var_0) ⟹
		 (wf_instrtype var_0) ⟹
		 (wf_instrtype (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (var_0 = (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (v_m = (length val_lst)) ⟹
		 (v_m = (length t_1_lst)) ⟹
		 (v_n = (length t_2_lst)) ⟹
		 Step_read (mk_config z ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc9 (LOOP bt instr_lst))])) [(instr_sc10 (LABEL_underscore v_m [(instr_sc9 (LOOP bt instr_lst))] ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ instr_lst)))]"
	| br_on_cast_succeed :
		"(fun_inst_reftype (MODULE f) rt_2 var_0) ⟹
		 (wf_reftype rt) ⟹
		 (wf_reftype var_0) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (Ref_ok s v_ref rt) ⟹
		 (Reftype_sub ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈ rt var_0) ⟹
		 Step_read (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc0 (BR_ON_CAST l rt_1 rt_2))]) [(instr_ref v_ref), (instr_sc0 (BR l))]"
	| Step_read__br_on_cast_fail :
		"(~(Step_read_before_br_on_cast_fail (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc0 (BR_ON_CAST l rt_1 rt_2))]))) ⟹
		 Step_read (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc0 (BR_ON_CAST l rt_1 rt_2))]) [(instr_ref v_ref)]"
	| br_on_cast_fail_succeed :
		"(fun_inst_reftype (MODULE f) rt_2 var_0) ⟹
		 (wf_reftype rt) ⟹
		 (wf_reftype var_0) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (Ref_ok s v_ref rt) ⟹
		 (Reftype_sub ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈ rt var_0) ⟹
		 Step_read (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc0 (BR_ON_CAST_FAIL l rt_1 rt_2))]) [(instr_ref v_ref)]"
	| br_on_cast_fail_fail :
		"(~(Step_read_before_br_on_cast_fail_fail (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc0 (BR_ON_CAST_FAIL l rt_1 rt_2))]))) ⟹
		 Step_read (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc0 (BR_ON_CAST_FAIL l rt_1 rt_2))]) [(instr_ref v_ref), (instr_sc0 (BR l))]"
	| Step_read__call :
		"(a < (length (fun_funcinst z))) ⟹
		 (wf_moduleinst (fun_moduleinst z)) ⟹
		 ((proj_uN_0 x) < (length (moduleinst_FUNCS (fun_moduleinst z)))) ⟹
		 (((moduleinst_FUNCS (fun_moduleinst z)) ! (proj_uN_0 x)) = a) ⟹
		 Step_read (mk_config z [(instr_sc1 (CALL x))]) [(instr_sc9 (instr_st9_REF_FUNC_ADDR a)), (instr_sc1 (CALL_REF (typeuse_deftype (funcinst_TYPE ((fun_funcinst z) ! a)))))]"
	| call_ref_null :
		"Step_read (mk_config z [(instr_sc4 (instr_st4_REF_NULL ht)), (instr_sc1 (CALL_REF yy))]) [(instr_sc9 TRAP)]"
	| call_ref_func :
		"list_all (λ (iter :: funcinst). (wf_funcinst iter)) (fun_funcinst z) ⟹
		 (wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (wf_funccode (funccode_FUNC x (map (λ (t :: valtype). (LOCAL t)) t_lst) instr_lst)) ⟹
		 list_all (λ (t :: valtype). ((default_underscore t) ≠ None)) t_lst ⟹
		 (wf_frame ⦇ frame_LOCALS = ((map (λ (v_val :: val). (Some v_val)) val_lst) @ (map (λ (t :: valtype). (the ((default_underscore t)))) t_lst)), MODULE = (funcinst_MODULE fi) ⦈) ⟹
		 (a < (length (fun_funcinst z))) ⟹
		 (((fun_funcinst z) ! a) = fi) ⟹
		 (Expand (funcinst_TYPE fi) (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 ((CODE fi) = (funccode_FUNC x (map (λ (t :: valtype). (LOCAL t)) t_lst) instr_lst)) ⟹
		 (f = ⦇ frame_LOCALS = ((map (λ (v_val :: val). (Some v_val)) val_lst) @ (map (λ (t :: valtype). (the ((default_underscore t)))) t_lst)), MODULE = (funcinst_MODULE fi) ⦈) ⟹
		 (v_n = (length val_lst)) ⟹
		 (v_n = (length t_1_lst)) ⟹
		 (v_m = (length t_2_lst)) ⟹
		 Step_read (mk_config z ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc9 (instr_st9_REF_FUNC_ADDR a)), (instr_sc1 (CALL_REF yy))])) [(instr_sc10 (FRAME_underscore v_m f [(instr_sc10 (LABEL_underscore v_m [] instr_lst))]))]"
	| Step_read__return_call :
		"(a < (length (fun_funcinst z))) ⟹
		 (wf_moduleinst (fun_moduleinst z)) ⟹
		 ((proj_uN_0 x) < (length (moduleinst_FUNCS (fun_moduleinst z)))) ⟹
		 (((moduleinst_FUNCS (fun_moduleinst z)) ! (proj_uN_0 x)) = a) ⟹
		 Step_read (mk_config z [(instr_sc1 (RETURN_CALL x))]) [(instr_sc9 (instr_st9_REF_FUNC_ADDR a)), (instr_sc1 (RETURN_CALL_REF (typeuse_deftype (funcinst_TYPE ((fun_funcinst z) ! a)))))]"
	| return_call_ref_label :
		"Step_read (mk_config z [(instr_sc10 (LABEL_underscore k instr'_lst (((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc1 (RETURN_CALL_REF yy))]) @ instr_lst)))]) ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc1 (RETURN_CALL_REF yy))])"
	| return_call_ref_handler :
		"Step_read (mk_config z [(instr_sc10 (HANDLER_underscore k catch_lst (((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc1 (RETURN_CALL_REF yy))]) @ instr_lst)))]) ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc1 (RETURN_CALL_REF yy))])"
	| return_call_ref_frame_null :
		"Step_read (mk_config z [(instr_sc10 (FRAME_underscore k f ((((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc4 (instr_st4_REF_NULL ht))]) @ [(instr_sc1 (RETURN_CALL_REF yy))]) @ instr_lst)))]) [(instr_sc9 TRAP)]"
	| return_call_ref_frame_addr :
		"list_all (λ (iter :: funcinst). (wf_funcinst iter)) (fun_funcinst z) ⟹
		 (wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (a < (length (fun_funcinst z))) ⟹
		 (Expand (funcinst_TYPE ((fun_funcinst z) ! a)) (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (v_n = (length val_lst)) ⟹
		 (v_n = (length t_1_lst)) ⟹
		 (v_m = (length t_2_lst)) ⟹
		 Step_read (mk_config z [(instr_sc10 (FRAME_underscore k f (((((map (λ (val' :: val). (instr_val val')) val'_lst) @ (map (λ (v_val :: val). (instr_val v_val)) val_lst)) @ [(instr_sc9 (instr_st9_REF_FUNC_ADDR a))]) @ [(instr_sc1 (RETURN_CALL_REF yy))]) @ instr_lst)))]) ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc9 (instr_st9_REF_FUNC_ADDR a)), (instr_sc1 (CALL_REF yy))])"
	| throw_ref_null :
		"Step_read (mk_config z [(instr_sc4 (instr_st4_REF_NULL ht)), (instr_sc1 THROW_REF)]) [(instr_sc9 TRAP)]"
	| throw_ref_instrs :
		"((val_lst ≠ []) ∨ (instr_lst ≠ [])) ⟹
		 Step_read (mk_config z ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ ([(instr_sc9 (instr_st9_REF_EXN_ADDR a))] @ ([(instr_sc1 THROW_REF)] @ instr_lst)))) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]"
	| throw_ref_label :
		"Step_read (mk_config z [(instr_sc10 (LABEL_underscore v_n instr'_lst [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]))]) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]"
	| throw_ref_frame :
		"Step_read (mk_config z [(instr_sc10 (FRAME_underscore v_n f [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]))]) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]"
	| throw_ref_handler_empty :
		"Step_read (mk_config z [(instr_sc10 (HANDLER_underscore v_n [] [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]))]) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]"
	| throw_ref_handler_catch :
		"list_all (λ (iter :: exninst). (wf_exninst iter)) (fun_exninst z) ⟹
		 (a < (length (fun_exninst z))) ⟹
		 ((proj_uN_0 x) < (length (fun_tagaddr z))) ⟹
		 ((exninst_TAG ((fun_exninst z) ! a)) = ((fun_tagaddr z) ! (proj_uN_0 x))) ⟹
		 (val_lst = (exninst_FIELDS ((fun_exninst z) ! a))) ⟹
		 Step_read (mk_config z [(instr_sc10 (HANDLER_underscore v_n ([(CATCH x l)] @ catch'_lst) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]))]) ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc0 (BR l))])"
	| throw_ref_handler_catch_ref :
		"list_all (λ (iter :: exninst). (wf_exninst iter)) (fun_exninst z) ⟹
		 (a < (length (fun_exninst z))) ⟹
		 ((proj_uN_0 x) < (length (fun_tagaddr z))) ⟹
		 ((exninst_TAG ((fun_exninst z) ! a)) = ((fun_tagaddr z) ! (proj_uN_0 x))) ⟹
		 (val_lst = (exninst_FIELDS ((fun_exninst z) ! a))) ⟹
		 Step_read (mk_config z [(instr_sc10 (HANDLER_underscore v_n ([(CATCH_REF x l)] @ catch'_lst) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]))]) ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc0 (BR l))])"
	| throw_ref_handler_catch_all :
		"Step_read (mk_config z [(instr_sc10 (HANDLER_underscore v_n ([(CATCH_ALL l)] @ catch'_lst) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]))]) [(instr_sc0 (BR l))]"
	| throw_ref_handler_catch_all_ref :
		"Step_read (mk_config z [(instr_sc10 (HANDLER_underscore v_n ([(CATCH_ALL_REF l)] @ catch'_lst) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]))]) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc0 (BR l))]"
	| throw_ref_handler_next :
		"(~(Step_read_before_throw_ref_handler_next (mk_config z [(instr_sc10 (HANDLER_underscore v_n ([v_catch] @ catch'_lst) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]))]))) ⟹
		 Step_read (mk_config z [(instr_sc10 (HANDLER_underscore v_n ([v_catch] @ catch'_lst) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]))]) [(instr_sc10 (HANDLER_underscore v_n catch'_lst [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)]))]"
	| Step_read__try_table :
		"(fun_blocktype_underscore z bt var_0) ⟹
		 (wf_instrtype var_0) ⟹
		 (wf_instrtype (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (var_0 = (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (v_m = (length val_lst)) ⟹
		 (v_m = (length t_1_lst)) ⟹
		 (v_n = (length t_2_lst)) ⟹
		 Step_read (mk_config z ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc10 (TRY_TABLE bt (mk_list catch_lst) instr_lst))])) [(instr_sc10 (HANDLER_underscore v_n catch_lst [(instr_sc10 (LABEL_underscore v_n [] ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ instr_lst)))]))]"
	| Step_read__local_get :
		"list_all (λ (iter :: val). (wf_val iter)) (option_to_list (fun_local z x)) ⟹
		 ((fun_local z x) = (Some v_val)) ⟹
		 Step_read (mk_config z [(instr_sc1 (LOCAL_GET x))]) [(instr_val v_val)]"
	| Step_read__global_get :
		"(wf_globalinst (fun_global z x)) ⟹
		 ((VALUE (fun_global z x)) = v_val) ⟹
		 Step_read (mk_config z [(instr_sc2 (GLOBAL_GET x))]) [(instr_val v_val)]"
	| table_get_oob :
		"(wf_tableinst (fun_table z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i)))) ≥ (length (tableinst_REFS (fun_table z x)))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc2 (TABLE_GET x))]) [(instr_sc9 TRAP)]"
	| table_get_val :
		"((proj_uN_0 (the ((proj_num__0 i)))) < (length (tableinst_REFS (fun_table z x)))) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (wf_tableinst (fun_table z x)) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc2 (TABLE_GET x))]) [(instr_ref ((tableinst_REFS (fun_table z x)) ! (proj_uN_0 (the ((proj_num__0 i))))))]"
	| Step_read__table_size :
		"(wf_tableinst (fun_table z x)) ⟹
		 (wf_tabletype (mk_tabletype at lim rt)) ⟹
		 ((length (tableinst_REFS (fun_table z x))) = v_n) ⟹
		 ((tableinst_TYPE (fun_table z x)) = (mk_tabletype at lim rt)) ⟹
		 Step_read (mk_config z [(instr_sc2 (TABLE_SIZE x))]) [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN v_n))))]"
	| table_fill_oob :
		"(wf_tableinst (fun_table z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (tableinst_REFS (fun_table z x)))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN v_n)))), (instr_sc2 (TABLE_FILL x))]) [(instr_sc9 TRAP)]"
	| table_fill_zero :
		"((proj_num__0 i) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (tableinst_REFS (fun_table z x)))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN v_n)))), (instr_sc2 (TABLE_FILL x))]) []"
	| table_fill_succ :
		"((proj_num__0 i) ≠ None) ⟹
		 (v_n ≠ 0) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (tableinst_REFS (fun_table z x)))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN v_n)))), (instr_sc2 (TABLE_FILL x))]) [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_val v_val), (instr_sc2 (TABLE_SET x)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (instr_val v_val), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (instr_sc2 (TABLE_FILL x))]"
	| table_copy_oob :
		"(wf_tableinst (fun_table z x_1)) ⟹
		 (wf_tableinst (fun_table z x_2)) ⟹
		 ((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) > (length (tableinst_REFS (fun_table z x_1)))) ∨ (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) > (length (tableinst_REFS (fun_table z x_2))))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc2 (TABLE_COPY x_1 x_2))]) [(instr_sc9 TRAP)]"
	| table_copy_zero :
		"((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) ≤ (length (tableinst_REFS (fun_table z x_1)))) ∧ (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) ≤ (length (tableinst_REFS (fun_table z x_2))))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc2 (TABLE_COPY x y))]) []"
	| table_copy_le :
		"((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 (v_n ≠ 0) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) ≤ (length (tableinst_REFS (fun_table z x_1)))) ∧ (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) ≤ (length (tableinst_REFS (fun_table z x_2))))) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i_1)))) ≤ (proj_uN_0 (the ((proj_num__0 i_2))))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc2 (TABLE_COPY x y))]) [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc2 (TABLE_GET y)), (instr_sc2 (TABLE_SET x)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) (mk_num__0 at_1 (mk_uN ((proj_uN_0 (the ((proj_num__0 i_1)))) + 1))))), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) (mk_num__0 at_2 (mk_uN ((proj_uN_0 (the ((proj_num__0 i_2)))) + 1))))), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (instr_sc2 (TABLE_COPY x y))]"
	| table_copy_gt :
		"((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i_1)))) > (proj_uN_0 (the ((proj_num__0 i_2))))) ⟹
		 (v_n ≠ 0) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) ≤ (length (tableinst_REFS (fun_table z x_1)))) ∧ (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) ≤ (length (tableinst_REFS (fun_table z x_2))))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc2 (TABLE_COPY x y))]) [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) (mk_num__0 at_1 (mk_uN (((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) :: nat) - (1 :: nat)) :: nat))))), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) (mk_num__0 at_2 (mk_uN (((((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) :: nat) - (1 :: nat)) :: nat))))), (instr_sc2 (TABLE_GET y)), (instr_sc2 (TABLE_SET x)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (instr_sc2 (TABLE_COPY x y))]"
	| table_init_oob :
		"(wf_tableinst (fun_table z x)) ⟹
		 (wf_eleminst (fun_elem z y)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (tableinst_REFS (fun_table z x)))) ∨ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (eleminst_REFS (fun_elem z y))))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc2 (TABLE_INIT x y))]) [(instr_sc9 TRAP)]"
	| table_init_zero :
		"((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (tableinst_REFS (fun_table z x)))) ∧ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) ≤ (length (eleminst_REFS (fun_elem z y))))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc2 (TABLE_INIT x y))]) []"
	| table_init_succ :
		"((proj_uN_0 (the ((proj_num__0 j)))) < (length (eleminst_REFS (fun_elem z y)))) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (v_n ≠ 0) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (tableinst_REFS (fun_table z x)))) ∧ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) ≤ (length (eleminst_REFS (fun_elem z y))))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc2 (TABLE_INIT x y))]) [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_ref ((eleminst_REFS (fun_elem z y)) ! (proj_uN_0 (the ((proj_num__0 j)))))), (instr_sc2 (TABLE_SET x)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 j)))) + 1))))), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (instr_sc2 (TABLE_INIT x y))]"
	| load_num_oob :
		"(wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((size nt) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z x)))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc3 (LOAD nt None x ao))]) [(instr_sc9 TRAP)]"
	| load_num_val :
		"list_all (λ (iter :: byte). (wf_byte iter)) (nbytes_underscore nt c) ⟹
		 (wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((nbytes_underscore nt c) = (list_slice (BYTES (fun_mem z x)) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((size nt) :: nat) div (8 :: nat)) :: nat))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc3 (LOAD nt None x ao))]) [(instr_sc6 (instr_st6_CONST nt c))]"
	| load_pack_oob :
		"(wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_n :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z x)))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc3 (LOAD (numtype_addrtype v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) x ao))]) [(instr_sc9 TRAP)]"
	| load_pack_val :
		"list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_n c) ⟹
		 (wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((ibytes_underscore v_n c) = (list_slice (BYTES (fun_mem z x)) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_n :: nat) div (8 :: nat)) :: nat))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc3 (LOAD (numtype_addrtype v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) x ao))]) [(instr_sc6 (instr_st6_CONST (numtype_addrtype v_Inn) (mk_num__0 v_Inn (extend__underscore v_n (size (numtype_addrtype v_Inn)) v_sx c))))]"
	| vload_oob :
		"(wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((vsize V128) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z x)))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc3 (VLOAD V128 None x ao))]) [(instr_sc9 TRAP)]"
	| Step_read__vload_val :
		"list_all (λ (iter :: byte). (wf_byte iter)) (vbytes_underscore V128 c) ⟹
		 (wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((vbytes_underscore V128 c) = (list_slice (BYTES (fun_mem z x)) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((vsize V128) :: nat) div (8 :: nat)) :: nat))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc3 (VLOAD V128 None x ao))]) [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| vload_pack_oob :
		"(wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((v_M * v_K) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z x)))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc3 (VLOAD V128 (Some (SHAPEX_underscore (mk_sz v_M) v_K v_sx)) x ao))]) [(instr_sc9 TRAP)]"
	| vload_pack_val :
		"list_alli (λ k (j :: iN). list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_M j)) j_lst ⟹
		 (wf_meminst (fun_mem z x)) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_K)) (map (λ (j :: iN). (mk_lane__2 v_Jnn (extend__underscore v_M (jsizenn v_Jnn) v_sx j))) j_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_K))) ⟹
		 list_all (λ (j :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_K))) (mk_lane__2 v_Jnn (extend__underscore v_M (jsizenn v_Jnn) v_sx j)))) j_lst ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 list_alli (λ k (j :: iN). ((ibytes_underscore v_M j) = (list_slice (BYTES (fun_mem z x)) (((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((k * v_M) :: nat) div (8 :: nat)) :: nat)) (((v_M :: nat) div (8 :: nat)) :: nat)))) j_lst ⟹
		 ((c = (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_K)) (map (λ (j :: iN). (mk_lane__2 v_Jnn (extend__underscore v_M (jsizenn v_Jnn) v_sx j))) j_lst))) ∧ ((jsizenn v_Jnn) = (v_M * 2))) ⟹
		 (v_K = (length j_lst)) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc3 (VLOAD V128 (Some (SHAPEX_underscore (mk_sz v_M) v_K v_sx)) x ao))]) [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| vload_splat_oob :
		"(wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_N :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z x)))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc3 (VLOAD V128 (Some (SPLAT (mk_sz v_N))) x ao))]) [(instr_sc9 TRAP)]"
	| vload_splat_val :
		"list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_N j) ⟹
		 (wf_meminst (fun_mem z x)) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (repeat v_M (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 j)))))) ⟹
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) ⟹
		 (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 j)))) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((ibytes_underscore v_N j) = (list_slice (BYTES (fun_mem z x)) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_N :: nat) div (8 :: nat)) :: nat))) ⟹
		 (v_N = (jsize v_Jnn)) ⟹
		 ((v_M :: nat) = ((128 :: nat) div (v_N :: nat))) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (repeat v_M (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 j)))))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc3 (VLOAD V128 (Some (SPLAT (mk_sz v_N))) x ao))]) [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| vload_zero_oob :
		"(wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_N :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z x)))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc3 (VLOAD V128 (Some (vloadop__ZERO (mk_sz v_N))) x ao))]) [(instr_sc9 TRAP)]"
	| vload_zero_val :
		"(wf_uN v_N j) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_N j) ⟹
		 (wf_meminst (fun_mem z x)) ⟹
		 (wf_uN 128 (extend__underscore v_N (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) U j)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((ibytes_underscore v_N j) = (list_slice (BYTES (fun_mem z x)) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_N :: nat) div (8 :: nat)) :: nat))) ⟹
		 (c = (extend__underscore v_N (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) U j)) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc3 (VLOAD V128 (Some (vloadop__ZERO (mk_sz v_N))) x ao))]) [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| vload_lane_oob :
		"(wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_N :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z x)))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc3 (VLOAD_LANE V128 (mk_sz v_N) x ao j))]) [(instr_sc9 TRAP)]"
	| vload_lane_val :
		"list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_N k) ⟹
		 (wf_meminst (fun_mem z x)) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (list_update_func (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c_1) (proj_uN_0 j) (λ (underscore_underscore :: lane_underscore). (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 k))))))) ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) iter)) (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c_1) ⟹
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) ⟹
		 (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 k)))) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((ibytes_underscore v_N k) = (list_slice (BYTES (fun_mem z x)) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_N :: nat) div (8 :: nat)) :: nat))) ⟹
		 (v_N = (jsize v_Jnn)) ⟹
		 ((v_M :: nat) = (((vsize V128) :: nat) div (v_N :: nat))) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (list_update_func (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c_1) (proj_uN_0 j) (λ (underscore_underscore :: lane_underscore). (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 k))))))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc7 (instr_st7_VCONST V128 c_1)), (instr_sc3 (VLOAD_LANE V128 (mk_sz v_N) x ao j))]) [(instr_sc7 (instr_st7_VCONST V128 c))]"
	| Step_read__memory_size :
		"(wf_meminst (fun_mem z x)) ⟹
		 (wf_memtype (PAGE at lim)) ⟹
		 ((v_n * (64 * (Ki ))) = (length (BYTES (fun_mem z x)))) ⟹
		 ((meminst_TYPE (fun_mem z x)) = (PAGE at lim)) ⟹
		 Step_read (mk_config z [(instr_sc3 (MEMORY_SIZE x))]) [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN v_n))))]"
	| memory_fill_oob :
		"(wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (BYTES (fun_mem z x)))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN v_n)))), (instr_sc3 (MEMORY_FILL x))]) [(instr_sc9 TRAP)]"
	| memory_fill_zero :
		"((proj_num__0 i) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (BYTES (fun_mem z x)))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN v_n)))), (instr_sc3 (MEMORY_FILL x))]) []"
	| memory_fill_succ :
		"((proj_num__0 i) ≠ None) ⟹
		 (v_n ≠ 0) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (BYTES (fun_mem z x)))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN v_n)))), (instr_sc3 (MEMORY_FILL x))]) [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_val v_val), (instr_sc3 (STORE numtype_I32 (Some (mk_storeop__0 I32 (mk_storeop_Inn (mk_sz 8)))) x (memarg0 ))), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (instr_val v_val), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (instr_sc3 (MEMORY_FILL x))]"
	| memory_copy_oob :
		"(wf_meminst (fun_mem z x_1)) ⟹
		 (wf_meminst (fun_mem z x_2)) ⟹
		 ((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) > (length (BYTES (fun_mem z x_1)))) ∨ (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) > (length (BYTES (fun_mem z x_2))))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc3 (MEMORY_COPY x_1 x_2))]) [(instr_sc9 TRAP)]"
	| memory_copy_zero :
		"((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) ≤ (length (BYTES (fun_mem z x_1)))) ∧ (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) ≤ (length (BYTES (fun_mem z x_2))))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc3 (MEMORY_COPY x_1 x_2))]) []"
	| memory_copy_le :
		"((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 (v_n ≠ 0) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) ≤ (length (BYTES (fun_mem z x_1)))) ∧ (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) ≤ (length (BYTES (fun_mem z x_2))))) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i_1)))) ≤ (proj_uN_0 (the ((proj_num__0 i_2))))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc3 (MEMORY_COPY x_1 x_2))]) [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc3 (LOAD numtype_I32 (Some (mk_loadop__0 I32 (mk_loadop_Inn (mk_sz 8) U))) x_2 (memarg0 ))), (instr_sc3 (STORE numtype_I32 (Some (mk_storeop__0 I32 (mk_storeop_Inn (mk_sz 8)))) x_1 (memarg0 ))), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) (mk_num__0 at_1 (mk_uN ((proj_uN_0 (the ((proj_num__0 i_1)))) + 1))))), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) (mk_num__0 at_2 (mk_uN ((proj_uN_0 (the ((proj_num__0 i_2)))) + 1))))), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (instr_sc3 (MEMORY_COPY x_1 x_2))]"
	| memory_copy_gt :
		"((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i_1)))) > (proj_uN_0 (the ((proj_num__0 i_2))))) ⟹
		 (v_n ≠ 0) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) ≤ (length (BYTES (fun_mem z x_1)))) ∧ (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) ≤ (length (BYTES (fun_mem z x_2))))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN v_n)))), (instr_sc3 (MEMORY_COPY x_1 x_2))]) [(instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) (mk_num__0 at_1 (mk_uN (((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) :: nat) - (1 :: nat)) :: nat))))), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) (mk_num__0 at_2 (mk_uN (((((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) :: nat) - (1 :: nat)) :: nat))))), (instr_sc3 (LOAD numtype_I32 (Some (mk_loadop__0 I32 (mk_loadop_Inn (mk_sz 8) U))) x_2 (memarg0 ))), (instr_sc3 (STORE numtype_I32 (Some (mk_storeop__0 I32 (mk_storeop_Inn (mk_sz 8)))) x_1 (memarg0 ))), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_1) i_1)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at_2) i_2)), (instr_sc6 (instr_st6_CONST (numtype_addrtype at') (mk_num__0 at' (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (instr_sc3 (MEMORY_COPY x_1 x_2))]"
	| memory_init_oob :
		"(wf_meminst (fun_mem z x)) ⟹
		 (wf_datainst (fun_data z y)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (BYTES (fun_mem z x)))) ∨ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (datainst_BYTES (fun_data z y))))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc3 (MEMORY_INIT x y))]) [(instr_sc9 TRAP)]"
	| memory_init_zero :
		"((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (BYTES (fun_mem z x)))) ∧ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) ≤ (length (datainst_BYTES (fun_data z y))))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc3 (MEMORY_INIT x y))]) []"
	| memory_init_succ :
		"((proj_uN_0 (the ((proj_num__0 j)))) < (length (datainst_BYTES (fun_data z y)))) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (v_n ≠ 0) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (BYTES (fun_mem z x)))) ∧ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) ≤ (length (datainst_BYTES (fun_data z y))))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc3 (MEMORY_INIT x y))]) [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN (proj_byte_0 ((datainst_BYTES (fun_data z y)) ! (proj_uN_0 (the ((proj_num__0 j)))))))))), (instr_sc3 (STORE numtype_I32 (Some (mk_storeop__0 I32 (mk_storeop_Inn (mk_sz 8)))) x (memarg0 ))), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 j)))) + 1))))), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (instr_sc3 (MEMORY_INIT x y))]"
	| ref_null_idx :
		"Step_read (mk_config z [(instr_sc4 (instr_st4_REF_NULL (heaptype__IDX x)))]) [(instr_sc4 (instr_st4_REF_NULL (heaptype_deftype (fun_type z x))))]"
	| Step_read__ref_func :
		"((proj_uN_0 x) < (length (moduleinst_FUNCS (fun_moduleinst z)))) ⟹
		 Step_read (mk_config z [(instr_sc4 (REF_FUNC x))]) [(instr_sc9 (instr_st9_REF_FUNC_ADDR ((moduleinst_FUNCS (fun_moduleinst z)) ! (proj_uN_0 x))))]"
	| ref_test_true :
		"(fun_inst_reftype (MODULE f) rt var_0) ⟹
		 (wf_reftype rt') ⟹
		 (wf_reftype var_0) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (Ref_ok s v_ref rt') ⟹
		 (Reftype_sub ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈ rt' var_0) ⟹
		 Step_read (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc4 (REF_TEST rt))]) [(instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN 1))))]"
	| ref_test_false :
		"(~(Step_read_before_ref_test_false (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc4 (REF_TEST rt))]))) ⟹
		 Step_read (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc4 (REF_TEST rt))]) [(instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN 0))))]"
	| ref_cast_succeed :
		"(fun_inst_reftype (MODULE f) rt var_0) ⟹
		 (wf_reftype rt') ⟹
		 (wf_reftype var_0) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈) ⟹
		 (Ref_ok s v_ref rt') ⟹
		 (Reftype_sub ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [], context_RETURN = None, REFS = [] ⦈ rt' var_0) ⟹
		 Step_read (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc4 (REF_CAST rt))]) [(instr_ref v_ref)]"
	| ref_cast_fail :
		"(~(Step_read_before_ref_cast_fail (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc4 (REF_CAST rt))]))) ⟹
		 Step_read (mk_config (mk_state s f) [(instr_ref v_ref), (instr_sc4 (REF_CAST rt))]) [(instr_sc9 TRAP)]"
	| Step_read__struct_new_default :
		"list_all (λ (zt :: storagetype). list_all (λ (iter :: val). (wf_val iter)) (option_to_list (the ((default_underscore (unpack zt)))))) zt_lst ⟹
		 list_all (λ (zt :: storagetype). (wf_valtype (unpack zt))) zt_lst ⟹
		 (wf_comptype (comptype_STRUCT (mk_list (list_zipWith (λ (mut_opt :: (mut option)) (zt :: storagetype). (mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ⟹
		 (Expand (fun_type z x) (comptype_STRUCT (mk_list (list_zipWith (λ (mut_opt :: (mut option)) (zt :: storagetype). (mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ⟹
		 ((length val_lst) = (length zt_lst)) ⟹
		 list_all (λ (zt :: storagetype). ((default_underscore (unpack zt)) ≠ None)) zt_lst ⟹
		 list_all2 (λ (v_val :: val) (zt :: storagetype). ((the ((default_underscore (unpack zt)))) = (Some v_val))) val_lst zt_lst ⟹
		 Step_read (mk_config z [(instr_sc5 (STRUCT_NEW_DEFAULT x))]) ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc4 (STRUCT_NEW x))])"
	| struct_get_null :
		"Step_read (mk_config z [(instr_sc4 (instr_st4_REF_NULL ht)), (instr_sc5 (STRUCT_GET sx_opt x i))]) [(instr_sc9 TRAP)]"
	| struct_get_struct :
		"((unpackfield_underscore (zt_lst ! (proj_uN_0 i)) sx_opt ((FIELDS ((fun_structinst z) ! a)) ! (proj_uN_0 i))) ≠ None) ⟹
		 ((proj_uN_0 i) < (length zt_lst)) ⟹
		 ((proj_uN_0 i) < (length (FIELDS ((fun_structinst z) ! a)))) ⟹
		 (a < (length (fun_structinst z))) ⟹
		 (wf_comptype (comptype_STRUCT (mk_list (list_zipWith (λ (mut_opt :: (mut option)) (zt :: storagetype). (mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ⟹
		 (Expand (fun_type z x) (comptype_STRUCT (mk_list (list_zipWith (λ (mut_opt :: (mut option)) (zt :: storagetype). (mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_STRUCT_ADDR a)), (instr_sc5 (STRUCT_GET sx_opt x i))]) [(instr_val (the ((unpackfield_underscore (zt_lst ! (proj_uN_0 i)) sx_opt ((FIELDS ((fun_structinst z) ! a)) ! (proj_uN_0 i))))))]"
	| Step_read__array_new_default :
		"list_all (λ (iter :: val). (wf_val iter)) (option_to_list (the ((default_underscore (unpack zt))))) ⟹
		 (wf_valtype (unpack zt)) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 (Expand (fun_type z x) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 ((default_underscore (unpack zt)) ≠ None) ⟹
		 ((the ((default_underscore (unpack zt)))) = (Some v_val)) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc5 (ARRAY_NEW_DEFAULT x))]) ((repeat v_n (instr_val v_val)) @ [(instr_sc5 (ARRAY_NEW_FIXED x (mk_uN v_n)))])"
	| array_new_elem_oob :
		"(wf_eleminst (fun_elem z y)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (eleminst_REFS (fun_elem z y)))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc5 (ARRAY_NEW_ELEM x y))]) [(instr_sc9 TRAP)]"
	| array_new_elem_alloc :
		"(wf_eleminst (fun_elem z y)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (ref_lst = (list_slice (eleminst_REFS (fun_elem z y)) (proj_uN_0 (the ((proj_num__0 i)))) v_n)) ⟹
		 (v_n = (length ref_lst)) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc5 (ARRAY_NEW_ELEM x y))]) ((map (λ (v_ref :: ref). (instr_ref v_ref)) ref_lst) @ [(instr_sc5 (ARRAY_NEW_FIXED x (mk_uN v_n)))])"
	| array_new_data_oob :
		"(wf_datainst (fun_data z y)) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 (Expand (fun_type z x) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((zsize zt) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + ((((v_n * (the ((zsize zt)))) :: nat) div (8 :: nat)) :: nat)) > (length (datainst_BYTES (fun_data z y)))) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc5 (ARRAY_NEW_DATA x y))]) [(instr_sc9 TRAP)]"
	| array_new_data_num :
		"((cunpack zt) ≠ None) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (concatn_underscore  (map (λ (c :: lit_underscore). (zbytes_underscore zt c)) c_lst) ((((the ((zsize zt))) :: nat) div (8 :: nat)) :: nat)) ⟹
		 list_all (λ (c :: lit_underscore). list_all (λ (iter :: byte). (wf_byte iter)) (zbytes_underscore zt c)) c_lst ⟹
		 (wf_datainst (fun_data z y)) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 (Expand (fun_type z x) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 ((zsize zt) ≠ None) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((concatn_underscore  (map (λ (c :: lit_underscore). (zbytes_underscore zt c)) c_lst) ((((the ((zsize zt))) :: nat) div (8 :: nat)) :: nat)) = (list_slice (datainst_BYTES (fun_data z y)) (proj_uN_0 (the ((proj_num__0 i)))) ((((v_n * (the ((zsize zt)))) :: nat) div (8 :: nat)) :: nat))) ⟹
		 (v_n = (length c_lst)) ⟹
		 Step_read (mk_config z [(instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc5 (ARRAY_NEW_DATA x y))]) ((map (λ (c :: lit_underscore). (const (the ((cunpack zt))) (cunpacknum_underscore zt c))) c_lst) @ [(instr_sc5 (ARRAY_NEW_FIXED x (mk_uN v_n)))])"
	| array_get_null :
		"Step_read (mk_config z [(instr_sc4 (instr_st4_REF_NULL ht)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc5 (ARRAY_GET sx_opt x))]) [(instr_sc9 TRAP)]"
	| array_get_oob :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (a < (length (fun_arrayinst z))) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i)))) ≥ (length (arrayinst_FIELDS ((fun_arrayinst z) ! a)))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc5 (ARRAY_GET sx_opt x))]) [(instr_sc9 TRAP)]"
	| array_get_array :
		"((unpackfield_underscore zt sx_opt ((arrayinst_FIELDS ((fun_arrayinst z) ! a)) ! (proj_uN_0 (the ((proj_num__0 i)))))) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i)))) < (length (arrayinst_FIELDS ((fun_arrayinst z) ! a)))) ⟹
		 (a < (length (fun_arrayinst z))) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 (Expand (fun_type z x) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc5 (ARRAY_GET sx_opt x))]) [(instr_val (the ((unpackfield_underscore zt sx_opt ((arrayinst_FIELDS ((fun_arrayinst z) ! a)) ! (proj_uN_0 (the ((proj_num__0 i)))))))))]"
	| array_len_null :
		"Step_read (mk_config z [(instr_sc4 (instr_st4_REF_NULL ht)), (instr_sc5 ARRAY_LEN)]) [(instr_sc9 TRAP)]"
	| array_len_array :
		"(a < (length (fun_arrayinst z))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc5 ARRAY_LEN)]) [(instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN (length (arrayinst_FIELDS ((fun_arrayinst z) ! a)))))))]"
	| array_fill_null :
		"Step_read (mk_config z [(instr_sc4 (instr_st4_REF_NULL ht)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_FILL x))]) [(instr_sc9 TRAP)]"
	| array_fill_oob :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (a < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a)))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_FILL x))]) [(instr_sc9 TRAP)]"
	| array_fill_zero :
		"(~(Step_read_before_array_fill_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_FILL x))]))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_FILL x))]) []"
	| array_fill_succ :
		"((proj_num__0 i) ≠ None) ⟹
		 (~(Step_read_before_array_fill_succ (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_FILL x))]))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_val v_val), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_FILL x))]) [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_val v_val), (instr_sc5 (ARRAY_SET x)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (instr_val v_val), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (instr_sc6 (ARRAY_FILL x))]"
	| array_copy_null1 :
		"Step_read (mk_config z [(instr_sc4 (instr_st4_REF_NULL ht_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_ref v_ref), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))]) [(instr_sc9 TRAP)]"
	| array_copy_null2 :
		"Step_read (mk_config z [(instr_ref v_ref), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc4 (instr_st4_REF_NULL ht_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))]) [(instr_sc9 TRAP)]"
	| array_copy_oob1 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i_1) ≠ None) ⟹
		 (a_1 < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a_1)))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))]) [(instr_sc9 TRAP)]"
	| array_copy_oob2 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 (a_2 < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a_2)))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))]) [(instr_sc9 TRAP)]"
	| array_copy_zero :
		"(~(Step_read_before_array_copy_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))]))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))]) []"
	| array_copy_le :
		"((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt_2))) ⟹
		 (~(Step_read_before_array_copy_le (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))]))) ⟹
		 (Expand (fun_type z x_2) (comptype_ARRAY (mk_fieldtype mut_opt zt_2))) ⟹
		 ((fun_sx zt_2) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i_1)))) ≤ (proj_uN_0 (the ((proj_num__0 i_2))))) ∧ (sx_opt = (the ((fun_sx zt_2))))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))]) [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc5 (ARRAY_GET sx_opt x_2)), (instr_sc5 (ARRAY_SET x_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i_1)))) + 1))))), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i_2)))) + 1))))), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (instr_sc6 (ARRAY_COPY x_1 x_2))]"
	| array_copy_gt :
		"((proj_num__0 i_1) ≠ None) ⟹
		 ((proj_num__0 i_2) ≠ None) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt_2))) ⟹
		 (~(Step_read_before_array_copy_gt (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))]))) ⟹
		 (Expand (fun_type z x_2) (comptype_ARRAY (mk_fieldtype mut_opt zt_2))) ⟹
		 ((fun_sx zt_2) ≠ None) ⟹
		 (sx_opt = (the ((fun_sx zt_2)))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_COPY x_1 x_2))]) [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN (((((proj_uN_0 (the ((proj_num__0 i_1)))) + v_n) :: nat) - (1 :: nat)) :: nat))))), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN (((((proj_uN_0 (the ((proj_num__0 i_2)))) + v_n) :: nat) - (1 :: nat)) :: nat))))), (instr_sc5 (ARRAY_GET sx_opt x_2)), (instr_sc5 (ARRAY_SET x_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_1)), (instr_sc6 (instr_st6_CONST numtype_I32 i_1)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a_2)), (instr_sc6 (instr_st6_CONST numtype_I32 i_2)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (instr_sc6 (ARRAY_COPY x_1 x_2))]"
	| array_init_elem_null :
		"Step_read (mk_config z [(instr_sc4 (instr_st4_REF_NULL ht)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_ELEM x y))]) [(instr_sc9 TRAP)]"
	| array_init_elem_oob1 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (a < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a)))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_ELEM x y))]) [(instr_sc9 TRAP)]"
	| array_init_elem_oob2 :
		"(wf_eleminst (fun_elem z y)) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (eleminst_REFS (fun_elem z y)))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_ELEM x y))]) [(instr_sc9 TRAP)]"
	| array_init_elem_zero :
		"(~(Step_read_before_array_init_elem_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_ELEM x y))]))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_ELEM x y))]) []"
	| array_init_elem_succ :
		"((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 (wf_eleminst (fun_elem z y)) ⟹
		 (~(Step_read_before_array_init_elem_succ (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_ELEM x y))]))) ⟹
		 ((proj_uN_0 (the ((proj_num__0 j)))) < (length (eleminst_REFS (fun_elem z y)))) ⟹
		 (v_ref = ((eleminst_REFS (fun_elem z y)) ! (proj_uN_0 (the ((proj_num__0 j)))))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_ELEM x y))]) [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_ref v_ref), (instr_sc5 (ARRAY_SET x)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 j)))) + 1))))), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (instr_sc6 (ARRAY_INIT_ELEM x y))]"
	| array_init_data_null :
		"Step_read (mk_config z [(instr_sc4 (instr_st4_REF_NULL ht)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_DATA x y))]) [(instr_sc9 TRAP)]"
	| array_init_data_oob1 :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (a < (length (fun_arrayinst z))) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (arrayinst_FIELDS ((fun_arrayinst z) ! a)))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_DATA x y))]) [(instr_sc9 TRAP)]"
	| array_init_data_oob2 :
		"(wf_datainst (fun_data z y)) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 (Expand (fun_type z x) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((zsize zt) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 j)))) + ((((v_n * (the ((zsize zt)))) :: nat) div (8 :: nat)) :: nat)) > (length (datainst_BYTES (fun_data z y)))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_DATA x y))]) [(instr_sc9 TRAP)]"
	| array_init_data_zero :
		"(~(Step_read_before_array_init_data_zero (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_DATA x y))]))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_DATA x y))]) []"
	| array_init_data_num :
		"((cunpack zt) ≠ None) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((zsize zt) ≠ None) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (zbytes_underscore zt c) ⟹
		 (wf_datainst (fun_data z y)) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 (~(Step_read_before_array_init_data_num (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_DATA x y))]))) ⟹
		 (Expand (fun_type z x) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 ((zbytes_underscore zt c) = (list_slice (datainst_BYTES (fun_data z y)) (proj_uN_0 (the ((proj_num__0 j)))) ((((the ((zsize zt))) :: nat) div (8 :: nat)) :: nat))) ⟹
		 Step_read (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_sc6 (instr_st6_CONST numtype_I32 j)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc6 (ARRAY_INIT_DATA x y))]) [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (const (the ((cunpack zt))) (cunpacknum_underscore zt c)), (instr_sc5 (ARRAY_SET x)), (instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 j)))) + ((((the ((zsize zt))) :: nat) div (8 :: nat)) :: nat)))))), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (instr_sc6 (ARRAY_INIT_DATA x y))]"

(* Mutual Recursion at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:5.1-5.88 *)
inductive Step :: "config ⇒ config ⇒ bool" where
	  pure :
		"(Step_pure instr_lst instr'_lst) ⟹
		 Step (mk_config z instr_lst) (mk_config z instr'_lst)"
	| read :
		"(wf_config (mk_config z instr_lst)) ⟹
		 (Step_read (mk_config z instr_lst) instr'_lst) ⟹
		 Step (mk_config z instr_lst) (mk_config z instr'_lst)"
	| ctxt_instrs :
		"(wf_config (mk_config z instr_lst)) ⟹
		 (wf_config (mk_config z' instr'_lst)) ⟹
		 (Step (mk_config z instr_lst) (mk_config z' instr'_lst)) ⟹
		 ((val_lst ≠ []) ∨ (instr_1_lst ≠ [])) ⟹
		 Step (mk_config z ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ (instr_lst @ instr_1_lst))) (mk_config z' ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ (instr'_lst @ instr_1_lst)))"
	| ctxt_label :
		"(wf_config (mk_config z instr_lst)) ⟹
		 (wf_config (mk_config z' instr'_lst)) ⟹
		 (Step (mk_config z instr_lst) (mk_config z' instr'_lst)) ⟹
		 Step (mk_config z [(instr_sc10 (LABEL_underscore v_n instr_0_lst instr_lst))]) (mk_config z' [(instr_sc10 (LABEL_underscore v_n instr_0_lst instr'_lst))])"
	| ctxt_handler :
		"(wf_config (mk_config z instr_lst)) ⟹
		 (wf_config (mk_config z' instr'_lst)) ⟹
		 (Step (mk_config z instr_lst) (mk_config z' instr'_lst)) ⟹
		 Step (mk_config z [(instr_sc10 (HANDLER_underscore v_n catch_lst instr_lst))]) (mk_config z' [(instr_sc10 (HANDLER_underscore v_n catch_lst instr'_lst))])"
	| ctxt_frame :
		"(wf_config (mk_config (mk_state s f') instr_lst)) ⟹
		 (wf_config (mk_config (mk_state s' f'') instr'_lst)) ⟹
		 (Step (mk_config (mk_state s f') instr_lst) (mk_config (mk_state s' f'') instr'_lst)) ⟹
		 Step (mk_config (mk_state s f) [(instr_sc10 (FRAME_underscore v_n f' instr_lst))]) (mk_config (mk_state s' f) [(instr_sc10 (FRAME_underscore v_n f'' instr'_lst))])"
	| Step__throw :
		"(wf_taginst (fun_tag z x)) ⟹
		 list_all (λ (iter :: exninst). (wf_exninst iter)) (fun_exninst z) ⟹
		 (wf_comptype (comptype_FUNC (mk_list t_lst) (mk_list []))) ⟹
		 ((proj_uN_0 x) < (length (fun_tagaddr z))) ⟹
		 (wf_exninst ⦇ exninst_TAG = ((fun_tagaddr z) ! (proj_uN_0 x)), exninst_FIELDS = val_lst ⦈) ⟹
		 ((as_deftype (taginst_TYPE (fun_tag z x))) ≠ None) ⟹
		 (Expand (the ((as_deftype (taginst_TYPE (fun_tag z x))))) (comptype_FUNC (mk_list t_lst) (mk_list []))) ⟹
		 (a = (length (fun_exninst z))) ⟹
		 (exn = ⦇ exninst_TAG = ((fun_tagaddr z) ! (proj_uN_0 x)), exninst_FIELDS = val_lst ⦈) ⟹
		 (v_n = (length val_lst)) ⟹
		 (v_n = (length t_lst)) ⟹
		 Step (mk_config z ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc1 (THROW x))])) (mk_config (add_exninst z [exn]) [(instr_sc9 (instr_st9_REF_EXN_ADDR a)), (instr_sc1 THROW_REF)])"
	| Step__local_set :
		"Step (mk_config z [(instr_val v_val), (instr_sc1 (LOCAL_SET x))]) (mk_config (with_local z x v_val) [])"
	| Step__global_set :
		"Step (mk_config z [(instr_val v_val), (instr_sc2 (GLOBAL_SET x))]) (mk_config (with_global z x v_val) [])"
	| table_set_oob :
		"(wf_tableinst (fun_table z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i)))) ≥ (length (tableinst_REFS (fun_table z x)))) ⟹
		 Step (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_ref v_ref), (instr_sc2 (TABLE_SET x))]) (mk_config z [(instr_sc9 TRAP)])"
	| table_set_val :
		"((proj_num__0 i) ≠ None) ⟹
		 (wf_tableinst (fun_table z x)) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i)))) < (length (tableinst_REFS (fun_table z x)))) ⟹
		 Step (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_ref v_ref), (instr_sc2 (TABLE_SET x))]) (mk_config (with_table z x (proj_uN_0 (the ((proj_num__0 i)))) v_ref) [])"
	| table_grow_succeed :
		"(fun_growtable (fun_table z x) v_n v_ref var_0) ⟹
		 (var_0 ≠ None) ⟹
		 (wf_tableinst (the (var_0))) ⟹
		 (wf_tableinst (fun_table z x)) ⟹
		 (ti = (the (var_0))) ⟹
		 Step (mk_config z [(instr_ref v_ref), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN v_n)))), (instr_sc2 (TABLE_GROW x))]) (mk_config (with_tableinst z x ti) [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN (length (tableinst_REFS (fun_table z x)))))))])"
	| table_grow_fail :
		"(fun_inv_signed_underscore (size (numtype_addrtype at)) (0 - (1 :: nat)) var_0) ⟹
		 Step (mk_config z [(instr_ref v_ref), (instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN v_n)))), (instr_sc2 (TABLE_GROW x))]) (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN var_0))))])"
	| Step__elem_drop :
		"Step (mk_config z [(instr_sc2 (ELEM_DROP x))]) (mk_config (with_elem z x []) [])"
	| store_num_oob :
		"(wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((size nt) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z x)))) ⟹
		 Step (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc6 (instr_st6_CONST nt c)), (instr_sc3 (STORE nt None x ao))]) (mk_config z [(instr_sc9 TRAP)])"
	| store_num_val :
		"((proj_num__0 i) ≠ None) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (nbytes_underscore nt c) ⟹
		 (b_lst = (nbytes_underscore nt c)) ⟹
		 Step (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc6 (instr_st6_CONST nt c)), (instr_sc3 (STORE nt None x ao))]) (mk_config (with_mem z x ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((size nt) :: nat) div (8 :: nat)) :: nat) b_lst) [])"
	| store_pack_oob :
		"(wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_n :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z x)))) ⟹
		 Step (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc6 (instr_st6_CONST (numtype_addrtype v_Inn) c)), (instr_sc3 (STORE (numtype_addrtype v_Inn) (Some (mk_storeop__0 v_Inn (mk_storeop_Inn (mk_sz v_n)))) x ao))]) (mk_config z [(instr_sc9 TRAP)])"
	| store_pack_val :
		"((proj_num__0 i) ≠ None) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_n (wrap__underscore (size (numtype_addrtype v_Inn)) v_n (the ((proj_num__0 c))))) ⟹
		 ((proj_num__0 c) ≠ None) ⟹
		 (wf_uN v_n (wrap__underscore (size (numtype_addrtype v_Inn)) v_n (the ((proj_num__0 c))))) ⟹
		 (b_lst = (ibytes_underscore v_n (wrap__underscore (size (numtype_addrtype v_Inn)) v_n (the ((proj_num__0 c)))))) ⟹
		 Step (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc6 (instr_st6_CONST (numtype_addrtype v_Inn) c)), (instr_sc3 (STORE (numtype_addrtype v_Inn) (Some (mk_storeop__0 v_Inn (mk_storeop_Inn (mk_sz v_n)))) x ao))]) (mk_config (with_mem z x ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_n :: nat) div (8 :: nat)) :: nat) b_lst) [])"
	| vstore_oob :
		"(wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((vsize V128) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z x)))) ⟹
		 Step (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc7 (instr_st7_VCONST V128 c)), (instr_sc3 (VSTORE V128 x ao))]) (mk_config z [(instr_sc9 TRAP)])"
	| vstore_val :
		"((proj_num__0 i) ≠ None) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (vbytes_underscore V128 c) ⟹
		 (b_lst = (vbytes_underscore V128 c)) ⟹
		 Step (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc7 (instr_st7_VCONST V128 c)), (instr_sc3 (VSTORE V128 x ao))]) (mk_config (with_mem z x ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((vsize V128) :: nat) div (8 :: nat)) :: nat) b_lst) [])"
	| vstore_lane_oob :
		"(wf_meminst (fun_mem z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + v_N) > (length (BYTES (fun_mem z x)))) ⟹
		 Step (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc7 (instr_st7_VCONST V128 c)), (instr_sc3 (VSTORE_LANE V128 (mk_sz v_N) x ao j))]) (mk_config z [(instr_sc9 TRAP)])"
	| vstore_lane_val :
		"((proj_num__0 i) ≠ None) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_N (mk_uN (proj_uN_0 (the ((proj_lane__2 ((lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c) ! (proj_uN_0 j)))))))) ⟹
		 ((proj_lane__2 ((lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c) ! (proj_uN_0 j))) ≠ None) ⟹
		 ((proj_uN_0 j) < (length (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c))) ⟹
		 (wf_uN v_N (mk_uN (proj_uN_0 (the ((proj_lane__2 ((lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c) ! (proj_uN_0 j)))))))) ⟹
		 (v_N = (jsize v_Jnn)) ⟹
		 ((v_M :: nat) = ((128 :: nat) div (v_N :: nat))) ⟹
		 (b_lst = (ibytes_underscore v_N (mk_uN (proj_uN_0 (the ((proj_lane__2 ((lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c) ! (proj_uN_0 j))))))))) ⟹
		 Step (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) i)), (instr_sc7 (instr_st7_VCONST V128 c)), (instr_sc3 (VSTORE_LANE V128 (mk_sz v_N) x ao j))]) (mk_config (with_mem z x ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_N :: nat) div (8 :: nat)) :: nat) b_lst) [])"
	| memory_grow_succeed :
		"(fun_growmem (fun_mem z x) v_n var_0) ⟹
		 (var_0 ≠ None) ⟹
		 (wf_meminst (the (var_0))) ⟹
		 (wf_meminst (fun_mem z x)) ⟹
		 (mi = (the (var_0))) ⟹
		 Step (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN v_n)))), (instr_sc3 (MEMORY_GROW x))]) (mk_config (with_meminst z x mi) [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN ((((length (BYTES (fun_mem z x))) :: nat) div ((64 * (Ki )) :: nat)) :: nat)))))])"
	| memory_grow_fail :
		"(fun_inv_signed_underscore (size (numtype_addrtype at)) (0 - (1 :: nat)) var_0) ⟹
		 Step (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN v_n)))), (instr_sc3 (MEMORY_GROW x))]) (mk_config z [(instr_sc6 (instr_st6_CONST (numtype_addrtype at) (mk_num__0 at (mk_uN var_0))))])"
	| Step__data_drop :
		"Step (mk_config z [(instr_sc4 (DATA_DROP x))]) (mk_config (with_data z x []) [])"
	| Step__struct_new :
		"list_all (λ (iter :: structinst). (wf_structinst iter)) (fun_structinst z) ⟹
		 (wf_comptype (comptype_STRUCT (mk_list (list_zipWith (λ (mut_opt :: (mut option)) (zt :: storagetype). (mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ⟹
		 list_all2 (λ (v_val :: val) (zt :: storagetype). ((packfield_underscore zt v_val) ≠ None)) val_lst zt_lst ⟹
		 (wf_structinst ⦇ structinst_TYPE = (fun_type z x), FIELDS = (list_zipWith (λ (v_val :: val) (zt :: storagetype). (the ((packfield_underscore zt v_val)))) val_lst zt_lst) ⦈) ⟹
		 (Expand (fun_type z x) (comptype_STRUCT (mk_list (list_zipWith (λ (mut_opt :: (mut option)) (zt :: storagetype). (mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ⟹
		 (a = (length (fun_structinst z))) ⟹
		 (si = ⦇ structinst_TYPE = (fun_type z x), FIELDS = (list_zipWith (λ (v_val :: val) (zt :: storagetype). (the ((packfield_underscore zt v_val)))) val_lst zt_lst) ⦈) ⟹
		 (v_n = (length val_lst)) ⟹
		 (v_n = (length mut_opt_lst)) ⟹
		 (v_n = (length zt_lst)) ⟹
		 Step (mk_config z ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc4 (STRUCT_NEW x))])) (mk_config (add_structinst z [si]) [(instr_sc9 (instr_st9_REF_STRUCT_ADDR a))])"
	| struct_set_null :
		"Step (mk_config z [(instr_sc4 (instr_st4_REF_NULL ht)), (instr_val v_val), (instr_sc5 (STRUCT_SET x i))]) (mk_config z [(instr_sc9 TRAP)])"
	| struct_set_struct :
		"((packfield_underscore (zt_lst ! (proj_uN_0 i)) v_val) ≠ None) ⟹
		 ((proj_uN_0 i) < (length zt_lst)) ⟹
		 (wf_comptype (comptype_STRUCT (mk_list (list_zipWith (λ (mut_opt :: (mut option)) (zt :: storagetype). (mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ⟹
		 (Expand (fun_type z x) (comptype_STRUCT (mk_list (list_zipWith (λ (mut_opt :: (mut option)) (zt :: storagetype). (mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ⟹
		 Step (mk_config z [(instr_sc9 (instr_st9_REF_STRUCT_ADDR a)), (instr_val v_val), (instr_sc5 (STRUCT_SET x i))]) (mk_config (with_struct z a (proj_uN_0 i) (the ((packfield_underscore (zt_lst ! (proj_uN_0 i)) v_val)))) [])"
	| Step__array_new_fixed :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 list_all (λ (v_val :: val). ((packfield_underscore zt v_val) ≠ None)) val_lst ⟹
		 (wf_arrayinst ⦇ arrayinst_TYPE = (fun_type z x), arrayinst_FIELDS = (map (λ (v_val :: val). (the ((packfield_underscore zt v_val)))) val_lst) ⦈) ⟹
		 (Expand (fun_type z x) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 ((a = (length (fun_arrayinst z))) ∧ (ai = ⦇ arrayinst_TYPE = (fun_type z x), arrayinst_FIELDS = (map (λ (v_val :: val). (the ((packfield_underscore zt v_val)))) val_lst) ⦈)) ⟹
		 (v_n = (length val_lst)) ⟹
		 Step (mk_config z ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc5 (ARRAY_NEW_FIXED x (mk_uN v_n)))])) (mk_config (add_arrayinst z [ai]) [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a))])"
	| array_set_null :
		"Step (mk_config z [(instr_sc4 (instr_st4_REF_NULL ht)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_val v_val), (instr_sc5 (ARRAY_SET x))]) (mk_config z [(instr_sc9 TRAP)])"
	| array_set_oob :
		"list_all (λ (iter :: arrayinst). (wf_arrayinst iter)) (fun_arrayinst z) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (a < (length (fun_arrayinst z))) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i)))) ≥ (length (arrayinst_FIELDS ((fun_arrayinst z) ! a)))) ⟹
		 Step (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_val v_val), (instr_sc5 (ARRAY_SET x))]) (mk_config z [(instr_sc9 TRAP)])"
	| array_set_array :
		"((proj_num__0 i) ≠ None) ⟹
		 ((packfield_underscore zt v_val) ≠ None) ⟹
		 (wf_comptype (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 (Expand (fun_type z x) (comptype_ARRAY (mk_fieldtype mut_opt zt))) ⟹
		 Step (mk_config z [(instr_sc9 (instr_st9_REF_ARRAY_ADDR a)), (instr_sc6 (instr_st6_CONST numtype_I32 i)), (instr_val v_val), (instr_sc5 (ARRAY_SET x))]) (mk_config (with_array z a (proj_uN_0 (the ((proj_num__0 i)))) (the ((packfield_underscore zt v_val)))) [])"

(* Mutual Recursion at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:8.1-8.92 *)
inductive Steps :: "config ⇒ config ⇒ bool" where
	  Steps__refl :
		"Steps (mk_config z instr_lst) (mk_config z instr_lst)"
	| Steps__trans :
		"(wf_config (mk_config z instr_lst)) ⟹
		 (wf_config (mk_config z' instr'_lst)) ⟹
		 (wf_config (mk_config z'' instr''_lst)) ⟹
		 (Step (mk_config z instr_lst) (mk_config z' instr'_lst)) ⟹
		 (Steps (mk_config z' instr'_lst) (mk_config z'' instr''_lst)) ⟹
		 Steps (mk_config z instr_lst) (mk_config z'' instr''_lst)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:1111.1-1111.108 *)
inductive Eval_expr :: "state ⇒ expr ⇒ state ⇒ (val list) ⇒ bool" where
	  mk_Eval_expr :
		"(wf_config (mk_config z instr_lst)) ⟹
		 (wf_config (mk_config z' (map (λ (v_val :: val). (instr_val v_val)) val_lst))) ⟹
		 (Steps (mk_config z instr_lst) (mk_config z' (map (λ (v_val :: val). (instr_val v_val)) val_lst))) ⟹
		 Eval_expr z instr_lst z' val_lst"

(* Mutual Recursion at: ../specification/wasm-3.0/4.4-execution.modules.spectec:7.1-7.63 *)
inductive fun_alloctypes :: "(type list) ⇒ (deftype list) ⇒ bool" where
	  fun_alloctypes_case_0 :
		"fun_alloctypes [] []"
	| fun_alloctypes_case_1 :
		"(fun_rolldt x v_rectype var_2) ⟹
		 (fun_subst_all_deftypes var_2 (map (λ (deftype' :: deftype). (typeuse_deftype deftype')) deftype'_lst) var_1) ⟹
		 (fun_alloctypes type'_lst var_0) ⟹
		 (wf_uN 32 x) ⟹
		 (deftype'_lst = var_0) ⟹
		 (v_type = (res_TYPE v_rectype)) ⟹
		 (deftype_lst = var_1) ⟹
		 ((proj_uN_0 x) = (length deftype'_lst)) ⟹
		 fun_alloctypes (type'_lst @ [v_type]) (deftype'_lst @ deftype_lst)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:15.6-15.15 *)
inductive fun_alloctag :: "store ⇒ tagtype ⇒ (store * tagaddr) ⇒ bool" where
	  fun_alloctag_case_0 :
		"(wf_taginst ⦇ taginst_TYPE = v_tagtype ⦈) ⟹
		 (v_taginst = ⦇ taginst_TYPE = v_tagtype ⦈) ⟹
		 fun_alloctag s v_tagtype ((append_store s ⦇ store_TAGS = [v_taginst], store_GLOBALS = [], store_MEMS = [], store_TABLES = [], store_FUNCS = [], store_DATAS = [], store_ELEMS = [], STRUCTS = [], ARRAYS = [], EXNS = [] ⦈), (length (store_TAGS s)))"

(* Mutual Recursion at: ../specification/wasm-3.0/4.4-execution.modules.spectec:20.1-20.102 *)
inductive fun_alloctags :: "store ⇒ (tagtype list) ⇒ (store * (tagaddr list)) ⇒ bool" where
	  fun_alloctags_case_0 :
		"fun_alloctags s [] (s, [])"
	| fun_alloctags_case_1 :
		"(fun_alloctags s_1 tagtype'_lst var_1) ⟹
		 (fun_alloctag s v_tagtype var_0) ⟹
		 (wf_store s_1) ⟹
		 (wf_store (fst var_0)) ⟹
		 (wf_store (fst var_1)) ⟹
		 ((s_1, ja) = var_0) ⟹
		 ((s_2, ja'_lst) = var_1) ⟹
		 fun_alloctags s ([v_tagtype] @ tagtype'_lst) (s_2, ([ja] @ ja'_lst))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:26.6-26.18 *)
inductive fun_allocglobal :: "store ⇒ globaltype ⇒ val ⇒ (store * globaladdr) ⇒ bool" where
	  fun_allocglobal_case_0 :
		"(wf_globalinst ⦇ globalinst_TYPE = v_globaltype, VALUE = v_val ⦈) ⟹
		 (v_globalinst = ⦇ globalinst_TYPE = v_globaltype, VALUE = v_val ⦈) ⟹
		 fun_allocglobal s v_globaltype v_val ((append_store s ⦇ store_TAGS = [], store_GLOBALS = [v_globalinst], store_MEMS = [], store_TABLES = [], store_FUNCS = [], store_DATAS = [], store_ELEMS = [], STRUCTS = [], ARRAYS = [], EXNS = [] ⦈), (length (store_GLOBALS s)))"

(* Mutual Recursion at: ../specification/wasm-3.0/4.4-execution.modules.spectec:31.1-31.122 *)
inductive fun_allocglobals :: "store ⇒ (globaltype list) ⇒ (val list) ⇒ (store * (globaladdr list)) ⇒ bool" where
	  fun_allocglobals_case_0 :
		"fun_allocglobals s [] [] (s, [])"
	| fun_allocglobals_case_1 :
		"(fun_allocglobals s_1 globaltype'_lst val'_lst var_1) ⟹
		 (fun_allocglobal s v_globaltype v_val var_0) ⟹
		 (wf_store s_1) ⟹
		 (wf_store (fst var_0)) ⟹
		 (wf_store (fst var_1)) ⟹
		 ((s_1, ga) = var_0) ⟹
		 ((s_2, ga'_lst) = var_1) ⟹
		 fun_allocglobals s ([v_globaltype] @ globaltype'_lst) ([v_val] @ val'_lst) (s_2, ([ga] @ ga'_lst))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:37.6-37.15 *)
inductive fun_allocmem :: "store ⇒ memtype ⇒ (store * memaddr) ⇒ bool" where
	  fun_allocmem_case_0 :
		"(wf_meminst ⦇ meminst_TYPE = (PAGE at (mk_limits i j_opt)), BYTES = (repeat ((proj_uN_0 i) * (64 * (Ki ))) (mk_byte 0)) ⦈) ⟹
		 (v_meminst = ⦇ meminst_TYPE = (PAGE at (mk_limits i j_opt)), BYTES = (repeat ((proj_uN_0 i) * (64 * (Ki ))) (mk_byte 0)) ⦈) ⟹
		 fun_allocmem s (PAGE at (mk_limits i j_opt)) ((append_store s ⦇ store_TAGS = [], store_GLOBALS = [], store_MEMS = [v_meminst], store_TABLES = [], store_FUNCS = [], store_DATAS = [], store_ELEMS = [], STRUCTS = [], ARRAYS = [], EXNS = [] ⦈), (length (store_MEMS s)))"

(* Mutual Recursion at: ../specification/wasm-3.0/4.4-execution.modules.spectec:42.1-42.102 *)
inductive fun_allocmems :: "store ⇒ (memtype list) ⇒ (store * (memaddr list)) ⇒ bool" where
	  fun_allocmems_case_0 :
		"fun_allocmems s [] (s, [])"
	| fun_allocmems_case_1 :
		"(fun_allocmems s_1 memtype'_lst var_1) ⟹
		 (fun_allocmem s v_memtype var_0) ⟹
		 (wf_store s_1) ⟹
		 (wf_store (fst var_0)) ⟹
		 (wf_store (fst var_1)) ⟹
		 ((s_1, ma) = var_0) ⟹
		 ((s_2, ma'_lst) = var_1) ⟹
		 fun_allocmems s ([v_memtype] @ memtype'_lst) (s_2, ([ma] @ ma'_lst))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:48.6-48.17 *)
inductive fun_alloctable :: "store ⇒ tabletype ⇒ ref ⇒ (store * tableaddr) ⇒ bool" where
	  fun_alloctable_case_0 :
		"(wf_tableinst ⦇ tableinst_TYPE = (mk_tabletype at (mk_limits i j_opt) rt), tableinst_REFS = (repeat (proj_uN_0 i) v_ref) ⦈) ⟹
		 (v_tableinst = ⦇ tableinst_TYPE = (mk_tabletype at (mk_limits i j_opt) rt), tableinst_REFS = (repeat (proj_uN_0 i) v_ref) ⦈) ⟹
		 fun_alloctable s (mk_tabletype at (mk_limits i j_opt) rt) v_ref ((append_store s ⦇ store_TAGS = [], store_GLOBALS = [], store_MEMS = [], store_TABLES = [v_tableinst], store_FUNCS = [], store_DATAS = [], store_ELEMS = [], STRUCTS = [], ARRAYS = [], EXNS = [] ⦈), (length (store_TABLES s)))"

(* Mutual Recursion at: ../specification/wasm-3.0/4.4-execution.modules.spectec:53.1-53.118 *)
inductive fun_alloctables :: "store ⇒ (tabletype list) ⇒ (ref list) ⇒ (store * (tableaddr list)) ⇒ bool" where
	  fun_alloctables_case_0 :
		"fun_alloctables s [] [] (s, [])"
	| fun_alloctables_case_1 :
		"(fun_alloctables s_1 tabletype'_lst ref'_lst var_1) ⟹
		 (fun_alloctable s v_tabletype v_ref var_0) ⟹
		 (wf_store s_1) ⟹
		 (wf_store (fst var_0)) ⟹
		 (wf_store (fst var_1)) ⟹
		 ((s_1, ta) = var_0) ⟹
		 ((s_2, ta'_lst) = var_1) ⟹
		 fun_alloctables s ([v_tabletype] @ tabletype'_lst) ([v_ref] @ ref'_lst) (s_2, ([ta] @ ta'_lst))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:59.6-59.16 *)
inductive fun_allocfunc :: "store ⇒ deftype ⇒ funccode ⇒ moduleinst ⇒ (store * funcaddr) ⇒ bool" where
	  fun_allocfunc_case_0 :
		"(wf_funcinst ⦇ funcinst_TYPE = v_deftype, funcinst_MODULE = v_moduleinst, CODE = v_funccode ⦈) ⟹
		 (v_funcinst = ⦇ funcinst_TYPE = v_deftype, funcinst_MODULE = v_moduleinst, CODE = v_funccode ⦈) ⟹
		 fun_allocfunc s v_deftype v_funccode v_moduleinst ((append_store s ⦇ store_TAGS = [], store_GLOBALS = [], store_MEMS = [], store_TABLES = [], store_FUNCS = [v_funcinst], store_DATAS = [], store_ELEMS = [], STRUCTS = [], ARRAYS = [], EXNS = [] ⦈), (length (store_FUNCS s)))"

(* Mutual Recursion at: ../specification/wasm-3.0/4.4-execution.modules.spectec:64.1-64.133 *)
inductive fun_allocfuncs :: "store ⇒ (deftype list) ⇒ (funccode list) ⇒ (moduleinst list) ⇒ (store * (funcaddr list)) ⇒ bool" where
	  fun_allocfuncs_case_0 :
		"fun_allocfuncs s [] [] [] (s, [])"
	| fun_allocfuncs_case_1 :
		"(fun_allocfuncs s_1 dt'_lst funccode'_lst moduleinst'_lst var_1) ⟹
		 (fun_allocfunc s dt v_funccode v_moduleinst var_0) ⟹
		 (wf_store s_1) ⟹
		 (wf_store (fst var_0)) ⟹
		 (wf_store (fst var_1)) ⟹
		 ((s_1, fa) = var_0) ⟹
		 ((s_2, fa'_lst) = var_1) ⟹
		 fun_allocfuncs s ([dt] @ dt'_lst) ([v_funccode] @ funccode'_lst) ([v_moduleinst] @ moduleinst'_lst) (s_2, ([fa] @ fa'_lst))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:70.6-70.16 *)
inductive fun_allocdata :: "store ⇒ res_datatype ⇒ (byte list) ⇒ (store * dataaddr) ⇒ bool" where
	  fun_allocdata_case_0 :
		"(wf_datainst ⦇ datainst_BYTES = byte_lst ⦈) ⟹
		 (v_datainst = ⦇ datainst_BYTES = byte_lst ⦈) ⟹
		 fun_allocdata s OK byte_lst ((append_store s ⦇ store_TAGS = [], store_GLOBALS = [], store_MEMS = [], store_TABLES = [], store_FUNCS = [], store_DATAS = [v_datainst], store_ELEMS = [], STRUCTS = [], ARRAYS = [], EXNS = [] ⦈), (length (store_DATAS s)))"

(* Mutual Recursion at: ../specification/wasm-3.0/4.4-execution.modules.spectec:75.1-75.118 *)
inductive fun_allocdatas :: "store ⇒ (res_datatype list) ⇒ ((byte list) list) ⇒ (store * (dataaddr list)) ⇒ bool" where
	  fun_allocdatas_case_0 :
		"fun_allocdatas s [] [] (s, [])"
	| fun_allocdatas_case_1 :
		"(fun_allocdatas s_1 ok'_lst b'_lst_lst var_1) ⟹
		 (fun_allocdata s ok b_lst var_0) ⟹
		 (wf_store s_1) ⟹
		 (wf_store (fst var_0)) ⟹
		 (wf_store (fst var_1)) ⟹
		 ((s_1, da) = var_0) ⟹
		 ((s_2, da'_lst) = var_1) ⟹
		 fun_allocdatas s ([ok] @ ok'_lst) ([b_lst] @ b'_lst_lst) (s_2, ([da] @ da'_lst))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:81.6-81.16 *)
inductive fun_allocelem :: "store ⇒ elemtype ⇒ (ref list) ⇒ (store * elemaddr) ⇒ bool" where
	  fun_allocelem_case_0 :
		"(wf_eleminst ⦇ eleminst_TYPE = v_elemtype, eleminst_REFS = ref_lst ⦈) ⟹
		 (v_eleminst = ⦇ eleminst_TYPE = v_elemtype, eleminst_REFS = ref_lst ⦈) ⟹
		 fun_allocelem s v_elemtype ref_lst ((append_store s ⦇ store_TAGS = [], store_GLOBALS = [], store_MEMS = [], store_TABLES = [], store_FUNCS = [], store_DATAS = [], store_ELEMS = [v_eleminst], STRUCTS = [], ARRAYS = [], EXNS = [] ⦈), (length (store_ELEMS s)))"

(* Mutual Recursion at: ../specification/wasm-3.0/4.4-execution.modules.spectec:86.1-86.117 *)
inductive fun_allocelems :: "store ⇒ (elemtype list) ⇒ ((ref list) list) ⇒ (store * (elemaddr list)) ⇒ bool" where
	  fun_allocelems_case_0 :
		"fun_allocelems s [] [] (s, [])"
	| fun_allocelems_case_1 :
		"(fun_allocelems s_1 rt'_lst ref'_lst_lst var_1) ⟹
		 (fun_allocelem s rt ref_lst var_0) ⟹
		 (wf_store s_1) ⟹
		 (wf_store (fst var_0)) ⟹
		 (wf_store (fst var_1)) ⟹
		 ((s_1, ea) = var_0) ⟹
		 ((s_2, ea'_lst) = var_1) ⟹
		 fun_allocelems s ([rt] @ rt'_lst) ([ref_lst] @ ref'_lst_lst) (s_2, ([ea] @ ea'_lst))"

(* Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:92.1-92.90 *)
function (sequential) allocexport :: "moduleinst ⇒ export ⇒ exportinst" where
		  "allocexport v_moduleinst (EXPORT v_name (TAG x)) = ⦇ NAME = v_name, ADDR = (externaddr_TAG ((moduleinst_TAGS v_moduleinst) ! (proj_uN_0 x))) ⦈"
		| "allocexport v_moduleinst (EXPORT v_name (GLOBAL x)) = ⦇ NAME = v_name, ADDR = (externaddr_GLOBAL ((moduleinst_GLOBALS v_moduleinst) ! (proj_uN_0 x))) ⦈"
		| "allocexport v_moduleinst (EXPORT v_name (MEM x)) = ⦇ NAME = v_name, ADDR = (externaddr_MEM ((moduleinst_MEMS v_moduleinst) ! (proj_uN_0 x))) ⦈"
		| "allocexport v_moduleinst (EXPORT v_name (TABLE x)) = ⦇ NAME = v_name, ADDR = (externaddr_TABLE ((moduleinst_TABLES v_moduleinst) ! (proj_uN_0 x))) ⦈"
		| "allocexport v_moduleinst (EXPORT v_name (FUNC x)) = ⦇ NAME = v_name, ADDR = (externaddr_FUNC ((moduleinst_FUNCS v_moduleinst) ! (proj_uN_0 x))) ⦈"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:99.1-99.104 *)
function (sequential) allocexports :: "moduleinst ⇒ (export list) ⇒ (exportinst list)" where
		  "allocexports v_moduleinst export_lst = (map (λ (v_export :: export). (allocexport v_moduleinst v_export)) export_lst)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:103.6-103.18 *)
inductive fun_allocmodule :: "store ⇒ module ⇒ (externaddr list) ⇒ (val list) ⇒ (ref list) ⇒ ((ref list) list) ⇒ (store * moduleinst) ⇒ bool" where
	  fun_allocmodule_case_0 :
		"(fun_alloctypes type_lst var_17) ⟹
		 (fun_funcsxa externaddr_lst var_16) ⟹
		 (fun_tablesxa externaddr_lst var_15) ⟹
		 (fun_memsxa externaddr_lst var_14) ⟹
		 (fun_globalsxa externaddr_lst var_13) ⟹
		 (fun_tagsxa externaddr_lst var_12) ⟹
		 list_all (λ (x :: idx). ((proj_uN_0 x) < (length dt_lst))) x_lst ⟹
		 (fun_allocfuncs s_6 (map (λ (x :: idx). (dt_lst ! (proj_uN_0 x))) x_lst) (list_map3 (λ (expr_F :: expr) (local_lst :: (local list)) (x :: idx). (funccode_FUNC x local_lst expr_F)) expr_F_lst local_lst_lst x_lst) (repeat (length func_lst) v_moduleinst) var_11) ⟹
		 ((length var_10_lst) = (length elemtype_lst)) ⟹
		 list_all2 (λ (var_10 :: elemtype) (v_elemtype :: elemtype). (fun_subst_all_reftype v_elemtype (map (λ (dt :: deftype). (typeuse_deftype dt)) dt_lst) var_10)) var_10_lst elemtype_lst ⟹
		 (fun_allocelems s_5 var_10_lst ref_E_lst_lst var_9) ⟹
		 (fun_allocdatas s_4 (repeat (length data_lst) OK) byte_lst_lst var_8) ⟹
		 ((length var_7_lst) = (length tabletype_lst)) ⟹
		 list_all2 (λ (var_7 :: tabletype) (v_tabletype :: tabletype). (fun_subst_all_tabletype v_tabletype (map (λ (dt :: deftype). (typeuse_deftype dt)) dt_lst) var_7)) var_7_lst tabletype_lst ⟹
		 (fun_alloctables s_3 var_7_lst ref_T_lst var_6) ⟹
		 ((length var_5_lst) = (length memtype_lst)) ⟹
		 list_all2 (λ (var_5 :: memtype) (v_memtype :: memtype). (fun_subst_all_memtype v_memtype (map (λ (dt :: deftype). (typeuse_deftype dt)) dt_lst) var_5)) var_5_lst memtype_lst ⟹
		 (fun_allocmems s_2 var_5_lst var_4) ⟹
		 ((length var_3_lst) = (length globaltype_lst)) ⟹
		 list_all2 (λ (var_3 :: globaltype) (v_globaltype :: globaltype). (fun_subst_all_globaltype v_globaltype (map (λ (dt :: deftype). (typeuse_deftype dt)) dt_lst) var_3)) var_3_lst globaltype_lst ⟹
		 (fun_allocglobals s_1 var_3_lst val_G_lst var_2) ⟹
		 ((length var_1_lst) = (length tagtype_lst)) ⟹
		 list_all2 (λ (var_1 :: tagtype) (v_tagtype :: tagtype). (fun_subst_all_tagtype v_tagtype (map (λ (dt :: deftype). (typeuse_deftype dt)) dt_lst) var_1)) var_1_lst tagtype_lst ⟹
		 (fun_alloctags s var_1_lst var_0) ⟹
		 (wf_store s_1) ⟹
		 (wf_store s_2) ⟹
		 (wf_store s_3) ⟹
		 (wf_store s_4) ⟹
		 (wf_store s_5) ⟹
		 (wf_store s_6) ⟹
		 (wf_store (fst var_0)) ⟹
		 list_all (λ (var_1 :: tagtype). (wf_typeuse var_1)) var_1_lst ⟹
		 (wf_store (fst var_2)) ⟹
		 list_all (λ (var_3 :: globaltype). (wf_globaltype var_3)) var_3_lst ⟹
		 (wf_store (fst var_4)) ⟹
		 list_all (λ (var_5 :: memtype). (wf_memtype var_5)) var_5_lst ⟹
		 (wf_store (fst var_6)) ⟹
		 list_all (λ (var_7 :: tabletype). (wf_tabletype var_7)) var_7_lst ⟹
		 (wf_store (fst var_8)) ⟹
		 (wf_store (fst var_9)) ⟹
		 list_all (λ (var_10 :: elemtype). (wf_reftype var_10)) var_10_lst ⟹
		 (wf_store (fst var_11)) ⟹
		 list_all (λ (iter :: exportinst). (wf_exportinst iter)) (allocexports ⦇ moduleinst_TYPES = [], moduleinst_TAGS = (aa_I_lst @ aa_lst), moduleinst_GLOBALS = (ga_I_lst @ ga_lst), moduleinst_MEMS = (ma_I_lst @ ma_lst), moduleinst_TABLES = (ta_I_lst @ ta_lst), moduleinst_FUNCS = (fa_I_lst @ fa_lst), moduleinst_DATAS = [], moduleinst_ELEMS = [], EXPORTS = [] ⦈ export_lst) ⟹
		 (wf_module (module_MODULE type_lst import_lst tag_lst global_lst mem_lst table_lst func_lst data_lst elem_lst start_opt export_lst)) ⟹
		 list_all (λ (v_tagtype :: tagtype). (wf_tag (tag_TAG v_tagtype))) tagtype_lst ⟹
		 ((length expr_G_lst) = (length globaltype_lst)) ⟹
		 list_all2 (λ (expr_G :: expr) (v_globaltype :: globaltype). (wf_global (global_GLOBAL v_globaltype expr_G))) expr_G_lst globaltype_lst ⟹
		 list_all (λ (v_memtype :: memtype). (wf_mem (MEMORY v_memtype))) memtype_lst ⟹
		 ((length expr_T_lst) = (length tabletype_lst)) ⟹
		 list_all2 (λ (expr_T :: expr) (v_tabletype :: tabletype). (wf_table (table_TABLE v_tabletype expr_T))) expr_T_lst tabletype_lst ⟹
		 ((length expr_F_lst) = (length local_lst_lst)) ⟹
		 ((length expr_F_lst) = (length x_lst)) ⟹
		 list_all3 (λ (expr_F :: expr) (local_lst :: (local list)) (x :: idx). (wf_func (func_FUNC x local_lst expr_F))) expr_F_lst local_lst_lst x_lst ⟹
		 ((length byte_lst_lst) = (length datamode_lst)) ⟹
		 list_all2 (λ (byte_lst :: (byte list)) (v_datamode :: datamode). (wf_data (DATA byte_lst v_datamode))) byte_lst_lst datamode_lst ⟹
		 ((length elemmode_lst) = (length elemtype_lst)) ⟹
		 ((length elemmode_lst) = (length expr_E_lst_lst)) ⟹
		 list_all3 (λ (v_elemmode :: elemmode) (v_elemtype :: elemtype) (expr_E_lst :: (expr list)). (wf_elem (ELEM v_elemtype expr_E_lst v_elemmode))) elemmode_lst elemtype_lst expr_E_lst_lst ⟹
		 (wf_moduleinst ⦇ moduleinst_TYPES = [], moduleinst_TAGS = (aa_I_lst @ aa_lst), moduleinst_GLOBALS = (ga_I_lst @ ga_lst), moduleinst_MEMS = (ma_I_lst @ ma_lst), moduleinst_TABLES = (ta_I_lst @ ta_lst), moduleinst_FUNCS = (fa_I_lst @ fa_lst), moduleinst_DATAS = [], moduleinst_ELEMS = [], EXPORTS = [] ⦈) ⟹
		 (wf_moduleinst ⦇ moduleinst_TYPES = dt_lst, moduleinst_TAGS = (aa_I_lst @ aa_lst), moduleinst_GLOBALS = (ga_I_lst @ ga_lst), moduleinst_MEMS = (ma_I_lst @ ma_lst), moduleinst_TABLES = (ta_I_lst @ ta_lst), moduleinst_FUNCS = (fa_I_lst @ fa_lst), moduleinst_DATAS = da_lst, moduleinst_ELEMS = ea_lst, EXPORTS = xi_lst ⦈) ⟹
		 (v_module = (module_MODULE type_lst import_lst tag_lst global_lst mem_lst table_lst func_lst data_lst elem_lst start_opt export_lst)) ⟹
		 (tag_lst = (map (λ (v_tagtype :: tagtype). (tag_TAG v_tagtype)) tagtype_lst)) ⟹
		 (global_lst = (list_zipWith (λ (expr_G :: expr) (v_globaltype :: globaltype). (global_GLOBAL v_globaltype expr_G)) expr_G_lst globaltype_lst)) ⟹
		 (mem_lst = (map (λ (v_memtype :: memtype). (MEMORY v_memtype)) memtype_lst)) ⟹
		 (table_lst = (list_zipWith (λ (expr_T :: expr) (v_tabletype :: tabletype). (table_TABLE v_tabletype expr_T)) expr_T_lst tabletype_lst)) ⟹
		 (func_lst = (list_map3 (λ (expr_F :: expr) (local_lst :: (local list)) (x :: idx). (func_FUNC x local_lst expr_F)) expr_F_lst local_lst_lst x_lst)) ⟹
		 (data_lst = (list_zipWith (λ (byte_lst :: (byte list)) (v_datamode :: datamode). (DATA byte_lst v_datamode)) byte_lst_lst datamode_lst)) ⟹
		 (elem_lst = (list_map3 (λ (v_elemmode :: elemmode) (v_elemtype :: elemtype) (expr_E_lst :: (expr list)). (ELEM v_elemtype expr_E_lst v_elemmode)) elemmode_lst elemtype_lst expr_E_lst_lst)) ⟹
		 (aa_I_lst = var_12) ⟹
		 (ga_I_lst = var_13) ⟹
		 (ma_I_lst = var_14) ⟹
		 (ta_I_lst = var_15) ⟹
		 (fa_I_lst = var_16) ⟹
		 (dt_lst = var_17) ⟹
		 (fa_lst = (mkseq (λ i_F. ((length (store_FUNCS s)) + i_F)) (length func_lst))) ⟹
		 ((s_1, aa_lst) = var_0) ⟹
		 ((s_2, ga_lst) = var_2) ⟹
		 ((s_3, ma_lst) = var_4) ⟹
		 ((s_4, ta_lst) = var_6) ⟹
		 ((s_5, da_lst) = var_8) ⟹
		 ((s_6, ea_lst) = var_9) ⟹
		 ((s_7, fa_lst) = var_11) ⟹
		 (xi_lst = (allocexports ⦇ moduleinst_TYPES = [], moduleinst_TAGS = (aa_I_lst @ aa_lst), moduleinst_GLOBALS = (ga_I_lst @ ga_lst), moduleinst_MEMS = (ma_I_lst @ ma_lst), moduleinst_TABLES = (ta_I_lst @ ta_lst), moduleinst_FUNCS = (fa_I_lst @ fa_lst), moduleinst_DATAS = [], moduleinst_ELEMS = [], EXPORTS = [] ⦈ export_lst)) ⟹
		 (v_moduleinst = ⦇ moduleinst_TYPES = dt_lst, moduleinst_TAGS = (aa_I_lst @ aa_lst), moduleinst_GLOBALS = (ga_I_lst @ ga_lst), moduleinst_MEMS = (ma_I_lst @ ma_lst), moduleinst_TABLES = (ta_I_lst @ ta_lst), moduleinst_FUNCS = (fa_I_lst @ fa_lst), moduleinst_DATAS = da_lst, moduleinst_ELEMS = ea_lst, EXPORTS = xi_lst ⦈) ⟹
		 fun_allocmodule s v_module externaddr_lst val_G_lst ref_T_lst ref_E_lst_lst (s_7, v_moduleinst)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:148.6-148.15 *)
inductive fun_rundata_underscore :: "dataidx ⇒ data ⇒ (instr list) ⇒ bool" where
	  fun_rundata__case_0 :
		"(v_n = (length b_lst)) ⟹
		 fun_rundata_underscore x (DATA b_lst datamode_PASSIVE) []"
	| fun_rundata__case_1 :
		"(v_n = (length b_lst)) ⟹
		 fun_rundata_underscore x (DATA b_lst (datamode_ACTIVE y instr_lst)) (instr_lst @ [(instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN 0)))), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc3 (MEMORY_INIT y x)), (instr_sc4 (DATA_DROP x))])"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:153.6-153.15 *)
inductive fun_runelem_underscore :: "elemidx ⇒ elem ⇒ (instr list) ⇒ bool" where
	  fun_runelem__case_0 :
		"(v_n = (length e_lst)) ⟹
		 fun_runelem_underscore x (ELEM rt e_lst PASSIVE) []"
	| fun_runelem__case_1 :
		"(v_n = (length e_lst)) ⟹
		 fun_runelem_underscore x (ELEM rt e_lst DECLARE) [(instr_sc2 (ELEM_DROP x))]"
	| fun_runelem__case_2 :
		"(v_n = (length e_lst)) ⟹
		 fun_runelem_underscore x (ELEM rt e_lst (ACTIVE y instr_lst)) (instr_lst @ [(instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN 0)))), (instr_sc6 (instr_st6_CONST numtype_I32 (mk_num__0 I32 (mk_uN v_n)))), (instr_sc2 (TABLE_INIT y x)), (instr_sc2 (ELEM_DROP x))])"

(* Mutual Recursion at: ../specification/wasm-3.0/4.4-execution.modules.spectec:160.1-160.92 *)
inductive fun_evalexprs :: "state ⇒ (expr list) ⇒ (state * (ref list)) ⇒ bool" where
	  fun_evalexprs_case_0 :
		"fun_evalexprs z [] (z, [])"
	| fun_evalexprs_case_1 :
		"(fun_evalexprs z' expr'_lst var_0) ⟹
		 (wf_state z') ⟹
		 (wf_state (fst var_0)) ⟹
		 list_all (λ (iter :: ref). (wf_ref iter)) (snd var_0) ⟹
		 (Eval_expr z v_expr z' [(val_ref v_ref)]) ⟹
		 ((z'', ref'_lst) = var_0) ⟹
		 fun_evalexprs z ([v_expr] @ expr'_lst) (z'', ([v_ref] @ ref'_lst))"

(* Mutual Recursion at: ../specification/wasm-3.0/4.4-execution.modules.spectec:167.1-167.96 *)
inductive fun_evalexprss :: "state ⇒ ((expr list) list) ⇒ (state * ((ref list) list)) ⇒ bool" where
	  fun_evalexprss_case_0 :
		"fun_evalexprss z [] (z, [])"
	| fun_evalexprss_case_1 :
		"(fun_evalexprss z' expr'_lst_lst var_1) ⟹
		 (fun_evalexprs z expr_lst var_0) ⟹
		 (wf_state z') ⟹
		 (wf_state (fst var_0)) ⟹
		 list_all (λ (iter :: ref). (wf_ref iter)) (snd var_0) ⟹
		 (wf_state (fst var_1)) ⟹
		 list_all (λ (iter :: (ref list)). list_all (λ (iter :: ref). (wf_ref iter)) iter) (snd var_1) ⟹
		 ((z', ref_lst) = var_0) ⟹
		 ((z'', ref'_lst_lst) = var_1) ⟹
		 fun_evalexprss z ([expr_lst] @ expr'_lst_lst) (z'', ([ref_lst] @ ref'_lst_lst))"

(* Mutual Recursion at: ../specification/wasm-3.0/4.4-execution.modules.spectec:174.1-174.111 *)
inductive fun_evalglobals :: "state ⇒ (globaltype list) ⇒ (expr list) ⇒ (state * (val list)) ⇒ bool" where
	  fun_evalglobals_case_0 :
		"fun_evalglobals z [] [] (z, [])"
	| fun_evalglobals_case_1 :
		"(fun_evalglobals (mk_state s' (f ⦇ MODULE := (MODULE f ⦇ moduleinst_GLOBALS := ((moduleinst_GLOBALS (MODULE f)) @ [a])  ⦈)  ⦈)) gt'_lst expr'_lst var_1) ⟹
		 (fun_allocglobal s gt v_val var_0) ⟹
		 (wf_state z') ⟹
		 (wf_store (fst var_0)) ⟹
		 (wf_state (fst var_1)) ⟹
		 list_all (λ (iter :: val). (wf_val iter)) (snd var_1) ⟹
		 (wf_state (mk_state s f)) ⟹
		 (wf_state (mk_state s' (f ⦇ MODULE := (MODULE f ⦇ moduleinst_GLOBALS := ((moduleinst_GLOBALS (MODULE f)) @ [a])  ⦈)  ⦈))) ⟹
		 (Eval_expr z v_expr z' [v_val]) ⟹
		 (z' = (mk_state s f)) ⟹
		 ((s', a) = var_0) ⟹
		 ((z'', val'_lst) = var_1) ⟹
		 fun_evalglobals z ([gt] @ gt'_lst) ([v_expr] @ expr'_lst) (z'', ([v_val] @ val'_lst))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:183.6-183.18 *)
inductive fun_instantiate :: "store ⇒ module ⇒ (externaddr list) ⇒ config ⇒ bool" where
	  fun_instantiate_case_0 :
		"(fun_funcsxa externaddr_lst var_8) ⟹
		 (fun_globalsxa externaddr_lst var_7) ⟹
		 (fun_alloctypes type_lst var_6) ⟹
		 (i_E < (length elem_lst)) ⟹
		 (fun_runelem_underscore (mk_uN i_E) (elem_lst ! i_E) var_5) ⟹
		 (i_D < (length data_lst)) ⟹
		 (fun_rundata_underscore (mk_uN i_D) (data_lst ! i_D) var_4) ⟹
		 (fun_allocmodule s''' v_module externaddr_lst val_G_lst ref_T_lst ref_E_lst_lst var_3) ⟹
		 (fun_evalexprss z'' expr_E_lst_lst var_2) ⟹
		 (fun_evalexprs z' expr_T_lst var_1) ⟹
		 (fun_evalglobals z globaltype_lst expr_G_lst var_0) ⟹
		 (wf_state z) ⟹
		 (wf_state z') ⟹
		 list_all (λ (val_G :: val). (wf_val val_G)) val_G_lst ⟹
		 (wf_state z'') ⟹
		 list_all (λ (ref_T :: ref). (wf_ref ref_T)) ref_T_lst ⟹
		 (wf_state z''') ⟹
		 list_all (λ (ref_E_lst :: (ref list)). list_all (λ (ref_E :: ref). (wf_ref ref_E)) ref_E_lst) ref_E_lst_lst ⟹
		 (wf_state (fst var_0)) ⟹
		 list_all (λ (iter :: val). (wf_val iter)) (snd var_0) ⟹
		 (wf_state (fst var_1)) ⟹
		 list_all (λ (iter :: ref). (wf_ref iter)) (snd var_1) ⟹
		 (wf_state (fst var_2)) ⟹
		 list_all (λ (iter :: (ref list)). list_all (λ (iter :: ref). (wf_ref iter)) iter) (snd var_2) ⟹
		 (wf_store (fst var_3)) ⟹
		 (wf_moduleinst (snd var_3)) ⟹
		 list_all (λ (iter :: instr). (wf_instr iter)) (concat_underscore  (mkseq (λ i_D. var_4) (length data_lst))) ⟹
		 list_all (λ (iter :: instr). (wf_instr iter)) var_4 ⟹
		 list_all (λ (iter :: instr). (wf_instr iter)) (concat_underscore  (mkseq (λ i_E. var_5) (length elem_lst))) ⟹
		 list_all (λ (iter :: instr). (wf_instr iter)) var_5 ⟹
		 (wf_moduletype (mk_moduletype xt_I_lst xt_E_lst)) ⟹
		 (wf_module (module_MODULE type_lst import_lst tag_lst global_lst mem_lst table_lst func_lst data_lst elem_lst start_opt export_lst)) ⟹
		 ((length expr_G_lst) = (length globaltype_lst)) ⟹
		 list_all2 (λ (expr_G :: expr) (v_globaltype :: globaltype). (wf_global (global_GLOBAL v_globaltype expr_G))) expr_G_lst globaltype_lst ⟹
		 ((length expr_T_lst) = (length tabletype_lst)) ⟹
		 list_all2 (λ (expr_T :: expr) (v_tabletype :: tabletype). (wf_table (table_TABLE v_tabletype expr_T))) expr_T_lst tabletype_lst ⟹
		 ((length byte_lst_lst) = (length datamode_lst)) ⟹
		 list_all2 (λ (byte_lst :: (byte list)) (v_datamode :: datamode). (wf_data (DATA byte_lst v_datamode))) byte_lst_lst datamode_lst ⟹
		 ((length elemmode_lst) = (length expr_E_lst_lst)) ⟹
		 ((length elemmode_lst) = (length reftype_lst)) ⟹
		 list_all3 (λ (v_elemmode :: elemmode) (expr_E_lst :: (expr list)) (v_reftype :: reftype). (wf_elem (ELEM v_reftype expr_E_lst v_elemmode))) elemmode_lst expr_E_lst_lst reftype_lst ⟹
		 list_all (λ (x :: idx). (wf_start (START x))) (option_to_list x_opt) ⟹
		 (wf_moduleinst ⦇ moduleinst_TYPES = var_6, moduleinst_TAGS = [], moduleinst_GLOBALS = var_7, moduleinst_MEMS = [], moduleinst_TABLES = [], moduleinst_FUNCS = (var_8 @ (mkseq (λ i_F. ((length (store_FUNCS s)) + i_F)) (length func_lst))), moduleinst_DATAS = [], moduleinst_ELEMS = [], EXPORTS = [] ⦈) ⟹
		 (wf_state (mk_state s ⦇ frame_LOCALS = [], MODULE = moduleinst_0 ⦈)) ⟹
		 (wf_state (mk_state s''' f)) ⟹
		 (wf_uN 32 (mk_uN i_D)) ⟹
		 (wf_uN 32 (mk_uN i_E)) ⟹
		 list_all (λ (x :: idx). (wf_instr (instr_sc1 (CALL x)))) (option_to_list x_opt) ⟹
		 (Module_ok v_module (mk_moduletype xt_I_lst xt_E_lst)) ⟹
		 ((length externaddr_lst) = (length xt_I_lst)) ⟹
		 list_all2 (λ (v_externaddr :: externaddr) (xt_I :: externtype). (Externaddr_ok s v_externaddr xt_I)) externaddr_lst xt_I_lst ⟹
		 (v_module = (module_MODULE type_lst import_lst tag_lst global_lst mem_lst table_lst func_lst data_lst elem_lst start_opt export_lst)) ⟹
		 (global_lst = (list_zipWith (λ (expr_G :: expr) (v_globaltype :: globaltype). (global_GLOBAL v_globaltype expr_G)) expr_G_lst globaltype_lst)) ⟹
		 (table_lst = (list_zipWith (λ (expr_T :: expr) (v_tabletype :: tabletype). (table_TABLE v_tabletype expr_T)) expr_T_lst tabletype_lst)) ⟹
		 (data_lst = (list_zipWith (λ (byte_lst :: (byte list)) (v_datamode :: datamode). (DATA byte_lst v_datamode)) byte_lst_lst datamode_lst)) ⟹
		 (elem_lst = (list_map3 (λ (v_elemmode :: elemmode) (expr_E_lst :: (expr list)) (v_reftype :: reftype). (ELEM v_reftype expr_E_lst v_elemmode)) elemmode_lst expr_E_lst_lst reftype_lst)) ⟹
		 (start_opt = (map_option (λ (x :: idx). (START x)) x_opt)) ⟹
		 (moduleinst_0 = ⦇ moduleinst_TYPES = var_6, moduleinst_TAGS = [], moduleinst_GLOBALS = var_7, moduleinst_MEMS = [], moduleinst_TABLES = [], moduleinst_FUNCS = (var_8 @ (mkseq (λ i_F. ((length (store_FUNCS s)) + i_F)) (length func_lst))), moduleinst_DATAS = [], moduleinst_ELEMS = [], EXPORTS = [] ⦈) ⟹
		 (z = (mk_state s ⦇ frame_LOCALS = [], MODULE = moduleinst_0 ⦈)) ⟹
		 ((z', val_G_lst) = var_0) ⟹
		 ((z'', ref_T_lst) = var_1) ⟹
		 ((z''', ref_E_lst_lst) = var_2) ⟹
		 (z''' = (mk_state s''' f)) ⟹
		 ((s'''', v_moduleinst) = var_3) ⟹
		 (instr_D_lst = (concat_underscore  (mkseq (λ i_D. var_4) (length data_lst)))) ⟹
		 (instr_E_lst = (concat_underscore  (mkseq (λ i_E. var_5) (length elem_lst)))) ⟹
		 (instr_S_opt = (map_option (λ (x :: idx). (instr_sc1 (CALL x))) x_opt)) ⟹
		 fun_instantiate s v_module externaddr_lst (mk_config (mk_state s'''' ⦇ frame_LOCALS = [], MODULE = v_moduleinst ⦈) (instr_E_lst @ (instr_D_lst @ (option_to_list instr_S_opt))))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:214.6-214.13 *)
inductive fun_invoke :: "store ⇒ funcaddr ⇒ (val list) ⇒ config ⇒ bool" where
	  fun_invoke_case_0 :
		"(v_funcaddr < (length (store_FUNCS s))) ⟹
		 (wf_comptype (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (Expand (funcinst_TYPE ((store_FUNCS s) ! v_funcaddr)) (comptype_FUNC (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 ((length t_1_lst) = (length val_lst)) ⟹
		 list_all2 (λ (t_1 :: valtype) (v_val :: val). (Val_ok s v_val t_1)) t_1_lst val_lst ⟹
		 fun_invoke s v_funcaddr val_lst (mk_config (mk_state s ⦇ frame_LOCALS = [], MODULE = ⦇ moduleinst_TYPES = [], moduleinst_TAGS = [], moduleinst_GLOBALS = [], moduleinst_MEMS = [], moduleinst_TABLES = [], moduleinst_FUNCS = [], moduleinst_DATAS = [], moduleinst_ELEMS = [], EXPORTS = [] ⦈ ⦈) ((map (λ (v_val :: val). (instr_val v_val)) val_lst) @ [(instr_sc9 (instr_st9_REF_FUNC_ADDR v_funcaddr)), (instr_sc1 (CALL_REF (typeuse_deftype (funcinst_TYPE ((store_FUNCS s) ! v_funcaddr)))))]))"

(* Type Alias Definition at: ../specification/wasm-3.0/5.3-binary.instructions.spectec:18.1-18.31 *)
type_synonym castop = "((null option) * (null option))"

(* Type Alias Definition at: ../specification/wasm-3.0/5.3-binary.instructions.spectec:98.1-98.35 *)
type_synonym memidxop = "(memidx * memarg)"

(* Type Alias Definition at: ../specification/wasm-3.0/5.4-binary.modules.spectec:89.1-89.43 *)
type_synonym startopt = "(start list)"

(* Type Alias Definition at: ../specification/wasm-3.0/5.4-binary.modules.spectec:124.1-124.46 *)
type_synonym code = "((local list) * expr)"

(* Type Alias Definition at: ../specification/wasm-3.0/5.4-binary.modules.spectec:156.1-156.33 *)
type_synonym nopt = "(u32 list)"

(* Axiom Definition at: ../specification/wasm-3.0/6.1-text.values.spectec:55.1-55.30 *)
axiomatization ieee_underscore :: "N ⇒ nat ⇒ fNmag"

(* Record Creation Definition at: ../specification/wasm-3.0/6.1-text.values.spectec:137.1-150.4 *)
record idctxt =
	idctxt_TYPES :: "((name option) list)"
	idctxt_TAGS :: "((name option) list)"
	idctxt_GLOBALS :: "((name option) list)"
	idctxt_MEMS :: "((name option) list)"
	idctxt_TABLES :: "((name option) list)"
	idctxt_FUNCS :: "((name option) list)"
	idctxt_DATAS :: "((name option) list)"
	idctxt_ELEMS :: "((name option) list)"
	idctxt_LOCALS :: "((name option) list)"
	idctxt_LABELS :: "((name option) list)"
	idctxt_FIELDS :: "(((name option) list) list)"
	TYPEDEFS :: "((deftype option) list)"

definition append_idctxt :: "idctxt ⇒ idctxt ⇒ idctxt" where
	"append_idctxt arg1 arg2 = ⦇
		idctxt_TYPES = idctxt_TYPES arg1 @ idctxt_TYPES arg2,
		idctxt_TAGS = idctxt_TAGS arg1 @ idctxt_TAGS arg2,
		idctxt_GLOBALS = idctxt_GLOBALS arg1 @ idctxt_GLOBALS arg2,
		idctxt_MEMS = idctxt_MEMS arg1 @ idctxt_MEMS arg2,
		idctxt_TABLES = idctxt_TABLES arg1 @ idctxt_TABLES arg2,
		idctxt_FUNCS = idctxt_FUNCS arg1 @ idctxt_FUNCS arg2,
		idctxt_DATAS = idctxt_DATAS arg1 @ idctxt_DATAS arg2,
		idctxt_ELEMS = idctxt_ELEMS arg1 @ idctxt_ELEMS arg2,
		idctxt_LOCALS = idctxt_LOCALS arg1 @ idctxt_LOCALS arg2,
		idctxt_LABELS = idctxt_LABELS arg1 @ idctxt_LABELS arg2,
		idctxt_FIELDS = idctxt_FIELDS arg1 @ idctxt_FIELDS arg2,
		TYPEDEFS = TYPEDEFS arg1 @ TYPEDEFS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-3.0/6.1-text.values.spectec:137.8-137.14 *)
inductive wf_idctxt :: "idctxt ⇒ bool" where
	  idctxt_case_underscore :
		"list_all (λ (var_0 :: (name option)). list_all (λ (var_0 :: name). (wf_name var_0)) (option_to_list var_0)) var_0 ⟹
		 list_all (λ (var_1 :: (name option)). list_all (λ (var_1 :: name). (wf_name var_1)) (option_to_list var_1)) var_1 ⟹
		 list_all (λ (var_2 :: (name option)). list_all (λ (var_2 :: name). (wf_name var_2)) (option_to_list var_2)) var_2 ⟹
		 list_all (λ (var_3 :: (name option)). list_all (λ (var_3 :: name). (wf_name var_3)) (option_to_list var_3)) var_3 ⟹
		 list_all (λ (var_4 :: (name option)). list_all (λ (var_4 :: name). (wf_name var_4)) (option_to_list var_4)) var_4 ⟹
		 list_all (λ (var_5 :: (name option)). list_all (λ (var_5 :: name). (wf_name var_5)) (option_to_list var_5)) var_5 ⟹
		 list_all (λ (var_6 :: (name option)). list_all (λ (var_6 :: name). (wf_name var_6)) (option_to_list var_6)) var_6 ⟹
		 list_all (λ (var_7 :: (name option)). list_all (λ (var_7 :: name). (wf_name var_7)) (option_to_list var_7)) var_7 ⟹
		 list_all (λ (var_8 :: (name option)). list_all (λ (var_8 :: name). (wf_name var_8)) (option_to_list var_8)) var_8 ⟹
		 list_all (λ (var_9 :: (name option)). list_all (λ (var_9 :: name). (wf_name var_9)) (option_to_list var_9)) var_9 ⟹
		 list_all (λ (var_10 :: ((name option) list)). list_all (λ (var_10 :: (name option)). list_all (λ (var_10 :: name). (wf_name var_10)) (option_to_list var_10)) var_10) var_10 ⟹
		 wf_idctxt ⦇ idctxt_TYPES = var_0, idctxt_TAGS = var_1, idctxt_GLOBALS = var_2, idctxt_MEMS = var_3, idctxt_TABLES = var_4, idctxt_FUNCS = var_5, idctxt_DATAS = var_6, idctxt_ELEMS = var_7, idctxt_LOCALS = var_8, idctxt_LABELS = var_9, idctxt_FIELDS = var_10, TYPEDEFS = var_11 ⦈"

(* Type Alias Definition at: ../specification/wasm-3.0/6.1-text.values.spectec:152.1-152.18 *)
type_synonym I = "idctxt"

(* Mutual Recursion at: ../specification/wasm-3.0/6.1-text.values.spectec:154.1-154.56 *)
inductive fun_concat_idctxt :: "(idctxt list) ⇒ idctxt ⇒ bool" where
	  fun_concat_idctxt_case_0 :
		"fun_concat_idctxt [] ⦇ idctxt_TYPES = [], idctxt_TAGS = [], idctxt_GLOBALS = [], idctxt_MEMS = [], idctxt_TABLES = [], idctxt_FUNCS = [], idctxt_DATAS = [], idctxt_ELEMS = [], idctxt_LOCALS = [], idctxt_LABELS = [], idctxt_FIELDS = [], TYPEDEFS = [] ⦈"
	| fun_concat_idctxt_case_1 :
		"(fun_concat_idctxt I'_lst var_0) ⟹
		 fun_concat_idctxt ([v_I] @ I'_lst) (append_idctxt v_I var_0)"

(* Inductive Relations Definition at: ../specification/wasm-3.0/6.1-text.values.spectec:159.1-159.35 *)
inductive Idctxt_ok :: "idctxt ⇒ bool" where
	  mk_Idctxt_ok :
		"list_all (λ (iter :: name). (wf_name iter)) (concatopt_underscore  (idctxt_TYPES v_I)) ⟹
		 list_all (λ (iter :: name). (wf_name iter)) (concatopt_underscore  (idctxt_TAGS v_I)) ⟹
		 list_all (λ (iter :: name). (wf_name iter)) (concatopt_underscore  (idctxt_GLOBALS v_I)) ⟹
		 list_all (λ (iter :: name). (wf_name iter)) (concatopt_underscore  (idctxt_MEMS v_I)) ⟹
		 list_all (λ (iter :: name). (wf_name iter)) (concatopt_underscore  (idctxt_TABLES v_I)) ⟹
		 list_all (λ (iter :: name). (wf_name iter)) (concatopt_underscore  (idctxt_FUNCS v_I)) ⟹
		 list_all (λ (iter :: name). (wf_name iter)) (concatopt_underscore  (idctxt_DATAS v_I)) ⟹
		 list_all (λ (iter :: name). (wf_name iter)) (concatopt_underscore  (idctxt_ELEMS v_I)) ⟹
		 list_all (λ (iter :: name). (wf_name iter)) (concatopt_underscore  (idctxt_LOCALS v_I)) ⟹
		 list_all (λ (iter :: name). (wf_name iter)) (concatopt_underscore  (idctxt_LABELS v_I)) ⟹
		 list_all (λ (field_lst :: (res_char list)). list_all (λ (iter :: name). (wf_name iter)) (concatopt_underscore  [(Some (mk_name field_lst))])) field_lst_lst ⟹
		 list_all (λ (field_lst :: (res_char list)). (wf_name (mk_name field_lst))) field_lst_lst ⟹
		 (disjoint_underscore  (concatopt_underscore  (idctxt_TYPES v_I))) ⟹
		 (disjoint_underscore  (concatopt_underscore  (idctxt_TAGS v_I))) ⟹
		 (disjoint_underscore  (concatopt_underscore  (idctxt_GLOBALS v_I))) ⟹
		 (disjoint_underscore  (concatopt_underscore  (idctxt_MEMS v_I))) ⟹
		 (disjoint_underscore  (concatopt_underscore  (idctxt_TABLES v_I))) ⟹
		 (disjoint_underscore  (concatopt_underscore  (idctxt_FUNCS v_I))) ⟹
		 (disjoint_underscore  (concatopt_underscore  (idctxt_DATAS v_I))) ⟹
		 (disjoint_underscore  (concatopt_underscore  (idctxt_ELEMS v_I))) ⟹
		 (disjoint_underscore  (concatopt_underscore  (idctxt_LOCALS v_I))) ⟹
		 (disjoint_underscore  (concatopt_underscore  (idctxt_LABELS v_I))) ⟹
		 list_all (λ (field_lst :: (res_char list)). (disjoint_underscore  (concatopt_underscore  [(Some (mk_name field_lst))]))) field_lst_lst ⟹
		 ([(map (λ (field_lst :: (res_char list)). (Some (mk_name field_lst))) field_lst_lst)] = (idctxt_FIELDS v_I)) ⟹
		 Idctxt_ok v_I"

(* Axiom Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:170.1-170.31 *)
axiomatization dots :: "unit"

(* Inductive Type Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:255.1-256.83 *)
datatype decl =
	  decl_TYPE "rectype"
	| decl_IMPORT "name" "name" "externtype"
	| decl_TAG "tagtype"
	| decl_GLOBAL "globaltype" "expr"
	| decl_MEMORY "memtype"
	| decl_TABLE "tabletype" "expr"
	| decl_FUNC "typeidx" "(local list)" "expr"
	| decl_DATA "(byte list)" "datamode"
	| decl_ELEM "reftype" "(expr list)" "elemmode"
	| decl_START "funcidx"
	| decl_EXPORT "name" "externidx"

(* Auxiliary Definition at:  *)
function (sequential) decl_data :: "data ⇒ decl" where
		  "decl_data (DATA x0 x1) = (decl_DATA x0 x1)"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) decl_elem :: "elem ⇒ decl" where
		  "decl_elem (ELEM x0 x1 x2) = (decl_ELEM x0 x1 x2)"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) decl_export :: "export ⇒ decl" where
		  "decl_export (EXPORT x0 x1) = (decl_EXPORT x0 x1)"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) decl_func :: "func ⇒ decl" where
		  "decl_func (func_FUNC x0 x1 x2) = (decl_FUNC x0 x1 x2)"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) decl_global :: "global ⇒ decl" where
		  "decl_global (global_GLOBAL x0 x1) = (decl_GLOBAL x0 x1)"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) decl_import :: "import ⇒ decl" where
		  "decl_import (IMPORT x0 x1 x2) = (decl_IMPORT x0 x1 x2)"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) decl_mem :: "mem ⇒ decl" where
		  "decl_mem (MEMORY x0) = (decl_MEMORY x0)"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) decl_start :: "start ⇒ decl" where
		  "decl_start (START x0) = (decl_START x0)"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) decl_table :: "table ⇒ decl" where
		  "decl_table (table_TABLE x0 x1) = (decl_TABLE x0 x1)"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) decl_tag :: "tag ⇒ decl" where
		  "decl_tag (tag_TAG x0) = (decl_TAG x0)"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) decl_type :: "type ⇒ decl" where
		  "decl_type (res_TYPE x0) = (decl_TYPE x0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:255.8-255.12 *)
inductive wf_decl :: "decl ⇒ bool" where
	  decl_case_0 :
		"wf_decl (decl_TYPE v_rectype)"
	| decl_case_1 :
		"(wf_name v_name) ⟹
		 (wf_name name_0) ⟹
		 (wf_externtype v_externtype) ⟹
		 wf_decl (decl_IMPORT v_name name_0 v_externtype)"
	| decl_case_2 :
		"(wf_typeuse v_tagtype) ⟹
		 wf_decl (decl_TAG v_tagtype)"
	| decl_case_3 :
		"(wf_globaltype v_globaltype) ⟹
		 list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_decl (decl_GLOBAL v_globaltype v_expr)"
	| decl_case_4 :
		"(wf_memtype v_memtype) ⟹
		 wf_decl (decl_MEMORY v_memtype)"
	| decl_case_5 :
		"(wf_tabletype v_tabletype) ⟹
		 list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_decl (decl_TABLE v_tabletype v_expr)"
	| decl_case_6 :
		"(wf_uN 32 v_typeidx) ⟹
		 list_all (λ (v_local :: local). (wf_local v_local)) local_lst ⟹
		 list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_decl (decl_FUNC v_typeidx local_lst v_expr)"
	| decl_case_7 :
		"list_all (λ (v_byte :: byte). (wf_byte v_byte)) byte_lst ⟹
		 (wf_datamode v_datamode) ⟹
		 wf_decl (decl_DATA byte_lst v_datamode)"
	| decl_case_8 :
		"(wf_reftype v_reftype) ⟹
		 list_all (λ (v_expr :: expr). list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr) expr_lst ⟹
		 (wf_elemmode v_elemmode) ⟹
		 wf_decl (decl_ELEM v_reftype expr_lst v_elemmode)"
	| decl_case_9 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_decl (decl_START v_funcidx)"
	| decl_case_10 :
		"(wf_name v_name) ⟹
		 (wf_externidx v_externidx) ⟹
		 wf_decl (decl_EXPORT v_name v_externidx)"

(* Mutual Recursion at: ../specification/wasm-3.0/6.4-text.modules.spectec:258.1-258.76 *)
inductive fun_typesd :: "(decl list) ⇒ (type list) ⇒ bool" where
	  fun_typesd_case_0 :
		"fun_typesd [] []"
	| fun_typesd_case_1 :
		"(fun_typesd decl'_lst var_0) ⟹
		 fun_typesd ([(decl_TYPE v_rectype)] @ decl'_lst) ([(res_TYPE v_rectype)] @ var_0)"
	| fun_typesd_case_2 :
		"(fun_typesd decl'_lst var_0) ⟹
		 fun_typesd ([v_decl] @ decl'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/6.4-text.modules.spectec:259.1-259.78 *)
inductive fun_importsd :: "(decl list) ⇒ (import list) ⇒ bool" where
	  fun_importsd_case_0 :
		"fun_importsd [] []"
	| fun_importsd_case_1 :
		"(fun_importsd decl'_lst var_0) ⟹
		 fun_importsd ([(decl_IMPORT v_name name_0 v_externtype)] @ decl'_lst) ([(IMPORT v_name name_0 v_externtype)] @ var_0)"
	| fun_importsd_case_2 :
		"(fun_importsd decl'_lst var_0) ⟹
		 fun_importsd ([v_decl] @ decl'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/6.4-text.modules.spectec:260.1-260.75 *)
inductive fun_tagsd :: "(decl list) ⇒ (tag list) ⇒ bool" where
	  fun_tagsd_case_0 :
		"fun_tagsd [] []"
	| fun_tagsd_case_1 :
		"(fun_tagsd decl'_lst var_0) ⟹
		 fun_tagsd ([(decl_TAG v_tagtype)] @ decl'_lst) ([(tag_TAG v_tagtype)] @ var_0)"
	| fun_tagsd_case_2 :
		"(fun_tagsd decl'_lst var_0) ⟹
		 fun_tagsd ([v_decl] @ decl'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/6.4-text.modules.spectec:261.1-261.78 *)
inductive fun_globalsd :: "(decl list) ⇒ (global list) ⇒ bool" where
	  fun_globalsd_case_0 :
		"fun_globalsd [] []"
	| fun_globalsd_case_1 :
		"(fun_globalsd decl'_lst var_0) ⟹
		 fun_globalsd ([(decl_GLOBAL v_globaltype v_expr)] @ decl'_lst) ([(global_GLOBAL v_globaltype v_expr)] @ var_0)"
	| fun_globalsd_case_2 :
		"(fun_globalsd decl'_lst var_0) ⟹
		 fun_globalsd ([v_decl] @ decl'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/6.4-text.modules.spectec:262.1-262.75 *)
inductive fun_memsd :: "(decl list) ⇒ (mem list) ⇒ bool" where
	  fun_memsd_case_0 :
		"fun_memsd [] []"
	| fun_memsd_case_1 :
		"(fun_memsd decl'_lst var_0) ⟹
		 fun_memsd ([(decl_MEMORY v_memtype)] @ decl'_lst) ([(MEMORY v_memtype)] @ var_0)"
	| fun_memsd_case_2 :
		"(fun_memsd decl'_lst var_0) ⟹
		 fun_memsd ([v_decl] @ decl'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/6.4-text.modules.spectec:263.1-263.77 *)
inductive fun_tablesd :: "(decl list) ⇒ (table list) ⇒ bool" where
	  fun_tablesd_case_0 :
		"fun_tablesd [] []"
	| fun_tablesd_case_1 :
		"(fun_tablesd decl'_lst var_0) ⟹
		 fun_tablesd ([(decl_TABLE v_tabletype v_expr)] @ decl'_lst) ([(table_TABLE v_tabletype v_expr)] @ var_0)"
	| fun_tablesd_case_2 :
		"(fun_tablesd decl'_lst var_0) ⟹
		 fun_tablesd ([v_decl] @ decl'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/6.4-text.modules.spectec:264.1-264.76 *)
inductive fun_funcsd :: "(decl list) ⇒ (func list) ⇒ bool" where
	  fun_funcsd_case_0 :
		"fun_funcsd [] []"
	| fun_funcsd_case_1 :
		"(fun_funcsd decl'_lst var_0) ⟹
		 fun_funcsd ([(decl_FUNC v_typeidx local_lst v_expr)] @ decl'_lst) ([(func_FUNC v_typeidx local_lst v_expr)] @ var_0)"
	| fun_funcsd_case_2 :
		"(fun_funcsd decl'_lst var_0) ⟹
		 fun_funcsd ([v_decl] @ decl'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/6.4-text.modules.spectec:265.1-265.76 *)
inductive fun_datasd :: "(decl list) ⇒ (data list) ⇒ bool" where
	  fun_datasd_case_0 :
		"fun_datasd [] []"
	| fun_datasd_case_1 :
		"(fun_datasd decl'_lst var_0) ⟹
		 fun_datasd ([(decl_DATA byte_lst v_datamode)] @ decl'_lst) ([(DATA byte_lst v_datamode)] @ var_0)"
	| fun_datasd_case_2 :
		"(fun_datasd decl'_lst var_0) ⟹
		 fun_datasd ([v_decl] @ decl'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/6.4-text.modules.spectec:266.1-266.76 *)
inductive fun_elemsd :: "(decl list) ⇒ (elem list) ⇒ bool" where
	  fun_elemsd_case_0 :
		"fun_elemsd [] []"
	| fun_elemsd_case_1 :
		"(fun_elemsd decl'_lst var_0) ⟹
		 fun_elemsd ([(decl_ELEM v_reftype expr_lst v_elemmode)] @ decl'_lst) ([(ELEM v_reftype expr_lst v_elemmode)] @ var_0)"
	| fun_elemsd_case_2 :
		"(fun_elemsd decl'_lst var_0) ⟹
		 fun_elemsd ([v_decl] @ decl'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/6.4-text.modules.spectec:267.1-267.77 *)
inductive fun_startsd :: "(decl list) ⇒ (start list) ⇒ bool" where
	  fun_startsd_case_0 :
		"fun_startsd [] []"
	| fun_startsd_case_1 :
		"(fun_startsd decl'_lst var_0) ⟹
		 fun_startsd ([(decl_START v_funcidx)] @ decl'_lst) ([(START v_funcidx)] @ var_0)"
	| fun_startsd_case_2 :
		"(fun_startsd decl'_lst var_0) ⟹
		 fun_startsd ([v_decl] @ decl'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-3.0/6.4-text.modules.spectec:268.1-268.78 *)
inductive fun_exportsd :: "(decl list) ⇒ (export list) ⇒ bool" where
	  fun_exportsd_case_0 :
		"fun_exportsd [] []"
	| fun_exportsd_case_1 :
		"(fun_exportsd decl'_lst var_0) ⟹
		 fun_exportsd ([(decl_EXPORT v_name v_externidx)] @ decl'_lst) ([(EXPORT v_name v_externidx)] @ var_0)"
	| fun_exportsd_case_2 :
		"(fun_exportsd decl'_lst var_0) ⟹
		 fun_exportsd ([v_decl] @ decl'_lst) var_0"

(* Inductive Relations Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:314.6-314.14 *)
inductive fun_ordered :: "(decl list) ⇒ bool ⇒ bool" where
	  fun_ordered_case_0 :
		"(fun_importsd decl_lst var_0) ⟹
		 list_all (λ (iter :: import). (wf_import iter)) var_0 ⟹
		 (var_0 = []) ⟹
		 fun_ordered decl_lst True"
	| fun_ordered_case_1 :
		"(fun_funcsd decl_1_lst var_5) ⟹
		 (fun_tablesd decl_1_lst var_4) ⟹
		 (fun_memsd decl_1_lst var_3) ⟹
		 (fun_globalsd decl_1_lst var_2) ⟹
		 (fun_tagsd decl_1_lst var_1) ⟹
		 (fun_importsd decl_1_lst var_0) ⟹
		 fun_ordered (decl_1_lst @ ([(decl_IMPORT v_name name_0 v_externtype)] @ decl_2_lst)) ((((((var_0 = []) ∧ (var_1 = [])) ∧ (var_2 = [])) ∧ (var_3 = [])) ∧ (var_4 = [])) ∧ (var_5 = []))"

(* Type Alias Definition at: ../specification/wasm-3.0/X.1-notation.syntax.spectec:7.1-7.32 *)
type_synonym A = "nat"

(* Type Alias Definition at: ../specification/wasm-3.0/X.1-notation.syntax.spectec:8.1-8.32 *)
type_synonym B = "nat"

(* Inductive Type Definition at: ../specification/wasm-3.0/X.1-notation.syntax.spectec:10.1-10.77 *)
datatype sym =
	  underscore_FIRST "A"
	| underscore_DOTS
	| underscore_LAST "A"

(* Inductive Type Definition at: ../specification/wasm-3.0/X.1-notation.syntax.spectec:12.1-12.68 *)
datatype symsplit =
	  symsplit__FIRST "A"
	| symsplit__LAST "A"

(* Type Alias Definition at: ../specification/wasm-3.0/X.1-notation.syntax.spectec:14.1-14.37 *)
type_synonym recorddots = "unit"

(* Record Creation Definition at: ../specification/wasm-3.0/X.1-notation.syntax.spectec:15.1-18.22 *)
record res_record =
	FIELD_1 :: "A"
	FIELD_2 :: "A"
	mk_record :: "recorddots"

definition append_res_record :: "res_record ⇒ res_record ⇒ res_record" where
	"append_res_record arg1 arg2 = ⦇
		FIELD_1 = FIELD_1 arg1,
		FIELD_2 = FIELD_2 arg1,
		mk_record = mk_record arg1
	⦈"



(* Inductive Type Definition at: ../specification/wasm-3.0/X.1-notation.syntax.spectec:20.1-20.71 *)
datatype pth =
	  PTHSYNTAX
	

(* Type Alias Definition at: ../specification/wasm-3.0/X.2-notation.typing.spectec:7.1-7.32 *)
type_synonym T = "nat"

(* Inductive Relations Definition at: ../specification/wasm-3.0/X.2-notation.typing.spectec:9.1-9.36 *)
axiomatization NotationTypingPremise :: "nat ⇒ bool"

(* Inductive Relations Definition at: ../specification/wasm-3.0/X.2-notation.typing.spectec:10.1-10.58 *)
axiomatization NotationTypingPremisedots :: "bool"

(* Inductive Relations Definition at: ../specification/wasm-3.0/X.2-notation.typing.spectec:11.1-11.35 *)
inductive NotationTypingScheme :: "nat ⇒ bool" where
	  mk_NotationTypingScheme :
		"(NotationTypingPremise premise_1) ⟹
		 (NotationTypingPremise premise_2) ⟹
		 (NotationTypingPremisedots) ⟹
		 (NotationTypingPremise premise_n) ⟹
		 NotationTypingScheme conclusion"

(* Mutual Recursion at: ../specification/wasm-3.0/X.2-notation.typing.spectec:20.1-20.83 *)
inductive NotationTypingInstrScheme :: "res_context ⇒ (instr list) ⇒ instrtype ⇒ bool" where
	  i32_add :
		"NotationTypingInstrScheme C [(instr_sc6 (BINOP numtype_I32 (mk_binop__0 I32 ADD)))] (mk_instrtype (mk_list [valtype_I32, valtype_I32]) [] (mk_list [valtype_I32]))"
	| NotationTypingInstrScheme__global_get :
		"(wf_globaltype (mk_globaltype (Some v_mut) t)) ⟹
		 ((proj_uN_0 x) < (length (context_GLOBALS C))) ⟹
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype (Some v_mut) t)) ⟹
		 NotationTypingInstrScheme C [(instr_sc2 (GLOBAL_GET x))] (mk_instrtype (mk_list []) [] (mk_list [t]))"
	| NotationTypingInstrScheme__block :
		"(wf_instrtype (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (wf_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [(mk_list t_2_lst)], context_RETURN = None, REFS = [] ⦈) ⟹
		 (Blocktype_ok C v_blocktype (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 (NotationTypingInstrScheme (append_context ⦇ context_TYPES = [], RECS = [], context_TAGS = [], context_GLOBALS = [], context_MEMS = [], context_TABLES = [], context_FUNCS = [], context_DATAS = [], context_ELEMS = [], context_LOCALS = [], context_LABELS = [(mk_list t_2_lst)], context_RETURN = None, REFS = [] ⦈ C) instr_lst (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))) ⟹
		 NotationTypingInstrScheme C [(instr_sc9 (BLOCK v_blocktype instr_lst))] (mk_instrtype (mk_list t_1_lst) [] (mk_list t_2_lst))"

(* Inductive Relations Definition at: ../specification/wasm-3.0/X.3-notation.execution.spectec:7.1-7.49 *)
inductive NotationReduct :: "(instr list) ⇒ bool" where
	  r_2 :
		"NotationReduct [(instr_sc6 (instr_st6_CONST F64 q_1)), (instr_sc6 (instr_st6_CONST F64 q_4)), (instr_sc6 (instr_st6_CONST F64 q_3)), (instr_sc6 (BINOP F64 (mk_binop__1 Fnn_F64 binop_Fnn_ADD))), (instr_sc6 (BINOP F64 (mk_binop__1 Fnn_F64 binop_Fnn_MUL)))]"
	| r_3 :
		"NotationReduct [(instr_sc6 (instr_st6_CONST F64 q_1)), (instr_sc6 (instr_st6_CONST F64 q_5)), (instr_sc6 (BINOP F64 (mk_binop__1 Fnn_F64 binop_Fnn_MUL)))]"
	| r_4 :
		"NotationReduct [(instr_sc6 (instr_st6_CONST F64 q_6))]"

(* Axiom Definition at: ../specification/wasm-3.0/X.3-notation.execution.spectec:21.1-21.40 *)
axiomatization instrdots :: "(instr list)"

(* Inductive Type Definition at: ../specification/wasm-3.0/X.3-notation.execution.spectec:23.1-23.75 *)
datatype label =
	  label_LABEL_underscore "n" "(instr list)"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/X.3-notation.execution.spectec:23.8-23.13 *)
inductive wf_label :: "label ⇒ bool" where
	  label_case_0 :
		"list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_label (label_LABEL_underscore v_n instr_lst)"

(* Inductive Type Definition at: ../specification/wasm-3.0/X.3-notation.execution.spectec:24.1-24.84 *)
datatype callframe =
	  callframe_FRAME_underscore "n" "frame"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/X.3-notation.execution.spectec:24.8-24.17 *)
inductive wf_callframe :: "callframe ⇒ bool" where
	  callframe_case_0 :
		"(wf_frame v_frame) ⟹
		 wf_callframe (callframe_FRAME_underscore v_n v_frame)"

(* Axiom Definition at: ../specification/wasm-3.0/X.3-notation.execution.spectec:31.1-31.78 *)
axiomatization allocX :: "store ⇒ 'v_X ⇒ 'Y ⇒ (store * addr)"

(* Mutual Recursion at: ../specification/wasm-3.0/X.3-notation.execution.spectec:32.1-32.117 *)
axiomatization allocXs :: "store ⇒ ('v_X list) ⇒ ('Y list) ⇒ (store * (addr list))"

(* Inductive Type Definition at: ../specification/wasm-3.0/X.4-notation.binary.spectec:7.1-7.52 *)
datatype symdots =
	  mk_symdots "nat"
	

(* Inductive Relations Definition at: ../specification/wasm-3.0/X.4-notation.binary.spectec:7.8-7.15 *)
inductive wf_symdots :: "symdots ⇒ bool" where
	  symdots_case_0 :
		"(i = 0) ⟹
		 wf_symdots (mk_symdots i)"

(* Auxiliary Definition at: ../specification/wasm-3.0/X.4-notation.binary.spectec:9.1-9.55 *)
definition var :: "nat" where
	"var = 0"

(* Type Alias Definition at: ../specification/wasm-3.0/X.5-notation.text.spectec:19.1-19.41 *)
type_synonym abbreviated = "unit"

(* Type Alias Definition at: ../specification/wasm-3.0/X.5-notation.text.spectec:20.1-20.38 *)
type_synonym expanded = "unit"

(* Type Alias Definition at: ../specification/wasm-3.0/X.5-notation.text.spectec:21.1-21.37 *)
type_synonym res_syntax = "unit"

end
