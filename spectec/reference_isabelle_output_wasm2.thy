theory reference_isabelle_output_wasm2
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
(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:162.14-162.17 *)
datatype MUT =
	  MUT_MUT
	

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:7.1-7.15 *)
type_synonym N = "nat"

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:8.1-8.15 *)
type_synonym M = "nat"

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:9.1-9.15 *)
type_synonym n = "nat"

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:10.1-10.15 *)
type_synonym m = "nat"

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:15.1-15.14 *)
definition Ki :: "nat" where
	"Ki = 1024"

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:21.1-21.25 *)
function (sequential) min :: "nat ⇒ nat ⇒ nat" where
		  "min i j = (if (i ≤ j) then i else j)"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:25.1-25.21 *)
inductive fun_sum :: "(nat list) ⇒ nat ⇒ bool" where
	  fun_sum_case_0 :
		"fun_sum [] 0"
	| fun_sum_case_1 :
		"(fun_sum n'_lst var_0) ⟹
		 fun_sum ([v_n] @ n'_lst) (v_n + var_0)"

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:32.1-32.58 *)
function (sequential) opt_underscore :: "('X list) ⇒ (('X option) option)" where
		  "opt_underscore  [] = (Some None)"
		| "opt_underscore  [w] = (Some (Some w))"
		| "opt_underscore  x1 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:36.1-36.45 *)
function (sequential) list_underscore :: "('X option) ⇒ ('X list)" where
		  "list_underscore  None = []"
		| "list_underscore  (Some w) = [w]"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:40.1-40.86 *)
function (sequential) concat_underscore :: "(('X list) list) ⇒ ('X list)" where
		  "concat_underscore  [] = []"
		| "concat_underscore  (w_lst # w'_lst_lst) = (w_lst @ (concat_underscore  w'_lst_lst))"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-2.0/0-aux.spectec:44.1-44.39 *)
axiomatization inv_concat_underscore :: "('X list) ⇒ (('X list) list)"

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:51.1-51.46 *)
function (sequential) setproduct2_underscore :: "'X ⇒ (('X list) list) ⇒ (('X list) list)" where
		  "setproduct2_underscore  w_1 [] = []"
		| "setproduct2_underscore  w_1 (w'_lst # w_lst_lst) = ([([w_1] @ w'_lst)] @ (setproduct2_underscore  w_1 w_lst_lst))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:50.1-50.47 *)
function (sequential) setproduct1_underscore :: "('X list) ⇒ (('X list) list) ⇒ (('X list) list)" where
		  "setproduct1_underscore  [] w_lst_lst = []"
		| "setproduct1_underscore  (w_1 # w'_lst) w_lst_lst = ((setproduct2_underscore  w_1 w_lst_lst) @ (setproduct1_underscore  w'_lst w_lst_lst))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:49.1-49.84 *)
function (sequential) setproduct_underscore :: "(('X list) list) ⇒ (('X list) list)" where
		  "setproduct_underscore  [] = [[]]"
		| "setproduct_underscore  (w_1_lst # w_lst_lst) = (setproduct1_underscore  w_1_lst (setproduct_underscore  w_lst_lst))"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 *)
datatype 'X res_list  =
	  mk_list "('X list)"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 *)
function (sequential) proj_list_0 :: "('X res_list) ⇒ (('X list))" where
		  "proj_list_0  (mk_list v_X_list_0) = (v_X_list_0)"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:15.1-15.36 *)
datatype bit =
	  mk_bit "nat"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:15.8-15.11 *)
inductive wf_bit :: "bit ⇒ bool" where
	  bit_case_0 :
		"((i = 0) ∨ (i = 1)) ⟹
		 wf_bit (mk_bit i)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 *)
datatype byte =
	  mk_byte "nat"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 *)
function (sequential) proj_byte_0 :: "byte ⇒ (nat)" where
		  "proj_byte_0 (mk_byte v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.8-16.12 *)
inductive wf_byte :: "byte ⇒ bool" where
	  byte_case_0 :
		"((i ≥ 0) ∧ (i ≤ 255)) ⟹
		 wf_byte (mk_byte i)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 *)
datatype uN =
	  mk_uN "nat"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 *)
function (sequential) proj_uN_0 :: "uN ⇒ (nat)" where
		  "proj_uN_0 (mk_uN v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.8-18.11 *)
inductive wf_uN :: "N ⇒ uN ⇒ bool" where
	  uN_case_0 :
		"((i ≥ 0) ∧ (i ≤ ((((2 ^ v_N) :: nat) - (1 :: nat)) :: nat))) ⟹
		 wf_uN v_N (mk_uN i)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 *)
datatype sN =
	  mk_sN "nat"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 *)
function (sequential) proj_sN_0 :: "sN ⇒ (nat)" where
		  "proj_sN_0 (mk_sN v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.8-20.11 *)
inductive wf_sN :: "N ⇒ sN ⇒ bool" where
	  sN_case_0 :
		"((((i ≥ (0 - ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat))) ∧ (i ≤ (0 - (1 :: nat)))) ∨ (i = (0 :: nat))) ∨ ((i ≥ ((1 :: nat))) ∧ (i ≤ (((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat) - (1 :: nat))))) ⟹
		 wf_sN v_N (mk_sN i)"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:22.1-23.8 *)
type_synonym iN = "uN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:25.1-25.18 *)
type_synonym u8 = "uN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:26.1-26.20 *)
type_synonym u16 = "uN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:27.1-27.20 *)
type_synonym u31 = "uN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:28.1-28.20 *)
type_synonym u32 = "uN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:29.1-29.20 *)
type_synonym u64 = "uN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:30.1-30.20 *)
type_synonym s33 = "sN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:31.1-31.20 *)
type_synonym i32 = "iN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:32.1-32.20 *)
type_synonym i64 = "iN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:33.1-33.22 *)
type_synonym i128 = "iN"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:40.1-40.35 *)
function (sequential) signif :: "N ⇒ (nat option)" where
		  "signif (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some 23)"
		| "signif (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some 52)"
		| "signif x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:44.1-44.34 *)
function (sequential) expon :: "N ⇒ (nat option)" where
		  "expon (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some 8)"
		| "expon (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some 11)"
		| "expon x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:48.1-48.30 *)
function (sequential) fun_M :: "N ⇒ nat" where
		  "fun_M v_N = (the ((signif v_N)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:51.1-51.30 *)
function (sequential) E :: "N ⇒ nat" where
		  "E v_N = (the ((expon v_N)))"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:58.1-58.30 *)
type_synonym exp = "nat"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:59.1-63.84 *)
datatype fNmag =
	  NORM "m" "exp"
	| SUBNORM "m"
	| res_INF
	| NAN "m"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:59.8-59.14 *)
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

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:54.1-56.35 *)
datatype fN =
	  POS "fNmag"
	| NEG "fNmag"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:54.8-54.11 *)
inductive wf_fN :: "N ⇒ fN ⇒ bool" where
	  fN_case_0 :
		"(wf_fNmag v_N var_0) ⟹
		 wf_fN v_N (POS var_0)"
	| fN_case_1 :
		"(wf_fNmag v_N var_0) ⟹
		 wf_fN v_N (NEG var_0)"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:65.1-65.20 *)
type_synonym f32 = "fN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:66.1-66.20 *)
type_synonym f64 = "fN"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:68.1-68.39 *)
function (sequential) fzero :: "N ⇒ fN" where
		  "fzero v_N = (POS (SUBNORM 0))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:71.1-71.39 *)
function (sequential) fone :: "N ⇒ fN" where
		  "fone v_N = (POS (NORM 1 (0 :: nat)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:74.1-74.21 *)
function (sequential) canon_underscore :: "N ⇒ nat" where
		  "canon_underscore v_N = (2 ^ ((((the ((signif v_N))) :: nat) - (1 :: nat)) :: nat))"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:80.1-81.8 *)
type_synonym vN = "iN"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.1-88.85 *)
datatype res_char =
	  mk_char "nat"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.1-88.85 *)
function (sequential) proj_char_0 :: "res_char ⇒ (nat)" where
		  "proj_char_0 (mk_char v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.8-88.12 *)
inductive wf_char :: "res_char ⇒ bool" where
	  char_case_0 :
		"(((i ≥ 0) ∧ (i ≤ 55295)) ∨ ((i ≥ 57344) ∧ (i ≤ 1114111))) ⟹
		 wf_char (mk_char i)"

(* Mutual Recursion at: ../specification/wasm-2.0/1-syntax.spectec:90.1-90.25 *)
inductive fun_utf8 :: "(res_char list) ⇒ (byte list) ⇒ bool" where
	  fun_utf8_case_0 :
		"(wf_byte (mk_byte (proj_char_0 ch))) ⟹
		 (((proj_char_0 ch) < 128) ∧ ((mk_byte (proj_char_0 ch)) = b)) ⟹
		 fun_utf8 [ch] [b]"
	| fun_utf8_case_1 :
		"(((128 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 2048)) ∧ ((proj_char_0 ch) = (((2 ^ 6) * ((((proj_byte_0 b_1) :: nat) - (192 :: nat)) :: nat)) + ((((proj_byte_0 b_2) :: nat) - (128 :: nat)) :: nat)))) ⟹
		 fun_utf8 [ch] [b_1, b_2]"
	| fun_utf8_case_2 :
		"((((2048 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 55296)) ∨ ((57344 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 65536))) ∧ ((proj_char_0 ch) = ((((2 ^ 12) * ((((proj_byte_0 b_1) :: nat) - (224 :: nat)) :: nat)) + ((2 ^ 6) * ((((proj_byte_0 b_2) :: nat) - (128 :: nat)) :: nat))) + ((((proj_byte_0 b_3) :: nat) - (128 :: nat)) :: nat)))) ⟹
		 fun_utf8 [ch] [b_1, b_2, b_3]"
	| fun_utf8_case_3 :
		"(((65536 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 69632)) ∧ ((proj_char_0 ch) = (((((2 ^ 18) * ((((proj_byte_0 b_1) :: nat) - (240 :: nat)) :: nat)) + ((2 ^ 12) * ((((proj_byte_0 b_2) :: nat) - (128 :: nat)) :: nat))) + ((2 ^ 6) * ((((proj_byte_0 b_3) :: nat) - (128 :: nat)) :: nat))) + ((((proj_byte_0 b_4) :: nat) - (128 :: nat)) :: nat)))) ⟹
		 fun_utf8 [ch] [b_1, b_2, b_3, b_4]"
	| fun_utf8_case_4 :
		"((length var_0_lst) = (length ch_lst)) ⟹
		 list_all2 (λ (var_0 :: (byte list)) (ch :: res_char). (fun_utf8 [ch] var_0)) var_0_lst ch_lst ⟹
		 fun_utf8 ch_lst (concat_underscore  var_0_lst)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.1-92.70 *)
datatype name =
	  mk_name "(res_char list)"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.1-92.70 *)
function (sequential) proj_name_0 :: "name ⇒ ((res_char list))" where
		  "proj_name_0 (mk_name v_char_list_0) = (v_char_list_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.8-92.12 *)
inductive wf_name :: "name ⇒ bool" where
	  name_case_0 :
		"(fun_utf8 char_lst var_0) ⟹
		 list_all (λ (v_char :: res_char). (wf_char v_char)) char_lst ⟹
		 ((length var_0) < (2 ^ 32)) ⟹
		 wf_name (mk_name char_lst)"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:101.1-101.36 *)
type_synonym idx = "u32"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:102.1-102.44 *)
type_synonym laneidx = "u8"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:104.1-104.45 *)
type_synonym typeidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:105.1-105.49 *)
type_synonym funcidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:106.1-106.49 *)
type_synonym globalidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:107.1-107.47 *)
type_synonym tableidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:108.1-108.46 *)
type_synonym memidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:109.1-109.45 *)
type_synonym elemidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:110.1-110.45 *)
type_synonym dataidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:111.1-111.47 *)
type_synonym labelidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:112.1-112.47 *)
type_synonym localidx = "idx"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:126.1-127.26 *)
datatype numtype =
	  I32
	| I64
	| F32
	| F64

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:129.1-130.9 *)
datatype vectype =
	  V128
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:132.1-133.22 *)
datatype consttype =
	  consttype_I32
	| consttype_I64
	| consttype_F32
	| consttype_F64
	| consttype_V128

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:135.1-136.24 *)
datatype reftype =
	  FUNCREF
	| EXTERNREF

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:138.1-139.38 *)
datatype valtype =
	  valtype_I32
	| valtype_I64
	| valtype_F32
	| valtype_F64
	| valtype_V128
	| valtype_FUNCREF
	| valtype_EXTERNREF
	| BOT

(* Auxiliary Definition at:  *)
function (sequential) valtype_numtype :: "numtype ⇒ valtype" where
		  "valtype_numtype I32 = valtype_I32"
		| "valtype_numtype I64 = valtype_I64"
		| "valtype_numtype F32 = valtype_F32"
		| "valtype_numtype F64 = valtype_F64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) valtype_reftype :: "reftype ⇒ valtype" where
		  "valtype_reftype FUNCREF = valtype_FUNCREF"
		| "valtype_reftype EXTERNREF = valtype_EXTERNREF"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) valtype_vectype :: "vectype ⇒ valtype" where
		  "valtype_vectype V128 = valtype_V128"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:141.1-141.38 *)
datatype Inn =
	  Inn_I32
	| Inn_I64

(* Auxiliary Definition at:  *)
function (sequential) numtype_Inn :: "Inn ⇒ numtype" where
		  "numtype_Inn Inn_I32 = I32"
		| "numtype_Inn Inn_I64 = I64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) valtype_Inn :: "Inn ⇒ valtype" where
		  "valtype_Inn Inn_I32 = valtype_I32"
		| "valtype_Inn Inn_I64 = valtype_I64"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:142.1-142.38 *)
datatype Fnn =
	  Fnn_F32
	| Fnn_F64

(* Auxiliary Definition at:  *)
function (sequential) numtype_Fnn :: "Fnn ⇒ numtype" where
		  "numtype_Fnn Fnn_F32 = F32"
		| "numtype_Fnn Fnn_F64 = F64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) valtype_Fnn :: "Fnn ⇒ valtype" where
		  "valtype_Fnn Fnn_F32 = valtype_F32"
		| "valtype_Fnn Fnn_F64 = valtype_F64"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:143.1-143.36 *)
type_synonym Vnn = "vectype"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:146.1-147.16 *)
type_synonym resulttype = "(valtype res_list)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:152.1-152.52 *)
datatype packtype =
	  I8
	| I16

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:153.1-153.60 *)
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
function (sequential) lanetype_Inn :: "Inn ⇒ lanetype" where
		  "lanetype_Inn Inn_I32 = lanetype_I32"
		| "lanetype_Inn Inn_I64 = lanetype_I64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) lanetype_numtype :: "numtype ⇒ lanetype" where
		  "lanetype_numtype I32 = lanetype_I32"
		| "lanetype_numtype I64 = lanetype_I64"
		| "lanetype_numtype F32 = lanetype_F32"
		| "lanetype_numtype F64 = lanetype_F64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) lanetype_packtype :: "packtype ⇒ lanetype" where
		  "lanetype_packtype I8 = lanetype_I8"
		| "lanetype_packtype I16 = lanetype_I16"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:155.1-155.37 *)
type_synonym Pnn = "packtype"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:156.1-156.38 *)
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
function (sequential) Jnn_packtype :: "packtype ⇒ Jnn" where
		  "Jnn_packtype I8 = Jnn_I8"
		| "Jnn_packtype I16 = Jnn_I16"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:157.1-157.37 *)
type_synonym Lnn = "lanetype"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:162.1-162.18 *)
type_synonym mut = "(MUT option)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:164.1-165.17 *)
datatype limits =
	  mk_limits "u32" "(u32 option)"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:164.8-164.14 *)
inductive wf_limits :: "limits ⇒ bool" where
	  limits_case_0 :
		"(wf_uN 32 v_u32) ⟹
		 wf_limits (mk_limits v_u32 u32_opt)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:167.1-168.14 *)
datatype globaltype =
	  mk_globaltype "mut" "valtype"
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:169.1-170.27 *)
datatype functype =
	  mk_functype "resulttype" "resulttype"
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:171.1-172.17 *)
datatype tabletype =
	  mk_tabletype "limits" "reftype"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:171.8-171.17 *)
inductive wf_tabletype :: "tabletype ⇒ bool" where
	  tabletype_case_0 :
		"(wf_limits v_limits) ⟹
		 wf_tabletype (mk_tabletype v_limits v_reftype)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:173.1-174.14 *)
datatype memtype =
	  PAGE "limits"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:173.8-173.15 *)
inductive wf_memtype :: "memtype ⇒ bool" where
	  memtype_case_0 :
		"(wf_limits v_limits) ⟹
		 wf_memtype (PAGE v_limits)"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:175.1-176.10 *)
type_synonym elemtype = "reftype"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:177.1-178.5 *)
datatype res_datatype =
	  OK
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:179.1-180.70 *)
datatype externtype =
	  FUNC "functype"
	| GLOBAL "globaltype"
	| TABLE "tabletype"
	| MEM "memtype"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:179.8-179.18 *)
inductive wf_externtype :: "externtype ⇒ bool" where
	  externtype_case_0 :
		"wf_externtype (FUNC v_functype)"
	| externtype_case_1 :
		"wf_externtype (GLOBAL v_globaltype)"
	| externtype_case_2 :
		"(wf_tabletype v_tabletype) ⟹
		 wf_externtype (TABLE v_tabletype)"
	| externtype_case_3 :
		"(wf_memtype v_memtype) ⟹
		 wf_externtype (MEM v_memtype)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:318.1-318.60 *)
datatype dim =
	  mk_dim "nat"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:318.1-318.60 *)
function (sequential) proj_dim_0 :: "dim ⇒ (nat)" where
		  "proj_dim_0 (mk_dim v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:318.8-318.11 *)
inductive wf_dim :: "dim ⇒ bool" where
	  dim_case_0 :
		"(((((i = 1) ∨ (i = 2)) ∨ (i = 4)) ∨ (i = 8)) ∨ (i = 16)) ⟹
		 wf_dim (mk_dim i)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:319.1-319.69 *)
datatype shape =
	  X "lanetype" "dim"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:319.8-319.13 *)
inductive wf_shape :: "shape ⇒ bool" where
	  shape_case_0 :
		"(wf_dim v_dim) ⟹
		 wf_shape (X v_lanetype v_dim)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:206.1-206.32 *)
function (sequential) fun_lanetype :: "shape ⇒ lanetype" where
		  "fun_lanetype (X v_Lnn (mk_dim v_N)) = v_Lnn"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:208.1-208.59 *)
function (sequential) size :: "valtype ⇒ (nat option)" where
		  "size valtype_I32 = (Some 32)"
		| "size valtype_I64 = (Some 64)"
		| "size valtype_F32 = (Some 32)"
		| "size valtype_F64 = (Some 64)"
		| "size valtype_V128 = (Some 128)"
		| "size x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:209.1-209.45 *)
function (sequential) psize :: "packtype ⇒ nat" where
		  "psize I8 = 8"
		| "psize I16 = 16"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:210.1-210.45 *)
function (sequential) lsize :: "lanetype ⇒ nat" where
		  "lsize lanetype_I32 = (the ((size (valtype_numtype I32))))"
		| "lsize lanetype_I64 = (the ((size (valtype_numtype I64))))"
		| "lsize lanetype_F32 = (the ((size (valtype_numtype F32))))"
		| "lsize lanetype_F64 = (the ((size (valtype_numtype F64))))"
		| "lsize lanetype_I8 = (psize I8)"
		| "lsize lanetype_I16 = (psize I16)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:211.1-211.70 *)
function (sequential) isize :: "Inn ⇒ nat" where
		  "isize v_Inn = (the ((size (valtype_Inn v_Inn))))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:212.1-212.70 *)
function (sequential) jsize :: "Jnn ⇒ nat" where
		  "jsize v_Jnn = (lsize (lanetype_Jnn v_Jnn))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:213.1-213.70 *)
function (sequential) fsize :: "Fnn ⇒ nat" where
		  "fsize v_Fnn = (the ((size (valtype_Fnn v_Fnn))))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:231.1-231.63 *)
function (sequential) sizenn :: "numtype ⇒ nat" where
		  "sizenn nt = (the ((size (valtype_numtype nt))))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:232.1-232.63 *)
function (sequential) sizenn1 :: "numtype ⇒ nat" where
		  "sizenn1 nt = (the ((size (valtype_numtype nt))))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:233.1-233.63 *)
function (sequential) sizenn2 :: "numtype ⇒ nat" where
		  "sizenn2 nt = (the ((size (valtype_numtype nt))))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:238.1-238.63 *)
function (sequential) lsizenn :: "lanetype ⇒ nat" where
		  "lsizenn lt = (lsize lt)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:239.1-239.63 *)
function (sequential) lsizenn1 :: "lanetype ⇒ nat" where
		  "lsizenn1 lt = (lsize lt)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:240.1-240.63 *)
function (sequential) lsizenn2 :: "lanetype ⇒ nat" where
		  "lsizenn2 lt = (lsize lt)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:245.1-245.40 *)
function (sequential) inv_isize :: "nat ⇒ (Inn option)" where
		  "inv_isize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some Inn_I32)"
		| "inv_isize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some Inn_I64)"
		| "inv_isize x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:246.1-246.40 *)
function (sequential) inv_jsize :: "nat ⇒ (Jnn option)" where
		  "inv_jsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) = (Some Jnn_I8)"
		| "inv_jsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))) = (Some Jnn_I16)"
		| "inv_jsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some Jnn_I32)"
		| "inv_jsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some Jnn_I64)"
		| "inv_jsize x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:247.1-247.40 *)
function (sequential) inv_fsize :: "nat ⇒ (Fnn option)" where
		  "inv_fsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some Fnn_F32)"
		| "inv_fsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some Fnn_F64)"
		| "inv_fsize x0 = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 *)
datatype num_underscore =
	  mk_num__0 "Inn" "iN"
	| mk_num__1 "Fnn" "fN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.8-259.13 *)
inductive wf_num_underscore :: "numtype ⇒ num_underscore ⇒ bool" where
	  num__case_0 :
		"((size (valtype_Inn v_Inn)) ≠ None) ⟹
		 (wf_uN (the ((size (valtype_Inn v_Inn)))) var_x) ⟹
		 (v_numtype = (numtype_Inn v_Inn)) ⟹
		 wf_num_underscore v_numtype (mk_num__0 v_Inn var_x)"
	| num__case_1 :
		"(wf_fN (sizenn (numtype_Fnn v_Fnn)) var_x) ⟹
		 (v_numtype = (numtype_Fnn v_Fnn)) ⟹
		 wf_num_underscore v_numtype (mk_num__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 *)
function (sequential) proj_num__0 :: "num_underscore ⇒ (iN option)" where
		  "proj_num__0 (mk_num__0 v_Inn var_x) = (Some var_x)"
		| "proj_num__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 *)
function (sequential) proj_num__1 :: "num_underscore ⇒ (fN option)" where
		  "proj_num__1 (mk_num__1 v_Fnn var_x) = (Some var_x)"
		| "proj_num__1 var_x = None"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:263.1-263.36 *)
type_synonym pack_underscore = "iN"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 *)
datatype lane_underscore =
	  mk_lane__0 "numtype" "num_underscore"
	| mk_lane__1 "packtype" "pack_underscore"
	| mk_lane__2 "Jnn" "iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.8-265.14 *)
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

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 *)
function (sequential) proj_lane__0 :: "lane_underscore ⇒ (num_underscore option)" where
		  "proj_lane__0 (mk_lane__0 v_numtype var_x) = (Some var_x)"
		| "proj_lane__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 *)
function (sequential) proj_lane__1 :: "lane_underscore ⇒ (pack_underscore option)" where
		  "proj_lane__1 (mk_lane__1 v_packtype var_x) = (Some var_x)"
		| "proj_lane__1 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 *)
function (sequential) proj_lane__2 :: "lane_underscore ⇒ (iN option)" where
		  "proj_lane__2 (mk_lane__2 v_Jnn var_x) = (Some var_x)"
		| "proj_lane__2 var_x = None"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:270.1-270.34 *)
type_synonym vec_underscore = "vN"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:272.1-272.35 *)
function (sequential) fun_zero :: "numtype ⇒ num_underscore" where
		  "fun_zero I32 = (mk_num__0 Inn_I32 (mk_uN 0))"
		| "fun_zero I64 = (mk_num__0 Inn_I64 (mk_uN 0))"
		| "fun_zero F32 = (mk_num__1 Fnn_F32 (fzero (the ((size (valtype_Fnn Fnn_F32))))))"
		| "fun_zero F64 = (mk_num__1 Fnn_F64 (fzero (the ((size (valtype_Fnn Fnn_F64))))))"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:279.1-279.42 *)
datatype sx =
	  U
	| S

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.1-280.56 *)
datatype sz =
	  mk_sz "nat"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.1-280.56 *)
function (sequential) proj_sz_0 :: "sz ⇒ (nat)" where
		  "proj_sz_0 (mk_sz v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.8-280.10 *)
inductive wf_sz :: "sz ⇒ bool" where
	  sz_case_0 :
		"((((i = 8) ∨ (i = 16)) ∨ (i = 32)) ∨ (i = 64)) ⟹
		 wf_sz (mk_sz i)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
datatype unop_Inn =
	  CLZ
	| CTZ
	| POPCNT
	| EXTEND "n"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
datatype unop_Fnn =
	  ABS
	| unop_Fnn_NEG
	| SQRT
	| CEIL
	| FLOOR
	| TRUNC
	| NEAREST

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
datatype unop_underscore =
	  mk_unop__0 "Inn" "unop_Inn"
	| mk_unop__1 "Fnn" "unop_Fnn"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.8-282.14 *)
inductive wf_unop_underscore :: "numtype ⇒ unop_underscore ⇒ bool" where
	  unop__case_0 :
		"(v_numtype = (numtype_Inn v_Inn)) ⟹
		 wf_unop_underscore v_numtype (mk_unop__0 v_Inn var_x)"
	| unop__case_1 :
		"(v_numtype = (numtype_Fnn v_Fnn)) ⟹
		 wf_unop_underscore v_numtype (mk_unop__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
function (sequential) proj_unop__0 :: "unop_underscore ⇒ (unop_Inn option)" where
		  "proj_unop__0 (mk_unop__0 v_Inn var_x) = (Some var_x)"
		| "proj_unop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
function (sequential) proj_unop__1 :: "unop_underscore ⇒ (unop_Fnn option)" where
		  "proj_unop__1 (mk_unop__1 v_Fnn var_x) = (Some var_x)"
		| "proj_unop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
datatype binop_Inn =
	  ADD
	| SUB
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

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
datatype binop_Fnn =
	  binop_Fnn_ADD
	| binop_Fnn_SUB
	| binop_Fnn_MUL
	| binop_Fnn_DIV
	| res_MIN
	| res_MAX
	| COPYSIGN

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
datatype binop_underscore =
	  mk_binop__0 "Inn" "binop_Inn"
	| mk_binop__1 "Fnn" "binop_Fnn"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.8-286.15 *)
inductive wf_binop_underscore :: "numtype ⇒ binop_underscore ⇒ bool" where
	  binop__case_0 :
		"(v_numtype = (numtype_Inn v_Inn)) ⟹
		 wf_binop_underscore v_numtype (mk_binop__0 v_Inn var_x)"
	| binop__case_1 :
		"(v_numtype = (numtype_Fnn v_Fnn)) ⟹
		 wf_binop_underscore v_numtype (mk_binop__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
function (sequential) proj_binop__0 :: "binop_underscore ⇒ (binop_Inn option)" where
		  "proj_binop__0 (mk_binop__0 v_Inn var_x) = (Some var_x)"
		| "proj_binop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
function (sequential) proj_binop__1 :: "binop_underscore ⇒ (binop_Fnn option)" where
		  "proj_binop__1 (mk_binop__1 v_Fnn var_x) = (Some var_x)"
		| "proj_binop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 *)
datatype testop_Inn =
	  EQZ
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 *)
datatype testop_underscore =
	  mk_testop__0 "Inn" "testop_Inn"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.8-293.16 *)
inductive wf_testop_underscore :: "numtype ⇒ testop_underscore ⇒ bool" where
	  testop__case_0 :
		"(v_numtype = (numtype_Inn v_Inn)) ⟹
		 wf_testop_underscore v_numtype (mk_testop__0 v_Inn var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 *)
function (sequential) proj_testop__0 :: "testop_underscore ⇒ testop_Inn" where
		  "proj_testop__0 (mk_testop__0 v_Inn var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
datatype relop_Inn =
	  EQ
	| NE
	| LT "sx"
	| GT "sx"
	| LE "sx"
	| GE "sx"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
datatype relop_Fnn =
	  relop_Fnn_EQ
	| relop_Fnn_NE
	| relop_Fnn_LT
	| relop_Fnn_GT
	| relop_Fnn_LE
	| relop_Fnn_GE

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
datatype relop_underscore =
	  mk_relop__0 "Inn" "relop_Inn"
	| mk_relop__1 "Fnn" "relop_Fnn"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.8-297.15 *)
inductive wf_relop_underscore :: "numtype ⇒ relop_underscore ⇒ bool" where
	  relop__case_0 :
		"(v_numtype = (numtype_Inn v_Inn)) ⟹
		 wf_relop_underscore v_numtype (mk_relop__0 v_Inn var_x)"
	| relop__case_1 :
		"(v_numtype = (numtype_Fnn v_Fnn)) ⟹
		 wf_relop_underscore v_numtype (mk_relop__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
function (sequential) proj_relop__0 :: "relop_underscore ⇒ (relop_Inn option)" where
		  "proj_relop__0 (mk_relop__0 v_Inn var_x) = (Some var_x)"
		| "proj_relop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
function (sequential) proj_relop__1 :: "relop_underscore ⇒ (relop_Fnn option)" where
		  "proj_relop__1 (mk_relop__1 v_Fnn var_x) = (Some var_x)"
		| "proj_relop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-313.16 *)
datatype cvtop =
	  cvtop_EXTEND "sx"
	| WRAP
	| CONVERT "sx"
	| cvtop_TRUNC "sx"
	| TRUNC_SAT "sx"
	| PROMOTE
	| DEMOTE
	| REINTERPRET

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:320.1-320.69 *)
datatype ishape =
	  ishape_X "Jnn" "dim"
	

(* Auxiliary Definition at:  *)
function (sequential) shape_ishape :: "ishape ⇒ shape" where
		  "shape_ishape (ishape_X x0 x1) = (X (lanetype_Jnn x0) x1)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:320.8-320.14 *)
inductive wf_ishape :: "ishape ⇒ bool" where
	  ishape_case_0 :
		"(wf_dim v_dim) ⟹
		 wf_ishape (ishape_X v_Jnn v_dim)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:321.1-321.69 *)
datatype fshape =
	  fshape_X "Fnn" "dim"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:321.8-321.14 *)
inductive wf_fshape :: "fshape ⇒ bool" where
	  fshape_case_0 :
		"(wf_dim v_dim) ⟹
		 wf_fshape (fshape_X v_Fnn v_dim)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:322.1-322.69 *)
datatype pshape =
	  pshape_X "Pnn" "dim"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:322.8-322.14 *)
inductive wf_pshape :: "pshape ⇒ bool" where
	  pshape_case_0 :
		"(wf_dim v_dim) ⟹
		 wf_pshape (pshape_X v_Pnn v_dim)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:324.1-324.22 *)
function (sequential) fun_dim :: "shape ⇒ dim" where
		  "fun_dim (X v_Lnn (mk_dim v_N)) = (mk_dim v_N)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:325.1-325.41 *)
function (sequential) shsize :: "shape ⇒ nat" where
		  "shsize (X v_Lnn (mk_dim v_N)) = ((lsize v_Lnn) * v_N)"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:327.1-327.20 *)
datatype vvunop =
	  NOT
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:328.1-328.41 *)
datatype vvbinop =
	  vvbinop_AND
	| ANDNOT
	| vvbinop_OR
	| vvbinop_XOR

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:329.1-329.28 *)
datatype vvternop =
	  BITSELECT
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:330.1-330.27 *)
datatype vvtestop =
	  ANY_TRUE
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 *)
datatype vunop_Jnn_N =
	  vunop_Jnn_N_ABS
	| vunop_Jnn_N_NEG
	| vunop_Jnn_N_POPCNT

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.8-332.15 *)
inductive wf_vunop_Jnn_N :: "Jnn ⇒ N ⇒ vunop_Jnn_N ⇒ bool" where
	  vunop_Jnn_N_case_0 :
		"wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N_ABS"
	| vunop_Jnn_N_case_1 :
		"wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N_NEG"
	| vunop_Jnn_N_case_2 :
		"(v_Jnn = Jnn_I8) ⟹
		 wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N_POPCNT"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 *)
datatype vunop_Fnn_N =
	  vunop_Fnn_N_ABS
	| vunop_Fnn_N_NEG
	| vunop_Fnn_N_SQRT
	| vunop_Fnn_N_CEIL
	| vunop_Fnn_N_FLOOR
	| vunop_Fnn_N_TRUNC
	| vunop_Fnn_N_NEAREST

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 *)
datatype vunop_underscore =
	  mk_vunop__0 "Jnn" "N" "vunop_Jnn_N"
	| mk_vunop__1 "Fnn" "N" "vunop_Fnn_N"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.8-332.15 *)
inductive wf_vunop_underscore :: "shape ⇒ vunop_underscore ⇒ bool" where
	  vunop__case_0 :
		"(wf_vunop_Jnn_N v_Jnn v_N var_x) ⟹
		 (v_shape = (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ⟹
		 wf_vunop_underscore v_shape (mk_vunop__0 v_Jnn v_N var_x)"
	| vunop__case_1 :
		"(v_shape = (X (lanetype_Fnn v_Fnn) (mk_dim v_N))) ⟹
		 wf_vunop_underscore v_shape (mk_vunop__1 v_Fnn v_N var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 *)
function (sequential) proj_vunop__0 :: "vunop_underscore ⇒ (vunop_Jnn_N option)" where
		  "proj_vunop__0 (mk_vunop__0 v_Jnn v_N var_x) = (Some var_x)"
		| "proj_vunop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 *)
function (sequential) proj_vunop__1 :: "vunop_underscore ⇒ (vunop_Fnn_N option)" where
		  "proj_vunop__1 (mk_vunop__1 v_Fnn v_N var_x) = (Some var_x)"
		| "proj_vunop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 *)
datatype vbinop_Jnn_N =
	  vbinop_Jnn_N_ADD
	| vbinop_Jnn_N_SUB
	| ADD_SAT "sx"
	| SUB_SAT "sx"
	| vbinop_Jnn_N_MUL
	| AVGRU
	| Q15MULR_SATS
	| vbinop_Jnn_N_MIN "sx"
	| vbinop_Jnn_N_MAX "sx"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.8-337.16 *)
inductive wf_vbinop_Jnn_N :: "Jnn ⇒ N ⇒ vbinop_Jnn_N ⇒ bool" where
	  vbinop_Jnn_N_case_0 :
		"wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N_ADD"
	| vbinop_Jnn_N_case_1 :
		"wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N_SUB"
	| vbinop_Jnn_N_case_2 :
		"((lsizenn (lanetype_Jnn v_Jnn)) ≤ 16) ⟹
		 wf_vbinop_Jnn_N v_Jnn v_N (ADD_SAT v_sx)"
	| vbinop_Jnn_N_case_3 :
		"((lsizenn (lanetype_Jnn v_Jnn)) ≤ 16) ⟹
		 wf_vbinop_Jnn_N v_Jnn v_N (SUB_SAT v_sx)"
	| vbinop_Jnn_N_case_4 :
		"((lsizenn (lanetype_Jnn v_Jnn)) ≥ 16) ⟹
		 wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N_MUL"
	| vbinop_Jnn_N_case_5 :
		"((lsizenn (lanetype_Jnn v_Jnn)) ≤ 16) ⟹
		 wf_vbinop_Jnn_N v_Jnn v_N AVGRU"
	| vbinop_Jnn_N_case_6 :
		"((lsizenn (lanetype_Jnn v_Jnn)) = 16) ⟹
		 wf_vbinop_Jnn_N v_Jnn v_N Q15MULR_SATS"
	| vbinop_Jnn_N_case_7 :
		"((lsizenn (lanetype_Jnn v_Jnn)) ≤ 32) ⟹
		 wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N_MIN v_sx)"
	| vbinop_Jnn_N_case_8 :
		"((lsizenn (lanetype_Jnn v_Jnn)) ≤ 32) ⟹
		 wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N_MAX v_sx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 *)
datatype vbinop_Fnn_N =
	  vbinop_Fnn_N_ADD
	| vbinop_Fnn_N_SUB
	| vbinop_Fnn_N_MUL
	| vbinop_Fnn_N_DIV
	| vbinop_Fnn_N_MIN
	| vbinop_Fnn_N_MAX
	| PMIN
	| PMAX

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 *)
datatype vbinop_underscore =
	  mk_vbinop__0 "Jnn" "N" "vbinop_Jnn_N"
	| mk_vbinop__1 "Fnn" "N" "vbinop_Fnn_N"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.8-337.16 *)
inductive wf_vbinop_underscore :: "shape ⇒ vbinop_underscore ⇒ bool" where
	  vbinop__case_0 :
		"(wf_vbinop_Jnn_N v_Jnn v_N var_x) ⟹
		 (v_shape = (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ⟹
		 wf_vbinop_underscore v_shape (mk_vbinop__0 v_Jnn v_N var_x)"
	| vbinop__case_1 :
		"(v_shape = (X (lanetype_Fnn v_Fnn) (mk_dim v_N))) ⟹
		 wf_vbinop_underscore v_shape (mk_vbinop__1 v_Fnn v_N var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 *)
function (sequential) proj_vbinop__0 :: "vbinop_underscore ⇒ (vbinop_Jnn_N option)" where
		  "proj_vbinop__0 (mk_vbinop__0 v_Jnn v_N var_x) = (Some var_x)"
		| "proj_vbinop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 *)
function (sequential) proj_vbinop__1 :: "vbinop_underscore ⇒ (vbinop_Fnn_N option)" where
		  "proj_vbinop__1 (mk_vbinop__1 v_Fnn v_N var_x) = (Some var_x)"
		| "proj_vbinop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:350.1-350.23 *)
datatype vtestop_Jnn_N =
	  ALL_TRUE
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:350.1-350.23 *)
datatype vtestop_underscore =
	  mk_vtestop__0 "Jnn" "N" "vtestop_Jnn_N"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:350.8-350.17 *)
inductive wf_vtestop_underscore :: "shape ⇒ vtestop_underscore ⇒ bool" where
	  vtestop__case_0 :
		"(v_shape = (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ⟹
		 wf_vtestop_underscore v_shape (mk_vtestop__0 v_Jnn v_N var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:350.1-350.23 *)
function (sequential) proj_vtestop__0 :: "vtestop_underscore ⇒ vtestop_Jnn_N" where
		  "proj_vtestop__0 (mk_vtestop__0 v_Jnn v_N var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 *)
datatype vrelop_Jnn_N =
	  vrelop_Jnn_N_EQ
	| vrelop_Jnn_N_NE
	| vrelop_Jnn_N_LT "sx"
	| vrelop_Jnn_N_GT "sx"
	| vrelop_Jnn_N_LE "sx"
	| vrelop_Jnn_N_GE "sx"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.8-354.16 *)
inductive wf_vrelop_Jnn_N :: "Jnn ⇒ N ⇒ vrelop_Jnn_N ⇒ bool" where
	  vrelop_Jnn_N_case_0 :
		"wf_vrelop_Jnn_N v_Jnn v_N vrelop_Jnn_N_EQ"
	| vrelop_Jnn_N_case_1 :
		"wf_vrelop_Jnn_N v_Jnn v_N vrelop_Jnn_N_NE"
	| vrelop_Jnn_N_case_2 :
		"(((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = S)) ⟹
		 wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N_LT v_sx)"
	| vrelop_Jnn_N_case_3 :
		"(((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = S)) ⟹
		 wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N_GT v_sx)"
	| vrelop_Jnn_N_case_4 :
		"(((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = S)) ⟹
		 wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N_LE v_sx)"
	| vrelop_Jnn_N_case_5 :
		"(((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = S)) ⟹
		 wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N_GE v_sx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 *)
datatype vrelop_Fnn_N =
	  vrelop_Fnn_N_EQ
	| vrelop_Fnn_N_NE
	| vrelop_Fnn_N_LT
	| vrelop_Fnn_N_GT
	| vrelop_Fnn_N_LE
	| vrelop_Fnn_N_GE

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 *)
datatype vrelop_underscore =
	  mk_vrelop__0 "Jnn" "N" "vrelop_Jnn_N"
	| mk_vrelop__1 "Fnn" "N" "vrelop_Fnn_N"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.8-354.16 *)
inductive wf_vrelop_underscore :: "shape ⇒ vrelop_underscore ⇒ bool" where
	  vrelop__case_0 :
		"(wf_vrelop_Jnn_N v_Jnn v_N var_x) ⟹
		 (v_shape = (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ⟹
		 wf_vrelop_underscore v_shape (mk_vrelop__0 v_Jnn v_N var_x)"
	| vrelop__case_1 :
		"(v_shape = (X (lanetype_Fnn v_Fnn) (mk_dim v_N))) ⟹
		 wf_vrelop_underscore v_shape (mk_vrelop__1 v_Fnn v_N var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 *)
function (sequential) proj_vrelop__0 :: "vrelop_underscore ⇒ (vrelop_Jnn_N option)" where
		  "proj_vrelop__0 (mk_vrelop__0 v_Jnn v_N var_x) = (Some var_x)"
		| "proj_vrelop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 *)
function (sequential) proj_vrelop__1 :: "vrelop_underscore ⇒ (vrelop_Fnn_N option)" where
		  "proj_vrelop__1 (mk_vrelop__1 v_Fnn v_N var_x) = (Some var_x)"
		| "proj_vrelop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:362.1-362.48 *)
datatype half =
	  LOW
	| HIGH

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:363.1-363.19 *)
datatype zero =
	  ZERO
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:365.1-365.99 *)
datatype vcvtop =
	  vcvtop_EXTEND "half" "sx"
	| vcvtop_TRUNC_SAT "sx" "(zero option)"
	| vcvtop_CONVERT "(half option)" "sx"
	| vcvtop_DEMOTE "zero"
	| PROMOTELOW

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.1-367.25 *)
datatype vshiftop_Jnn_N =
	  vshiftop_Jnn_N_SHL
	| vshiftop_Jnn_N_SHR "sx"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.1-367.25 *)
datatype vshiftop_underscore =
	  mk_vshiftop__0 "Jnn" "N" "vshiftop_Jnn_N"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.8-367.18 *)
inductive wf_vshiftop_underscore :: "ishape ⇒ vshiftop_underscore ⇒ bool" where
	  vshiftop__case_0 :
		"(v_ishape = (ishape_X v_Jnn (mk_dim v_N))) ⟹
		 wf_vshiftop_underscore v_ishape (mk_vshiftop__0 v_Jnn v_N var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.1-367.25 *)
function (sequential) proj_vshiftop__0 :: "vshiftop_underscore ⇒ vshiftop_Jnn_N" where
		  "proj_vshiftop__0 (mk_vshiftop__0 v_Jnn v_N var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.1-370.25 *)
datatype vextunop_Jnn_N =
	  EXTADD_PAIRWISE "sx"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.8-370.18 *)
inductive wf_vextunop_Jnn_N :: "Jnn ⇒ N ⇒ vextunop_Jnn_N ⇒ bool" where
	  vextunop_Jnn_N_case_0 :
		"((16 ≤ (lsizenn (lanetype_Jnn v_Jnn))) ∧ ((lsizenn (lanetype_Jnn v_Jnn)) ≤ 32)) ⟹
		 wf_vextunop_Jnn_N v_Jnn v_N (EXTADD_PAIRWISE v_sx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.1-370.25 *)
datatype vextunop_underscore =
	  mk_vextunop__0 "Jnn" "N" "vextunop_Jnn_N"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.8-370.18 *)
inductive wf_vextunop_underscore :: "ishape ⇒ vextunop_underscore ⇒ bool" where
	  vextunop__case_0 :
		"(wf_vextunop_Jnn_N v_Jnn v_N var_x) ⟹
		 (v_ishape = (ishape_X v_Jnn (mk_dim v_N))) ⟹
		 wf_vextunop_underscore v_ishape (mk_vextunop__0 v_Jnn v_N var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.1-370.25 *)
function (sequential) proj_vextunop__0 :: "vextunop_underscore ⇒ vextunop_Jnn_N" where
		  "proj_vextunop__0 (mk_vextunop__0 v_Jnn v_N var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.1-373.26 *)
datatype vextbinop_Jnn_N =
	  EXTMUL "half" "sx"
	| DOTS

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.8-373.19 *)
inductive wf_vextbinop_Jnn_N :: "Jnn ⇒ N ⇒ vextbinop_Jnn_N ⇒ bool" where
	  vextbinop_Jnn_N_case_0 :
		"wf_vextbinop_Jnn_N v_Jnn v_N (EXTMUL v_half v_sx)"
	| vextbinop_Jnn_N_case_1 :
		"((lsizenn (lanetype_Jnn v_Jnn)) = 32) ⟹
		 wf_vextbinop_Jnn_N v_Jnn v_N DOTS"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.1-373.26 *)
datatype vextbinop_underscore =
	  mk_vextbinop__0 "Jnn" "N" "vextbinop_Jnn_N"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.8-373.19 *)
inductive wf_vextbinop_underscore :: "ishape ⇒ vextbinop_underscore ⇒ bool" where
	  vextbinop__case_0 :
		"(wf_vextbinop_Jnn_N v_Jnn v_N var_x) ⟹
		 (v_ishape = (ishape_X v_Jnn (mk_dim v_N))) ⟹
		 wf_vextbinop_underscore v_ishape (mk_vextbinop__0 v_Jnn v_N var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.1-373.26 *)
function (sequential) proj_vextbinop__0 :: "vextbinop_underscore ⇒ vextbinop_Jnn_N" where
		  "proj_vextbinop__0 (mk_vextbinop__0 v_Jnn v_N var_x) = var_x"
	by pat_completeness auto

(* Record Creation Definition at: ../specification/wasm-2.0/1-syntax.spectec:381.1-381.69 *)
record memarg =
	ALIGN :: "u32"
	OFFSET :: "u32"

definition append_memarg :: "memarg ⇒ memarg ⇒ memarg" where
	"append_memarg arg1 arg2 = ⦇
		ALIGN = ALIGN arg1,
		OFFSET = OFFSET arg1
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:381.8-381.14 *)
inductive wf_memarg :: "memarg ⇒ bool" where
	  memarg_case_underscore :
		"(wf_uN 32 var_0) ⟹
		 (wf_uN 32 var_1) ⟹
		 wf_memarg ⦇ ALIGN = var_0, OFFSET = var_1 ⦈"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.1-385.24 *)
datatype loadop_Inn =
	  mk_loadop_Inn "sz" "sx"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.8-385.16 *)
inductive wf_loadop_Inn :: "Inn ⇒ loadop_Inn ⇒ bool" where
	  loadop_Inn_case_0 :
		"(wf_sz v_sz) ⟹
		 ((proj_sz_0 v_sz) < (sizenn (numtype_Inn v_Inn))) ⟹
		 wf_loadop_Inn v_Inn (mk_loadop_Inn v_sz v_sx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.1-385.24 *)
datatype loadop_underscore =
	  mk_loadop__0 "Inn" "loadop_Inn"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.8-385.16 *)
inductive wf_loadop_underscore :: "numtype ⇒ loadop_underscore ⇒ bool" where
	  loadop__case_0 :
		"(wf_loadop_Inn v_Inn var_x) ⟹
		 (v_numtype = (numtype_Inn v_Inn)) ⟹
		 wf_loadop_underscore v_numtype (mk_loadop__0 v_Inn var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.1-385.24 *)
function (sequential) proj_loadop__0 :: "loadop_underscore ⇒ loadop_Inn" where
		  "proj_loadop__0 (mk_loadop__0 v_Inn var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:388.1-391.46 *)
datatype vloadop =
	  SHAPEX_underscore "nat" "nat" "sx"
	| SPLAT "nat"
	| vloadop_ZERO "nat"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:398.1-400.17 *)
datatype blocktype =
	  underscore_RESULT "(valtype option)"
	| underscore_IDX "typeidx"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:398.8-398.17 *)
inductive wf_blocktype :: "blocktype ⇒ bool" where
	  blocktype_case_0 :
		"wf_blocktype (underscore_RESULT valtype_opt)"
	| blocktype_case_1 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_blocktype (underscore_IDX v_typeidx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:519.1-520.22 *)
datatype instr_st6 =
	  MEMORY_COPY
	| MEMORY_FILL
	| MEMORY_GROW
	| MEMORY_SIZE
	| VSTORE_LANE "vectype" "sz" "memarg" "laneidx"
	| VSTORE "vectype" "memarg"
	| VLOAD_LANE "vectype" "sz" "memarg" "laneidx"
	| VLOAD "vectype" "(vloadop option)" "memarg"
	| STORE "numtype" "(sz option)" "memarg"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:519.1-520.22 *)
datatype instr_st5 =
	  LOAD "numtype" "(loadop_underscore option)" "memarg"
	| ELEM_DROP "elemidx"
	| TABLE_INIT "tableidx" "elemidx"
	| TABLE_COPY "tableidx" "tableidx"
	| TABLE_FILL "tableidx"
	| TABLE_GROW "tableidx"
	| TABLE_SIZE "tableidx"
	| TABLE_SET "tableidx"
	| TABLE_GET "tableidx"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:519.1-520.22 *)
datatype instr_st4 =
	  GLOBAL_SET "globalidx"
	| GLOBAL_GET "globalidx"
	| LOCAL_TEE "localidx"
	| LOCAL_SET "localidx"
	| LOCAL_GET "localidx"
	| REF_IS_NULL
	| REF_FUNC "funcidx"
	| REF_NULL "reftype"
	| VCVTOP "shape" "shape" "vcvtop"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:519.1-520.22 *)
datatype instr_st3 =
	  VNARROW "ishape" "ishape" "sx"
	| VEXTBINOP "ishape" "ishape" "vextbinop_underscore"
	| VEXTUNOP "ishape" "ishape" "vextunop_underscore"
	| VREPLACE_LANE "shape" "laneidx"
	| VEXTRACT_LANE "shape" "(sx option)" "laneidx"
	| VSPLAT "shape"
	| VSHUFFLE "ishape" "(laneidx list)"
	| VSWIZZLE "ishape"
	| VBITMASK "ishape"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:519.1-520.22 *)
datatype instr_st2 =
	  VSHIFTOP "ishape" "vshiftop_underscore"
	| VRELOP "shape" "vrelop_underscore"
	| VTESTOP "shape" "vtestop_underscore"
	| VBINOP "shape" "vbinop_underscore"
	| VUNOP "shape" "vunop_underscore"
	| VVTESTOP "vectype" "vvtestop"
	| VVTERNOP "vectype" "vvternop"
	| VVBINOP "vectype" "vvbinop"
	| VVUNOP "vectype" "vvunop"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:519.1-520.22 *)
datatype instr_st1 =
	  VCONST "vectype" "vec_underscore"
	| instr_st1_EXTEND "numtype" "n"
	| CVTOP "numtype" "numtype" "cvtop"
	| RELOP "numtype" "relop_underscore"
	| TESTOP "numtype" "testop_underscore"
	| BINOP "numtype" "binop_underscore"
	| UNOP "numtype" "unop_underscore"
	| res_CONST "numtype" "num_underscore"
	| RETURN

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:519.1-520.22 *)
datatype instr_st0 =
	  CALL_INDIRECT "tableidx" "typeidx"
	| CALL "funcidx"
	| BR_TABLE "(labelidx list)" "labelidx"
	| BR_IF "labelidx"
	| BR "labelidx"
	| SELECT "((valtype list) option)"
	| DROP
	| UNREACHABLE
	| NOP

(* Mutual Recursion at: ../specification/wasm-2.0/1-syntax.spectec:519.1-520.22 *)
datatype instr =
	  instr_sc0 "instr_st0"
	| instr_sc1 "instr_st1"
	| instr_sc2 "instr_st2"
	| instr_sc3 "instr_st3"
	| instr_sc4 "instr_st4"
	| instr_sc5 "instr_st5"
	| instr_sc6 "instr_st6"
	| instr_sc7 "instr_st7"

and

instr_st7 =
	  IFELSE "blocktype" "(instr list)" "(instr list)"
	| LOOP "blocktype" "(instr list)"
	| BLOCK "blocktype" "(instr list)"
	| DATA_DROP "dataidx"
	| MEMORY_INIT "dataidx"

(* Mutual Recursion at: ../specification/wasm-2.0/1-syntax.spectec:519.1-520.22 *)
inductive wf_instr :: "instr ⇒ bool" where
	  instr_case_0 :
		"wf_instr (instr_sc0 NOP)"
	| instr_case_1 :
		"wf_instr (instr_sc0 UNREACHABLE)"
	| instr_case_2 :
		"wf_instr (instr_sc0 DROP)"
	| instr_case_3 :
		"wf_instr (instr_sc0 (SELECT valtype_lst_opt))"
	| instr_case_4 :
		"(wf_blocktype v_blocktype) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_instr (instr_sc7 (BLOCK v_blocktype instr_lst))"
	| instr_case_5 :
		"(wf_blocktype v_blocktype) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_instr (instr_sc7 (LOOP v_blocktype instr_lst))"
	| instr_case_6 :
		"(wf_blocktype v_blocktype) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 list_all (λ (instr_lst_0 :: instr). (wf_instr instr_lst_0)) instr_lst_0 ⟹
		 wf_instr (instr_sc7 (IFELSE v_blocktype instr_lst instr_lst_0))"
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
		"(wf_uN 32 v_funcidx) ⟹
		 wf_instr (instr_sc0 (CALL v_funcidx))"
	| instr_case_11 :
		"(wf_uN 32 v_tableidx) ⟹
		 (wf_uN 32 v_typeidx) ⟹
		 wf_instr (instr_sc0 (CALL_INDIRECT v_tableidx v_typeidx))"
	| instr_case_12 :
		"wf_instr (instr_sc1 RETURN)"
	| instr_case_13 :
		"(wf_num_underscore v_numtype var_0) ⟹
		 wf_instr (instr_sc1 (res_CONST v_numtype var_0))"
	| instr_case_14 :
		"(wf_unop_underscore v_numtype var_0) ⟹
		 wf_instr (instr_sc1 (UNOP v_numtype var_0))"
	| instr_case_15 :
		"(wf_binop_underscore v_numtype var_0) ⟹
		 wf_instr (instr_sc1 (BINOP v_numtype var_0))"
	| instr_case_16 :
		"(wf_testop_underscore v_numtype var_0) ⟹
		 wf_instr (instr_sc1 (TESTOP v_numtype var_0))"
	| instr_case_17 :
		"(wf_relop_underscore v_numtype var_0) ⟹
		 wf_instr (instr_sc1 (RELOP v_numtype var_0))"
	| instr_case_18 :
		"(numtype_1 ≠ numtype_2) ⟹
		 wf_instr (instr_sc1 (CVTOP numtype_1 numtype_2 v_cvtop))"
	| instr_case_19 :
		"wf_instr (instr_sc1 (instr_st1_EXTEND v_numtype v_n))"
	| instr_case_20 :
		"((size (valtype_vectype v_vectype)) ≠ None) ⟹
		 (wf_uN (the ((size (valtype_vectype v_vectype)))) var_0) ⟹
		 wf_instr (instr_sc1 (VCONST v_vectype var_0))"
	| instr_case_21 :
		"wf_instr (instr_sc2 (VVUNOP v_vectype v_vvunop))"
	| instr_case_22 :
		"wf_instr (instr_sc2 (VVBINOP v_vectype v_vvbinop))"
	| instr_case_23 :
		"wf_instr (instr_sc2 (VVTERNOP v_vectype v_vvternop))"
	| instr_case_24 :
		"wf_instr (instr_sc2 (VVTESTOP v_vectype v_vvtestop))"
	| instr_case_25 :
		"(wf_shape v_shape) ⟹
		 (wf_vunop_underscore v_shape var_0) ⟹
		 wf_instr (instr_sc2 (VUNOP v_shape var_0))"
	| instr_case_26 :
		"(wf_shape v_shape) ⟹
		 (wf_vbinop_underscore v_shape var_0) ⟹
		 wf_instr (instr_sc2 (VBINOP v_shape var_0))"
	| instr_case_27 :
		"(wf_shape v_shape) ⟹
		 (wf_vtestop_underscore v_shape var_0) ⟹
		 wf_instr (instr_sc2 (VTESTOP v_shape var_0))"
	| instr_case_28 :
		"(wf_shape v_shape) ⟹
		 (wf_vrelop_underscore v_shape var_0) ⟹
		 wf_instr (instr_sc2 (VRELOP v_shape var_0))"
	| instr_case_29 :
		"(wf_ishape v_ishape) ⟹
		 (wf_vshiftop_underscore v_ishape var_0) ⟹
		 wf_instr (instr_sc2 (VSHIFTOP v_ishape var_0))"
	| instr_case_30 :
		"(wf_ishape v_ishape) ⟹
		 wf_instr (instr_sc3 (VBITMASK v_ishape))"
	| instr_case_31 :
		"(wf_ishape v_ishape) ⟹
		 (v_ishape = (ishape_X Jnn_I8 (mk_dim 16))) ⟹
		 wf_instr (instr_sc3 (VSWIZZLE v_ishape))"
	| instr_case_32 :
		"(wf_ishape v_ishape) ⟹
		 list_all (λ (v_laneidx :: laneidx). (wf_uN 8 v_laneidx)) laneidx_lst ⟹
		 ((v_ishape = (ishape_X Jnn_I8 (mk_dim 16))) ∧ ((length laneidx_lst) = 16)) ⟹
		 wf_instr (instr_sc3 (VSHUFFLE v_ishape laneidx_lst))"
	| instr_case_33 :
		"(wf_shape v_shape) ⟹
		 wf_instr (instr_sc3 (VSPLAT v_shape))"
	| instr_case_34 :
		"(wf_shape v_shape) ⟹
		 (wf_uN 8 v_laneidx) ⟹
		 (((fun_lanetype v_shape) = (lanetype_numtype v_numtype)) ⟷ (sx_opt = None)) ⟹
		 wf_instr (instr_sc3 (VEXTRACT_LANE v_shape sx_opt v_laneidx))"
	| instr_case_35 :
		"(wf_shape v_shape) ⟹
		 (wf_uN 8 v_laneidx) ⟹
		 wf_instr (instr_sc3 (VREPLACE_LANE v_shape v_laneidx))"
	| instr_case_36 :
		"(wf_ishape ishape_1) ⟹
		 (wf_ishape ishape_2) ⟹
		 (wf_vextunop_underscore ishape_1 var_0) ⟹
		 ((lsize (fun_lanetype (shape_ishape ishape_1))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))) ⟹
		 wf_instr (instr_sc3 (VEXTUNOP ishape_1 ishape_2 var_0))"
	| instr_case_37 :
		"(wf_ishape ishape_1) ⟹
		 (wf_ishape ishape_2) ⟹
		 (wf_vextbinop_underscore ishape_1 var_0) ⟹
		 ((lsize (fun_lanetype (shape_ishape ishape_1))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))) ⟹
		 wf_instr (instr_sc3 (VEXTBINOP ishape_1 ishape_2 var_0))"
	| instr_case_38 :
		"(wf_ishape ishape_1) ⟹
		 (wf_ishape ishape_2) ⟹
		 (((lsize (fun_lanetype (shape_ishape ishape_2))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_1))))) ∧ ((2 * (lsize (fun_lanetype (shape_ishape ishape_1)))) ≤ 32)) ⟹
		 wf_instr (instr_sc3 (VNARROW ishape_1 ishape_2 v_sx))"
	| instr_case_39 :
		"(wf_shape v_shape) ⟹
		 (wf_shape shape_0) ⟹
		 wf_instr (instr_sc4 (VCVTOP v_shape shape_0 v_vcvtop))"
	| instr_case_40 :
		"wf_instr (instr_sc4 (REF_NULL v_reftype))"
	| instr_case_41 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_instr (instr_sc4 (REF_FUNC v_funcidx))"
	| instr_case_42 :
		"wf_instr (instr_sc4 REF_IS_NULL)"
	| instr_case_43 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_instr (instr_sc4 (LOCAL_GET v_localidx))"
	| instr_case_44 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_instr (instr_sc4 (LOCAL_SET v_localidx))"
	| instr_case_45 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_instr (instr_sc4 (LOCAL_TEE v_localidx))"
	| instr_case_46 :
		"(wf_uN 32 v_globalidx) ⟹
		 wf_instr (instr_sc4 (GLOBAL_GET v_globalidx))"
	| instr_case_47 :
		"(wf_uN 32 v_globalidx) ⟹
		 wf_instr (instr_sc4 (GLOBAL_SET v_globalidx))"
	| instr_case_48 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_instr (instr_sc5 (TABLE_GET v_tableidx))"
	| instr_case_49 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_instr (instr_sc5 (TABLE_SET v_tableidx))"
	| instr_case_50 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_instr (instr_sc5 (TABLE_SIZE v_tableidx))"
	| instr_case_51 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_instr (instr_sc5 (TABLE_GROW v_tableidx))"
	| instr_case_52 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_instr (instr_sc5 (TABLE_FILL v_tableidx))"
	| instr_case_53 :
		"(wf_uN 32 v_tableidx) ⟹
		 (wf_uN 32 tableidx_0) ⟹
		 wf_instr (instr_sc5 (TABLE_COPY v_tableidx tableidx_0))"
	| instr_case_54 :
		"(wf_uN 32 v_tableidx) ⟹
		 (wf_uN 32 v_elemidx) ⟹
		 wf_instr (instr_sc5 (TABLE_INIT v_tableidx v_elemidx))"
	| instr_case_55 :
		"(wf_uN 32 v_elemidx) ⟹
		 wf_instr (instr_sc5 (ELEM_DROP v_elemidx))"
	| instr_case_56 :
		"list_all (λ (var_0 :: loadop_underscore). (wf_loadop_underscore v_numtype var_0)) (option_to_list var_0) ⟹
		 (wf_memarg v_memarg) ⟹
		 wf_instr (instr_sc5 (LOAD v_numtype var_0 v_memarg))"
	| instr_case_57 :
		"list_all (λ (v_sz :: sz). (wf_sz v_sz)) (option_to_list sz_opt) ⟹
		 (wf_memarg v_memarg) ⟹
		 ((Inn_opt = None) ⟷ (numtype_opt = None)) ⟹
		 ((Inn_opt = None) ⟷ (sz_opt = None)) ⟹
		 list_all3 (λ (v_Inn :: Inn) (v_numtype :: numtype) (v_sz :: sz). ((v_numtype = (numtype_Inn v_Inn)) ∧ ((proj_sz_0 v_sz) < (sizenn (numtype_Inn v_Inn))))) (option_to_list Inn_opt) (option_to_list numtype_opt) (option_to_list sz_opt) ⟹
		 wf_instr (instr_sc6 (STORE v_numtype sz_opt v_memarg))"
	| instr_case_58 :
		"(wf_memarg v_memarg) ⟹
		 wf_instr (instr_sc6 (VLOAD v_vectype vloadop_opt v_memarg))"
	| instr_case_59 :
		"(wf_sz v_sz) ⟹
		 (wf_memarg v_memarg) ⟹
		 (wf_uN 8 v_laneidx) ⟹
		 wf_instr (instr_sc6 (VLOAD_LANE v_vectype v_sz v_memarg v_laneidx))"
	| instr_case_60 :
		"(wf_memarg v_memarg) ⟹
		 wf_instr (instr_sc6 (VSTORE v_vectype v_memarg))"
	| instr_case_61 :
		"(wf_sz v_sz) ⟹
		 (wf_memarg v_memarg) ⟹
		 (wf_uN 8 v_laneidx) ⟹
		 wf_instr (instr_sc6 (VSTORE_LANE v_vectype v_sz v_memarg v_laneidx))"
	| instr_case_62 :
		"wf_instr (instr_sc6 MEMORY_SIZE)"
	| instr_case_63 :
		"wf_instr (instr_sc6 MEMORY_GROW)"
	| instr_case_64 :
		"wf_instr (instr_sc6 MEMORY_FILL)"
	| instr_case_65 :
		"wf_instr (instr_sc6 MEMORY_COPY)"
	| instr_case_66 :
		"(wf_uN 32 v_dataidx) ⟹
		 wf_instr (instr_sc7 (MEMORY_INIT v_dataidx))"
	| instr_case_67 :
		"(wf_uN 32 v_dataidx) ⟹
		 wf_instr (instr_sc7 (DATA_DROP v_dataidx))"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:523.1-524.9 *)
type_synonym expr = "(instr list)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:536.1-536.59 *)
datatype elemmode =
	  ACTIVE "tableidx" "expr"
	| PASSIVE
	| DECLARE

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:536.8-536.16 *)
inductive wf_elemmode :: "elemmode ⇒ bool" where
	  elemmode_case_0 :
		"(wf_uN 32 v_tableidx) ⟹
		 list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_elemmode (ACTIVE v_tableidx v_expr)"
	| elemmode_case_1 :
		"wf_elemmode PASSIVE"
	| elemmode_case_2 :
		"wf_elemmode DECLARE"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:537.1-537.47 *)
datatype datamode =
	  datamode_ACTIVE "memidx" "expr"
	| datamode_PASSIVE

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:537.8-537.16 *)
inductive wf_datamode :: "datamode ⇒ bool" where
	  datamode_case_0 :
		"(wf_uN 32 v_memidx) ⟹
		 list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_datamode (datamode_ACTIVE v_memidx v_expr)"
	| datamode_case_1 :
		"wf_datamode datamode_PASSIVE"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:539.1-540.16 *)
datatype type =
	  res_TYPE "functype"
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:541.1-542.16 *)
datatype local =
	  LOCAL "valtype"
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:543.1-544.27 *)
datatype func =
	  func_FUNC "typeidx" "(local list)" "expr"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:543.8-543.12 *)
inductive wf_func :: "func ⇒ bool" where
	  func_case_0 :
		"(wf_uN 32 v_typeidx) ⟹
		 list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_func (func_FUNC v_typeidx local_lst v_expr)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:545.1-546.25 *)
datatype global =
	  global_GLOBAL "globaltype" "expr"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:545.8-545.14 *)
inductive wf_global :: "global ⇒ bool" where
	  global_case_0 :
		"list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_global (global_GLOBAL v_globaltype v_expr)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:547.1-548.18 *)
datatype table =
	  table_TABLE "tabletype"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:547.8-547.13 *)
inductive wf_table :: "table ⇒ bool" where
	  table_case_0 :
		"(wf_tabletype v_tabletype) ⟹
		 wf_table (table_TABLE v_tabletype)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:549.1-550.17 *)
datatype mem =
	  MEMORY "memtype"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:549.8-549.11 *)
inductive wf_mem :: "mem ⇒ bool" where
	  mem_case_0 :
		"(wf_memtype v_memtype) ⟹
		 wf_mem (MEMORY v_memtype)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:551.1-552.30 *)
datatype elem =
	  ELEM "reftype" "(expr list)" "elemmode"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:551.8-551.12 *)
inductive wf_elem :: "elem ⇒ bool" where
	  elem_case_0 :
		"list_all (λ (v_expr :: expr). list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr) expr_lst ⟹
		 (wf_elemmode v_elemmode) ⟹
		 wf_elem (ELEM v_reftype expr_lst v_elemmode)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:553.1-554.22 *)
datatype data =
	  DATA "(byte list)" "datamode"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:553.8-553.12 *)
inductive wf_data :: "data ⇒ bool" where
	  data_case_0 :
		"list_all (λ (v_byte :: byte). (wf_byte v_byte)) byte_lst ⟹
		 (wf_datamode v_datamode) ⟹
		 wf_data (DATA byte_lst v_datamode)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:555.1-556.16 *)
datatype start =
	  START "funcidx"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:555.8-555.13 *)
inductive wf_start :: "start ⇒ bool" where
	  start_case_0 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_start (START v_funcidx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:558.1-559.66 *)
datatype externidx =
	  externidx_FUNC "funcidx"
	| externidx_GLOBAL "globalidx"
	| externidx_TABLE "tableidx"
	| externidx_MEM "memidx"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:558.8-558.17 *)
inductive wf_externidx :: "externidx ⇒ bool" where
	  externidx_case_0 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_externidx (externidx_FUNC v_funcidx)"
	| externidx_case_1 :
		"(wf_uN 32 v_globalidx) ⟹
		 wf_externidx (externidx_GLOBAL v_globalidx)"
	| externidx_case_2 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_externidx (externidx_TABLE v_tableidx)"
	| externidx_case_3 :
		"(wf_uN 32 v_memidx) ⟹
		 wf_externidx (externidx_MEM v_memidx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:560.1-561.24 *)
datatype export =
	  EXPORT "name" "externidx"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:560.8-560.14 *)
inductive wf_export :: "export ⇒ bool" where
	  export_case_0 :
		"(wf_name v_name) ⟹
		 (wf_externidx v_externidx) ⟹
		 wf_export (EXPORT v_name v_externidx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:562.1-563.30 *)
datatype import =
	  IMPORT "name" "name" "externtype"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:562.8-562.14 *)
inductive wf_import :: "import ⇒ bool" where
	  import_case_0 :
		"(wf_name v_name) ⟹
		 (wf_name name_0) ⟹
		 (wf_externtype v_externtype) ⟹
		 wf_import (IMPORT v_name name_0 v_externtype)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:565.1-566.76 *)
datatype module =
	  MODULE "(type list)" "(import list)" "(func list)" "(global list)" "(table list)" "(mem list)" "(elem list)" "(data list)" "(start option)" "(export list)"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:565.8-565.14 *)
inductive wf_module :: "module ⇒ bool" where
	  module_case_0 :
		"list_all (λ (v_import :: import). (wf_import v_import)) import_lst ⟹
		 list_all (λ (v_func :: func). (wf_func v_func)) func_lst ⟹
		 list_all (λ (v_global :: global). (wf_global v_global)) global_lst ⟹
		 list_all (λ (v_table :: table). (wf_table v_table)) table_lst ⟹
		 list_all (λ (v_mem :: mem). (wf_mem v_mem)) mem_lst ⟹
		 list_all (λ (v_elem :: elem). (wf_elem v_elem)) elem_lst ⟹
		 list_all (λ (v_data :: data). (wf_data v_data)) data_lst ⟹
		 list_all (λ (v_start :: start). (wf_start v_start)) (option_to_list start_opt) ⟹
		 list_all (λ (v_export :: export). (wf_export v_export)) export_lst ⟹
		 wf_module (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)"

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.1-7.59 *)
inductive fun_concat_bytes :: "((byte list) list) ⇒ (byte list) ⇒ bool" where
	  fun_concat_bytes_case_0 :
		"fun_concat_bytes [] []"
	| fun_concat_bytes_case_1 :
		"(fun_concat_bytes b'_lst_lst var_0) ⟹
		 fun_concat_bytes ([b_lst] @ b'_lst_lst) (b_lst @ var_0)"

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:28.1-28.32 *)
function (sequential) unpack :: "lanetype ⇒ numtype" where
		  "unpack lanetype_I32 = I32"
		| "unpack lanetype_I64 = I64"
		| "unpack lanetype_F32 = F32"
		| "unpack lanetype_F64 = F64"
		| "unpack lanetype_I8 = I32"
		| "unpack lanetype_I16 = I32"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:44.1-44.54 *)
function (sequential) shunpack :: "shape ⇒ numtype" where
		  "shunpack (X v_Lnn (mk_dim v_N)) = (unpack v_Lnn)"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:51.1-51.64 *)
inductive fun_funcsxt :: "(externtype list) ⇒ (functype list) ⇒ bool" where
	  fun_funcsxt_case_0 :
		"fun_funcsxt [] []"
	| fun_funcsxt_case_1 :
		"(fun_funcsxt xt_lst var_0) ⟹
		 fun_funcsxt ([(FUNC ft)] @ xt_lst) ([ft] @ var_0)"
	| fun_funcsxt_case_2 :
		"(fun_funcsxt xt_lst var_0) ⟹
		 fun_funcsxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:52.1-52.66 *)
inductive fun_globalsxt :: "(externtype list) ⇒ (globaltype list) ⇒ bool" where
	  fun_globalsxt_case_0 :
		"fun_globalsxt [] []"
	| fun_globalsxt_case_1 :
		"(fun_globalsxt xt_lst var_0) ⟹
		 fun_globalsxt ([(GLOBAL gt)] @ xt_lst) ([gt] @ var_0)"
	| fun_globalsxt_case_2 :
		"(fun_globalsxt xt_lst var_0) ⟹
		 fun_globalsxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.1-53.65 *)
inductive fun_tablesxt :: "(externtype list) ⇒ (tabletype list) ⇒ bool" where
	  fun_tablesxt_case_0 :
		"fun_tablesxt [] []"
	| fun_tablesxt_case_1 :
		"(fun_tablesxt xt_lst var_0) ⟹
		 fun_tablesxt ([(TABLE tt)] @ xt_lst) ([tt] @ var_0)"
	| fun_tablesxt_case_2 :
		"(fun_tablesxt xt_lst var_0) ⟹
		 fun_tablesxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63 *)
inductive fun_memsxt :: "(externtype list) ⇒ (memtype list) ⇒ bool" where
	  fun_memsxt_case_0 :
		"fun_memsxt [] []"
	| fun_memsxt_case_1 :
		"(fun_memsxt xt_lst var_0) ⟹
		 fun_memsxt ([(MEM mt)] @ xt_lst) ([mt] @ var_0)"
	| fun_memsxt_case_2 :
		"(fun_memsxt xt_lst var_0) ⟹
		 fun_memsxt ([v_externtype] @ xt_lst) var_0"

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:80.1-80.61 *)
function (sequential) dataidx_instr :: "instr ⇒ (dataidx list)" where
		  "dataidx_instr (instr_sc7 (MEMORY_INIT x)) = [x]"
		| "dataidx_instr (instr_sc7 (DATA_DROP x)) = [x]"
		| "dataidx_instr res_in = []"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63 *)
inductive fun_dataidx_instrs :: "(instr list) ⇒ (dataidx list) ⇒ bool" where
	  fun_dataidx_instrs_case_0 :
		"fun_dataidx_instrs [] []"
	| fun_dataidx_instrs_case_1 :
		"(fun_dataidx_instrs instr'_lst var_0) ⟹
		 fun_dataidx_instrs ([v_instr] @ instr'_lst) ((dataidx_instr v_instr) @ var_0)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:89.6-89.19 *)
inductive fun_dataidx_expr :: "expr ⇒ (dataidx list) ⇒ bool" where
	  fun_dataidx_expr_case_0 :
		"(fun_dataidx_instrs in_lst var_0) ⟹
		 fun_dataidx_expr in_lst var_0"

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:92.6-92.19 *)
inductive fun_dataidx_func :: "func ⇒ (dataidx list) ⇒ bool" where
	  fun_dataidx_func_case_0 :
		"(fun_dataidx_expr e var_0) ⟹
		 fun_dataidx_func (func_FUNC x loc_lst e) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61 *)
inductive fun_dataidx_funcs :: "(func list) ⇒ (dataidx list) ⇒ bool" where
	  fun_dataidx_funcs_case_0 :
		"fun_dataidx_funcs [] []"
	| fun_dataidx_funcs_case_1 :
		"(fun_dataidx_funcs func'_lst var_1) ⟹
		 (fun_dataidx_func v_func var_0) ⟹
		 fun_dataidx_funcs ([v_func] @ func'_lst) (var_0 @ var_1)"

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:106.1-106.35 *)
definition memarg0 :: "memarg" where
	"memarg0 = ⦇ ALIGN = (mk_uN 0), OFFSET = (mk_uN 0) ⦈"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:7.1-7.41 *)
axiomatization s33_to_u32 :: "s33 ⇒ u32"

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:9.1-9.22 *)
function (sequential) res_bool :: "bool ⇒ nat" where
		  "res_bool False = 0"
		| "res_bool True = 1"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:13.1-13.23 *)
axiomatization truncz :: "nat ⇒ nat"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:20.6-20.14 *)
inductive fun_signed_underscore :: "N ⇒ nat ⇒ nat ⇒ bool" where
	  fun_signed__case_0 :
		"(i < (2 ^ (((v_N :: nat) - (1 :: nat)) :: nat))) ⟹
		 fun_signed_underscore v_N i (i :: nat)"
	| fun_signed__case_1 :
		"(((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) ≤ i) ∧ (i < (2 ^ v_N))) ⟹
		 fun_signed_underscore v_N i ((i :: nat) - ((2 ^ v_N) :: nat))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:24.6-24.18 *)
inductive fun_inv_signed_underscore :: "N ⇒ nat ⇒ nat ⇒ bool" where
	  fun_inv_signed__case_0 :
		"(((0 :: nat) ≤ i) ∧ (i < ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat))) ⟹
		 fun_inv_signed_underscore v_N i (i :: nat)"
	| fun_inv_signed__case_1 :
		"(((0 - ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat)) ≤ i) ∧ (i < (0 :: nat))) ⟹
		 fun_inv_signed_underscore v_N i ((i + ((2 ^ v_N) :: nat)) :: nat)"

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:31.1-31.61 *)
function (sequential) sat_u_underscore :: "N ⇒ nat ⇒ nat" where
		  "sat_u_underscore v_N i = (if (i < (0 :: nat)) then 0 else (if (i > (((2 ^ v_N) :: nat) - (1 :: nat))) then ((((2 ^ v_N) :: nat) - (1 :: nat)) :: nat) else (i :: nat)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:36.1-36.61 *)
function (sequential) sat_s_underscore :: "N ⇒ nat ⇒ nat" where
		  "sat_s_underscore v_N i = (if (i < (0 - ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat))) then (0 - ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat)) else (if (i > (((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat) - (1 :: nat))) then (((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat) - (1 :: nat)) else i))"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:56.1-56.89 *)
axiomatization extend__underscore :: "M ⇒ N ⇒ sx ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:224.1-224.30 *)
axiomatization fabs_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:227.1-227.31 *)
axiomatization fceil_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:228.1-228.32 *)
axiomatization ffloor_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:230.1-230.34 *)
axiomatization fnearest_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:225.1-225.30 *)
axiomatization fneg_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:226.1-226.31 *)
axiomatization fsqrt_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:229.1-229.32 *)
axiomatization ftrunc_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:120.1-120.29 *)
axiomatization iclz_underscore :: "N ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:121.1-121.29 *)
axiomatization ictz_underscore :: "N ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:122.1-122.32 *)
axiomatization ipopcnt_underscore :: "N ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:55.1-55.33 *)
axiomatization wrap__underscore :: "M ⇒ N ⇒ iN ⇒ iN"

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32 *)
function (sequential) fun_unop__I64 :: "unop_underscore ⇒ num_underscore ⇒ (num_underscore list)" where
		  "fun_unop__I64 (mk_unop__0 Inn_I64 CLZ) (mk_num__0 Inn_I64 v_iN) = [(mk_num__0 Inn_I64 (iclz_underscore (sizenn (numtype_Inn Inn_I64)) v_iN))]"
		| "fun_unop__I64 (mk_unop__0 Inn_I64 CTZ) (mk_num__0 Inn_I64 v_iN) = [(mk_num__0 Inn_I64 (ictz_underscore (sizenn (numtype_Inn Inn_I64)) v_iN))]"
		| "fun_unop__I64 (mk_unop__0 Inn_I64 POPCNT) (mk_num__0 Inn_I64 v_iN) = [(mk_num__0 Inn_I64 (ipopcnt_underscore (sizenn (numtype_Inn Inn_I64)) v_iN))]"
		| "fun_unop__I64 (mk_unop__0 Inn_I64 (EXTEND v_M)) (mk_num__0 Inn_I64 v_iN) = [(mk_num__0 Inn_I64 (extend__underscore v_M (sizenn (numtype_Inn Inn_I64)) S (wrap__underscore (sizenn (numtype_Inn Inn_I64)) v_M v_iN)))]"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32 *)
function (sequential) fun_unop__I32 :: "unop_underscore ⇒ num_underscore ⇒ (num_underscore list)" where
		  "fun_unop__I32 (mk_unop__0 Inn_I32 CLZ) (mk_num__0 Inn_I32 v_iN) = [(mk_num__0 Inn_I32 (iclz_underscore (sizenn (numtype_Inn Inn_I32)) v_iN))]"
		| "fun_unop__I32 (mk_unop__0 Inn_I32 CTZ) (mk_num__0 Inn_I32 v_iN) = [(mk_num__0 Inn_I32 (ictz_underscore (sizenn (numtype_Inn Inn_I32)) v_iN))]"
		| "fun_unop__I32 (mk_unop__0 Inn_I32 POPCNT) (mk_num__0 Inn_I32 v_iN) = [(mk_num__0 Inn_I32 (ipopcnt_underscore (sizenn (numtype_Inn Inn_I32)) v_iN))]"
		| "fun_unop__I32 (mk_unop__0 Inn_I32 (EXTEND v_M)) (mk_num__0 Inn_I32 v_iN) = [(mk_num__0 Inn_I32 (extend__underscore v_M (sizenn (numtype_Inn Inn_I32)) S (wrap__underscore (sizenn (numtype_Inn Inn_I32)) v_M v_iN)))]"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32 *)
function (sequential) fun_unop__F64 :: "unop_underscore ⇒ num_underscore ⇒ (num_underscore list)" where
		  "fun_unop__F64 (mk_unop__1 Fnn_F64 ABS) (mk_num__1 Fnn_F64 v_fN) = (map (λ (iter_0_2 :: fN). (mk_num__1 Fnn_F64 iter_0_2)) (fabs_underscore (sizenn (numtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 unop_Fnn_NEG) (mk_num__1 Fnn_F64 v_fN) = (map (λ (iter_0_4 :: fN). (mk_num__1 Fnn_F64 iter_0_4)) (fneg_underscore (sizenn (numtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 SQRT) (mk_num__1 Fnn_F64 v_fN) = (map (λ (iter_0_6 :: fN). (mk_num__1 Fnn_F64 iter_0_6)) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 CEIL) (mk_num__1 Fnn_F64 v_fN) = (map (λ (iter_0_8 :: fN). (mk_num__1 Fnn_F64 iter_0_8)) (fceil_underscore (sizenn (numtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 FLOOR) (mk_num__1 Fnn_F64 v_fN) = (map (λ (iter_0_10 :: fN). (mk_num__1 Fnn_F64 iter_0_10)) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 TRUNC) (mk_num__1 Fnn_F64 v_fN) = (map (λ (iter_0_12 :: fN). (mk_num__1 Fnn_F64 iter_0_12)) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 NEAREST) (mk_num__1 Fnn_F64 v_fN) = (map (λ (iter_0_14 :: fN). (mk_num__1 Fnn_F64 iter_0_14)) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F64)) v_fN))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32 *)
function (sequential) fun_unop__F32 :: "unop_underscore ⇒ num_underscore ⇒ (num_underscore list)" where
		  "fun_unop__F32 (mk_unop__1 Fnn_F32 ABS) (mk_num__1 Fnn_F32 v_fN) = (map (λ (iter_0_1 :: fN). (mk_num__1 Fnn_F32 iter_0_1)) (fabs_underscore (sizenn (numtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 unop_Fnn_NEG) (mk_num__1 Fnn_F32 v_fN) = (map (λ (iter_0_3 :: fN). (mk_num__1 Fnn_F32 iter_0_3)) (fneg_underscore (sizenn (numtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 SQRT) (mk_num__1 Fnn_F32 v_fN) = (map (λ (iter_0_5 :: fN). (mk_num__1 Fnn_F32 iter_0_5)) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 CEIL) (mk_num__1 Fnn_F32 v_fN) = (map (λ (iter_0_7 :: fN). (mk_num__1 Fnn_F32 iter_0_7)) (fceil_underscore (sizenn (numtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 FLOOR) (mk_num__1 Fnn_F32 v_fN) = (map (λ (iter_0_9 :: fN). (mk_num__1 Fnn_F32 iter_0_9)) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 TRUNC) (mk_num__1 Fnn_F32 v_fN) = (map (λ (iter_0_11 :: fN). (mk_num__1 Fnn_F32 iter_0_11)) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 NEAREST) (mk_num__1 Fnn_F32 v_fN) = (map (λ (iter_0_13 :: fN). (mk_num__1 Fnn_F32 iter_0_13)) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F32)) v_fN))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32 *)
function (sequential) fun_unop_underscore :: "numtype ⇒ unop_underscore ⇒ num_underscore ⇒ (num_underscore list)" where
		  "fun_unop_underscore I64 v_unop_underscore v_num_underscore = (fun_unop__I64 v_unop_underscore v_num_underscore)"
		| "fun_unop_underscore I32 v_unop_underscore v_num_underscore = (fun_unop__I32 v_unop_underscore v_num_underscore)"
		| "fun_unop_underscore F64 v_unop_underscore v_num_underscore = (fun_unop__F64 v_unop_underscore v_num_underscore)"
		| "fun_unop_underscore F32 v_unop_underscore v_num_underscore = (fun_unop__F32 v_unop_underscore v_num_underscore)"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:215.1-215.37 *)
axiomatization fadd_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:223.1-223.42 *)
axiomatization fcopysign_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:218.1-218.37 *)
axiomatization fdiv_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:220.1-220.37 *)
axiomatization fmax_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:219.1-219.37 *)
axiomatization fmin_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:217.1-217.37 *)
axiomatization fmul_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:216.1-216.37 *)
axiomatization fsub_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:105.1-105.36 *)
function (sequential) iadd_underscore :: "N ⇒ iN ⇒ iN ⇒ iN" where
		  "iadd_underscore v_N i_1 i_2 = (mk_uN (((proj_uN_0 i_1) + (proj_uN_0 i_2)) mod (2 ^ v_N)))"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:112.1-112.36 *)
axiomatization iand_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:108.6-108.12 *)
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

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:107.1-107.36 *)
function (sequential) imul_underscore :: "N ⇒ iN ⇒ iN ⇒ iN" where
		  "imul_underscore v_N i_1 i_2 = (mk_uN (((proj_uN_0 i_1) * (proj_uN_0 i_2)) mod (2 ^ v_N)))"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:114.1-114.35 *)
axiomatization ior_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:109.6-109.12 *)
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

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:118.1-118.37 *)
axiomatization irotl_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:119.1-119.37 *)
axiomatization irotr_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:116.1-116.34 *)
axiomatization ishl_underscore :: "N ⇒ iN ⇒ u32 ⇒ iN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:117.1-117.74 *)
axiomatization ishr_underscore :: "N ⇒ sx ⇒ iN ⇒ u32 ⇒ iN"

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:106.1-106.36 *)
function (sequential) isub_underscore :: "N ⇒ iN ⇒ iN ⇒ iN" where
		  "isub_underscore v_N i_1 i_2 = (mk_uN ((((((2 ^ v_N) + (proj_uN_0 i_1)) :: nat) - ((proj_uN_0 i_2) :: nat)) mod ((2 ^ v_N) :: nat)) :: nat))"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:115.1-115.36 *)
axiomatization ixor_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:46.6-46.13 *)
inductive fun_binop_underscore :: "numtype ⇒ binop_underscore ⇒ num_underscore ⇒ num_underscore ⇒ (num_underscore list) ⇒ bool" where
	  fun_binop__case_0 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 ADD) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (iadd_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_1 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 ADD) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (iadd_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_2 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 SUB) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (isub_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_3 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 SUB) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (isub_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_4 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 MUL) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (imul_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_5 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 MUL) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (imul_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_6 :
		"(fun_idiv_underscore (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_binop_underscore I32 (mk_binop__0 Inn_I32 (DIV v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (list_underscore  (map_option (λ (iter_0_15 :: iN). (mk_num__0 Inn_I32 iter_0_15)) var_0))"
	| fun_binop__case_7 :
		"(fun_idiv_underscore (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_binop_underscore I64 (mk_binop__0 Inn_I64 (DIV v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (list_underscore  (map_option (λ (iter_0_16 :: iN). (mk_num__0 Inn_I64 iter_0_16)) var_0))"
	| fun_binop__case_8 :
		"(fun_irem_underscore (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_binop_underscore I32 (mk_binop__0 Inn_I32 (REM v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (list_underscore  (map_option (λ (iter_0_17 :: iN). (mk_num__0 Inn_I32 iter_0_17)) var_0))"
	| fun_binop__case_9 :
		"(fun_irem_underscore (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_binop_underscore I64 (mk_binop__0 Inn_I64 (REM v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (list_underscore  (map_option (λ (iter_0_18 :: iN). (mk_num__0 Inn_I64 iter_0_18)) var_0))"
	| fun_binop__case_10 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 AND) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (iand_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_11 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 AND) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (iand_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_12 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 OR) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (ior_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_13 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 OR) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (ior_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_14 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 XOR) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (ixor_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_15 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 XOR) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (ixor_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_16 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 SHL) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (ishl_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 (mk_uN (proj_uN_0 iN_2))))]"
	| fun_binop__case_17 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 SHL) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (ishl_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 (mk_uN (proj_uN_0 iN_2))))]"
	| fun_binop__case_18 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 (SHR v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (ishr_underscore (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 (mk_uN (proj_uN_0 iN_2))))]"
	| fun_binop__case_19 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 (SHR v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (ishr_underscore (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 (mk_uN (proj_uN_0 iN_2))))]"
	| fun_binop__case_20 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 ROTL) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (irotl_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_21 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 ROTL) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (irotl_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_22 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 ROTR) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (irotr_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_23 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 ROTR) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (irotr_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_24 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_ADD) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (map (λ (iter_0_19 :: fN). (mk_num__1 Fnn_F32 iter_0_19)) (fadd_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_25 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_ADD) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (map (λ (iter_0_20 :: fN). (mk_num__1 Fnn_F64 iter_0_20)) (fadd_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_26 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_SUB) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (map (λ (iter_0_21 :: fN). (mk_num__1 Fnn_F32 iter_0_21)) (fsub_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_27 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_SUB) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (map (λ (iter_0_22 :: fN). (mk_num__1 Fnn_F64 iter_0_22)) (fsub_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_28 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_MUL) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (map (λ (iter_0_23 :: fN). (mk_num__1 Fnn_F32 iter_0_23)) (fmul_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_29 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_MUL) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (map (λ (iter_0_24 :: fN). (mk_num__1 Fnn_F64 iter_0_24)) (fmul_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_30 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_DIV) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (map (λ (iter_0_25 :: fN). (mk_num__1 Fnn_F32 iter_0_25)) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_31 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_DIV) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (map (λ (iter_0_26 :: fN). (mk_num__1 Fnn_F64 iter_0_26)) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_32 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 res_MIN) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (map (λ (iter_0_27 :: fN). (mk_num__1 Fnn_F32 iter_0_27)) (fmin_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_33 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 res_MIN) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (map (λ (iter_0_28 :: fN). (mk_num__1 Fnn_F64 iter_0_28)) (fmin_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_34 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 res_MAX) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (map (λ (iter_0_29 :: fN). (mk_num__1 Fnn_F32 iter_0_29)) (fmax_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_35 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 res_MAX) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (map (λ (iter_0_30 :: fN). (mk_num__1 Fnn_F64 iter_0_30)) (fmax_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_36 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 COPYSIGN) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (map (λ (iter_0_31 :: fN). (mk_num__1 Fnn_F32 iter_0_31)) (fcopysign_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_37 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 COPYSIGN) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (map (λ (iter_0_32 :: fN). (mk_num__1 Fnn_F64 iter_0_32)) (fcopysign_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:123.1-123.27 *)
function (sequential) ieqz_underscore :: "N ⇒ iN ⇒ u32" where
		  "ieqz_underscore v_N i_1 = (mk_uN (res_bool ((proj_uN_0 i_1) = 0)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:48.1-49.32 *)
function (sequential) fun_testop_underscore :: "numtype ⇒ testop_underscore ⇒ num_underscore ⇒ num_underscore" where
		  "fun_testop_underscore I32 (mk_testop__0 Inn_I32 EQZ) (mk_num__0 Inn_I32 v_iN) = (mk_num__0 Inn_I32 (ieqz_underscore (sizenn (numtype_Inn Inn_I32)) v_iN))"
		| "fun_testop_underscore I64 (mk_testop__0 Inn_I64 EQZ) (mk_num__0 Inn_I64 v_iN) = (mk_num__0 Inn_I32 (ieqz_underscore (sizenn (numtype_Inn Inn_I64)) v_iN))"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:231.1-231.33 *)
axiomatization feq_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:236.1-236.33 *)
axiomatization fge_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:234.1-234.33 *)
axiomatization fgt_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:235.1-235.33 *)
axiomatization fle_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:233.1-233.33 *)
axiomatization flt_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:232.1-232.33 *)
axiomatization fne_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:125.1-125.33 *)
function (sequential) ieq_underscore :: "N ⇒ iN ⇒ iN ⇒ u32" where
		  "ieq_underscore v_N i_1 i_2 = (mk_uN (res_bool (i_1 = i_2)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:130.6-130.11 *)
inductive fun_ige_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ u32 ⇒ bool" where
	  fun_ige__case_0 :
		"fun_ige_underscore v_N U i_1 i_2 (mk_uN (res_bool ((proj_uN_0 i_1) ≥ (proj_uN_0 i_2))))"
	| fun_ige__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) ⟹
		 fun_ige_underscore v_N S i_1 i_2 (mk_uN (res_bool (var_0 ≥ var_1)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:128.6-128.11 *)
inductive fun_igt_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ u32 ⇒ bool" where
	  fun_igt__case_0 :
		"fun_igt_underscore v_N U i_1 i_2 (mk_uN (res_bool ((proj_uN_0 i_1) > (proj_uN_0 i_2))))"
	| fun_igt__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) ⟹
		 fun_igt_underscore v_N S i_1 i_2 (mk_uN (res_bool (var_0 > var_1)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:129.6-129.11 *)
inductive fun_ile_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ u32 ⇒ bool" where
	  fun_ile__case_0 :
		"fun_ile_underscore v_N U i_1 i_2 (mk_uN (res_bool ((proj_uN_0 i_1) ≤ (proj_uN_0 i_2))))"
	| fun_ile__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) ⟹
		 fun_ile_underscore v_N S i_1 i_2 (mk_uN (res_bool (var_0 ≤ var_1)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:127.6-127.11 *)
inductive fun_ilt_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ u32 ⇒ bool" where
	  fun_ilt__case_0 :
		"fun_ilt_underscore v_N U i_1 i_2 (mk_uN (res_bool ((proj_uN_0 i_1) < (proj_uN_0 i_2))))"
	| fun_ilt__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) ⟹
		 fun_ilt_underscore v_N S i_1 i_2 (mk_uN (res_bool (var_0 < var_1)))"

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:126.1-126.33 *)
function (sequential) ine_underscore :: "N ⇒ iN ⇒ iN ⇒ u32" where
		  "ine_underscore v_N i_1 i_2 = (mk_uN (res_bool (i_1 ≠ i_2)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:50.6-50.13 *)
inductive fun_relop_underscore :: "numtype ⇒ relop_underscore ⇒ num_underscore ⇒ num_underscore ⇒ num_underscore ⇒ bool" where
	  fun_relop__case_0 :
		"fun_relop_underscore I32 (mk_relop__0 Inn_I32 EQ) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 (ieq_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))"
	| fun_relop__case_1 :
		"fun_relop_underscore I64 (mk_relop__0 Inn_I64 EQ) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 (ieq_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))"
	| fun_relop__case_2 :
		"fun_relop_underscore I32 (mk_relop__0 Inn_I32 NE) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 (ine_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))"
	| fun_relop__case_3 :
		"fun_relop_underscore I64 (mk_relop__0 Inn_I64 NE) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 (ine_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))"
	| fun_relop__case_4 :
		"(fun_ilt_underscore (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I32 (mk_relop__0 Inn_I32 (LT v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_5 :
		"(fun_ilt_underscore (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I64 (mk_relop__0 Inn_I64 (LT v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_6 :
		"(fun_igt_underscore (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I32 (mk_relop__0 Inn_I32 (GT v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_7 :
		"(fun_igt_underscore (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I64 (mk_relop__0 Inn_I64 (GT v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_8 :
		"(fun_ile_underscore (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I32 (mk_relop__0 Inn_I32 (LE v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_9 :
		"(fun_ile_underscore (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I64 (mk_relop__0 Inn_I64 (LE v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_10 :
		"(fun_ige_underscore (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I32 (mk_relop__0 Inn_I32 (GE v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_11 :
		"(fun_ige_underscore (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I64 (mk_relop__0 Inn_I64 (GE v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_12 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_EQ) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (feq_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_13 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_EQ) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (feq_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_14 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_NE) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fne_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_15 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_NE) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fne_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_16 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_LT) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (flt_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_17 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_LT) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (flt_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_18 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_GT) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fgt_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_19 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_GT) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fgt_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_20 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_LE) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fle_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_21 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_LE) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fle_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_22 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_GE) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fge_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_23 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_GE) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fge_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:61.1-61.90 *)
axiomatization convert__underscore :: "M ⇒ N ⇒ sx ⇒ iN ⇒ fN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:59.1-59.36 *)
axiomatization demote__underscore :: "M ⇒ N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:60.1-60.37 *)
axiomatization promote__underscore :: "M ⇒ N ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:63.1-63.76 *)
axiomatization reinterpret__underscore :: "numtype ⇒ numtype ⇒ num_underscore ⇒ num_underscore"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:57.1-57.88 *)
axiomatization trunc__underscore :: "M ⇒ N ⇒ sx ⇒ fN ⇒ (iN option)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:58.1-58.93 *)
axiomatization trunc_sat__underscore :: "M ⇒ N ⇒ sx ⇒ fN ⇒ (iN option)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:52.6-52.14 *)
inductive fun_cvtop__underscore :: "numtype ⇒ numtype ⇒ cvtop ⇒ num_underscore ⇒ (num_underscore list) ⇒ bool" where
	  fun_cvtop___case_0 :
		"fun_cvtop__underscore I32 I32 (cvtop_EXTEND v_sx) (mk_num__0 Inn_I32 iN_1) [(mk_num__0 Inn_I32 (extend__underscore (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx iN_1))]"
	| fun_cvtop___case_1 :
		"fun_cvtop__underscore I64 I32 (cvtop_EXTEND v_sx) (mk_num__0 Inn_I64 iN_1) [(mk_num__0 Inn_I32 (extend__underscore (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx iN_1))]"
	| fun_cvtop___case_2 :
		"fun_cvtop__underscore I32 I64 (cvtop_EXTEND v_sx) (mk_num__0 Inn_I32 iN_1) [(mk_num__0 Inn_I64 (extend__underscore (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx iN_1))]"
	| fun_cvtop___case_3 :
		"fun_cvtop__underscore I64 I64 (cvtop_EXTEND v_sx) (mk_num__0 Inn_I64 iN_1) [(mk_num__0 Inn_I64 (extend__underscore (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx iN_1))]"
	| fun_cvtop___case_4 :
		"fun_cvtop__underscore I32 I32 WRAP (mk_num__0 Inn_I32 iN_1) [(mk_num__0 Inn_I32 (wrap__underscore (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I32)) iN_1))]"
	| fun_cvtop___case_5 :
		"fun_cvtop__underscore I64 I32 WRAP (mk_num__0 Inn_I64 iN_1) [(mk_num__0 Inn_I32 (wrap__underscore (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I32)) iN_1))]"
	| fun_cvtop___case_6 :
		"fun_cvtop__underscore I32 I64 WRAP (mk_num__0 Inn_I32 iN_1) [(mk_num__0 Inn_I64 (wrap__underscore (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I64)) iN_1))]"
	| fun_cvtop___case_7 :
		"fun_cvtop__underscore I64 I64 WRAP (mk_num__0 Inn_I64 iN_1) [(mk_num__0 Inn_I64 (wrap__underscore (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I64)) iN_1))]"
	| fun_cvtop___case_8 :
		"fun_cvtop__underscore F32 I32 (cvtop_TRUNC v_sx) (mk_num__1 Fnn_F32 fN_1) (list_underscore  (map_option (λ (iter_0_33 :: iN). (mk_num__0 Inn_I32 iter_0_33)) (trunc__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))"
	| fun_cvtop___case_9 :
		"fun_cvtop__underscore F64 I32 (cvtop_TRUNC v_sx) (mk_num__1 Fnn_F64 fN_1) (list_underscore  (map_option (λ (iter_0_34 :: iN). (mk_num__0 Inn_I32 iter_0_34)) (trunc__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))"
	| fun_cvtop___case_10 :
		"fun_cvtop__underscore F32 I64 (cvtop_TRUNC v_sx) (mk_num__1 Fnn_F32 fN_1) (list_underscore  (map_option (λ (iter_0_35 :: iN). (mk_num__0 Inn_I64 iter_0_35)) (trunc__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))"
	| fun_cvtop___case_11 :
		"fun_cvtop__underscore F64 I64 (cvtop_TRUNC v_sx) (mk_num__1 Fnn_F64 fN_1) (list_underscore  (map_option (λ (iter_0_36 :: iN). (mk_num__0 Inn_I64 iter_0_36)) (trunc__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))"
	| fun_cvtop___case_12 :
		"fun_cvtop__underscore F32 I32 (TRUNC_SAT v_sx) (mk_num__1 Fnn_F32 fN_1) (list_underscore  (map_option (λ (iter_0_37 :: iN). (mk_num__0 Inn_I32 iter_0_37)) (trunc_sat__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))"
	| fun_cvtop___case_13 :
		"fun_cvtop__underscore F64 I32 (TRUNC_SAT v_sx) (mk_num__1 Fnn_F64 fN_1) (list_underscore  (map_option (λ (iter_0_38 :: iN). (mk_num__0 Inn_I32 iter_0_38)) (trunc_sat__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))"
	| fun_cvtop___case_14 :
		"fun_cvtop__underscore F32 I64 (TRUNC_SAT v_sx) (mk_num__1 Fnn_F32 fN_1) (list_underscore  (map_option (λ (iter_0_39 :: iN). (mk_num__0 Inn_I64 iter_0_39)) (trunc_sat__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))"
	| fun_cvtop___case_15 :
		"fun_cvtop__underscore F64 I64 (TRUNC_SAT v_sx) (mk_num__1 Fnn_F64 fN_1) (list_underscore  (map_option (λ (iter_0_40 :: iN). (mk_num__0 Inn_I64 iter_0_40)) (trunc_sat__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))"
	| fun_cvtop___case_16 :
		"fun_cvtop__underscore I32 F32 (CONVERT v_sx) (mk_num__0 Inn_I32 iN_1) [(mk_num__1 Fnn_F32 (convert__underscore (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Fnn Fnn_F32)) v_sx iN_1))]"
	| fun_cvtop___case_17 :
		"fun_cvtop__underscore I64 F32 (CONVERT v_sx) (mk_num__0 Inn_I64 iN_1) [(mk_num__1 Fnn_F32 (convert__underscore (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Fnn Fnn_F32)) v_sx iN_1))]"
	| fun_cvtop___case_18 :
		"fun_cvtop__underscore I32 F64 (CONVERT v_sx) (mk_num__0 Inn_I32 iN_1) [(mk_num__1 Fnn_F64 (convert__underscore (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Fnn Fnn_F64)) v_sx iN_1))]"
	| fun_cvtop___case_19 :
		"fun_cvtop__underscore I64 F64 (CONVERT v_sx) (mk_num__0 Inn_I64 iN_1) [(mk_num__1 Fnn_F64 (convert__underscore (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Fnn Fnn_F64)) v_sx iN_1))]"
	| fun_cvtop___case_20 :
		"fun_cvtop__underscore F32 F32 PROMOTE (mk_num__1 Fnn_F32 fN_1) (map (λ (iter_0_41 :: fN). (mk_num__1 Fnn_F32 iter_0_41)) (promote__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))"
	| fun_cvtop___case_21 :
		"fun_cvtop__underscore F64 F32 PROMOTE (mk_num__1 Fnn_F64 fN_1) (map (λ (iter_0_42 :: fN). (mk_num__1 Fnn_F32 iter_0_42)) (promote__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))"
	| fun_cvtop___case_22 :
		"fun_cvtop__underscore F32 F64 PROMOTE (mk_num__1 Fnn_F32 fN_1) (map (λ (iter_0_43 :: fN). (mk_num__1 Fnn_F64 iter_0_43)) (promote__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))"
	| fun_cvtop___case_23 :
		"fun_cvtop__underscore F64 F64 PROMOTE (mk_num__1 Fnn_F64 fN_1) (map (λ (iter_0_44 :: fN). (mk_num__1 Fnn_F64 iter_0_44)) (promote__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))"
	| fun_cvtop___case_24 :
		"fun_cvtop__underscore F32 F32 DEMOTE (mk_num__1 Fnn_F32 fN_1) (map (λ (iter_0_45 :: fN). (mk_num__1 Fnn_F32 iter_0_45)) (demote__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))"
	| fun_cvtop___case_25 :
		"fun_cvtop__underscore F64 F32 DEMOTE (mk_num__1 Fnn_F64 fN_1) (map (λ (iter_0_46 :: fN). (mk_num__1 Fnn_F32 iter_0_46)) (demote__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))"
	| fun_cvtop___case_26 :
		"fun_cvtop__underscore F32 F64 DEMOTE (mk_num__1 Fnn_F32 fN_1) (map (λ (iter_0_47 :: fN). (mk_num__1 Fnn_F64 iter_0_47)) (demote__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))"
	| fun_cvtop___case_27 :
		"fun_cvtop__underscore F64 F64 DEMOTE (mk_num__1 Fnn_F64 fN_1) (map (λ (iter_0_48 :: fN). (mk_num__1 Fnn_F64 iter_0_48)) (demote__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))"
	| fun_cvtop___case_28 :
		"((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 ((size (valtype_Fnn Fnn_F32)) ≠ None) ⟹
		 ((the ((size (valtype_Inn Inn_I32)))) = (the ((size (valtype_Fnn Fnn_F32))))) ⟹
		 fun_cvtop__underscore I32 F32 REINTERPRET (mk_num__0 Inn_I32 iN_1) [(reinterpret__underscore (numtype_Inn Inn_I32) (numtype_Fnn Fnn_F32) (mk_num__0 Inn_I32 iN_1))]"
	| fun_cvtop___case_29 :
		"((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 ((size (valtype_Fnn Fnn_F32)) ≠ None) ⟹
		 ((the ((size (valtype_Inn Inn_I64)))) = (the ((size (valtype_Fnn Fnn_F32))))) ⟹
		 fun_cvtop__underscore I64 F32 REINTERPRET (mk_num__0 Inn_I64 iN_1) [(reinterpret__underscore (numtype_Inn Inn_I64) (numtype_Fnn Fnn_F32) (mk_num__0 Inn_I64 iN_1))]"
	| fun_cvtop___case_30 :
		"((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 ((size (valtype_Fnn Fnn_F64)) ≠ None) ⟹
		 ((the ((size (valtype_Inn Inn_I32)))) = (the ((size (valtype_Fnn Fnn_F64))))) ⟹
		 fun_cvtop__underscore I32 F64 REINTERPRET (mk_num__0 Inn_I32 iN_1) [(reinterpret__underscore (numtype_Inn Inn_I32) (numtype_Fnn Fnn_F64) (mk_num__0 Inn_I32 iN_1))]"
	| fun_cvtop___case_31 :
		"((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 ((size (valtype_Fnn Fnn_F64)) ≠ None) ⟹
		 ((the ((size (valtype_Inn Inn_I64)))) = (the ((size (valtype_Fnn Fnn_F64))))) ⟹
		 fun_cvtop__underscore I64 F64 REINTERPRET (mk_num__0 Inn_I64 iN_1) [(reinterpret__underscore (numtype_Inn Inn_I64) (numtype_Fnn Fnn_F64) (mk_num__0 Inn_I64 iN_1))]"
	| fun_cvtop___case_32 :
		"((size (valtype_Fnn Fnn_F32)) ≠ None) ⟹
		 ((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 ((the ((size (valtype_Fnn Fnn_F32)))) = (the ((size (valtype_Inn Inn_I32))))) ⟹
		 fun_cvtop__underscore F32 I32 REINTERPRET (mk_num__1 Fnn_F32 fN_1) [(reinterpret__underscore (numtype_Fnn Fnn_F32) (numtype_Inn Inn_I32) (mk_num__1 Fnn_F32 fN_1))]"
	| fun_cvtop___case_33 :
		"((size (valtype_Fnn Fnn_F64)) ≠ None) ⟹
		 ((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 ((the ((size (valtype_Fnn Fnn_F64)))) = (the ((size (valtype_Inn Inn_I32))))) ⟹
		 fun_cvtop__underscore F64 I32 REINTERPRET (mk_num__1 Fnn_F64 fN_1) [(reinterpret__underscore (numtype_Fnn Fnn_F64) (numtype_Inn Inn_I32) (mk_num__1 Fnn_F64 fN_1))]"
	| fun_cvtop___case_34 :
		"((size (valtype_Fnn Fnn_F32)) ≠ None) ⟹
		 ((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 ((the ((size (valtype_Fnn Fnn_F32)))) = (the ((size (valtype_Inn Inn_I64))))) ⟹
		 fun_cvtop__underscore F32 I64 REINTERPRET (mk_num__1 Fnn_F32 fN_1) [(reinterpret__underscore (numtype_Fnn Fnn_F32) (numtype_Inn Inn_I64) (mk_num__1 Fnn_F32 fN_1))]"
	| fun_cvtop___case_35 :
		"((size (valtype_Fnn Fnn_F64)) ≠ None) ⟹
		 ((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 ((the ((size (valtype_Fnn Fnn_F64)))) = (the ((size (valtype_Inn Inn_I64))))) ⟹
		 fun_cvtop__underscore F64 I64 REINTERPRET (mk_num__1 Fnn_F64 fN_1) [(reinterpret__underscore (numtype_Fnn Fnn_F64) (numtype_Inn Inn_I64) (mk_num__1 Fnn_F64 fN_1))]"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:62.1-62.87 *)
axiomatization narrow__underscore :: "M ⇒ N ⇒ sx ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:76.1-76.102 *)
axiomatization ibits_underscore :: "N ⇒ iN ⇒ (bit list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:77.1-77.102 *)
axiomatization fbits_underscore :: "N ⇒ fN ⇒ (bit list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:78.1-78.103 *)
axiomatization ibytes_underscore :: "N ⇒ iN ⇒ (byte list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:79.1-79.103 *)
axiomatization fbytes_underscore :: "N ⇒ fN ⇒ (byte list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:80.1-80.103 *)
axiomatization nbytes_underscore :: "numtype ⇒ num_underscore ⇒ (byte list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:81.1-81.103 *)
axiomatization vbytes_underscore :: "vectype ⇒ vec_underscore ⇒ (byte list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:83.1-83.85 *)
axiomatization inv_ibits_underscore :: "N ⇒ (bit list) ⇒ iN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:84.1-84.85 *)
axiomatization inv_fbits_underscore :: "N ⇒ (bit list) ⇒ fN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:85.1-85.86 *)
axiomatization inv_ibytes_underscore :: "N ⇒ (byte list) ⇒ iN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:86.1-86.86 *)
axiomatization inv_fbytes_underscore :: "N ⇒ (byte list) ⇒ fN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:87.1-87.84 *)
axiomatization inv_nbytes_underscore :: "numtype ⇒ (byte list) ⇒ num_underscore"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:88.1-88.84 *)
axiomatization inv_vbytes_underscore :: "vectype ⇒ (byte list) ⇒ vec_underscore"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:110.1-110.29 *)
axiomatization inot_underscore :: "N ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:111.1-111.29 *)
axiomatization irev_underscore :: "N ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:113.1-113.39 *)
axiomatization iandnot_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:124.1-124.27 *)
function (sequential) inez_underscore :: "N ⇒ iN ⇒ u32" where
		  "inez_underscore v_N i_1 = (mk_uN (res_bool ((proj_uN_0 i_1) ≠ 0)))"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:131.1-131.49 *)
axiomatization ibitselect_underscore :: "N ⇒ iN ⇒ iN ⇒ iN ⇒ iN"

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:133.1-133.29 *)
function (sequential) ineg_underscore :: "N ⇒ iN ⇒ iN" where
		  "ineg_underscore v_N i_1 = (mk_uN (((((2 ^ v_N) :: nat) - ((proj_uN_0 i_1) :: nat)) mod ((2 ^ v_N) :: nat)) :: nat))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:132.6-132.12 *)
inductive fun_iabs_underscore :: "N ⇒ iN ⇒ iN ⇒ bool" where
	  fun_iabs__case_0 :
		"(fun_signed_underscore v_N (proj_uN_0 i_1) var_0) ⟹
		 fun_iabs_underscore v_N i_1 (if (var_0 ≥ (0 :: nat)) then i_1 else (ineg_underscore v_N i_1))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:134.6-134.12 *)
inductive fun_imin_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ iN ⇒ bool" where
	  fun_imin__case_0 :
		"((proj_uN_0 i_1) ≤ (proj_uN_0 i_2)) ⟹
		 fun_imin_underscore v_N U i_1 i_2 i_1"
	| fun_imin__case_1 :
		"((proj_uN_0 i_1) > (proj_uN_0 i_2)) ⟹
		 fun_imin_underscore v_N U i_1 i_2 i_2"
	| fun_imin__case_2 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) ⟹
		 fun_imin_underscore v_N S i_1 i_2 (if (var_0 ≤ var_1) then i_1 else i_2)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:135.6-135.12 *)
inductive fun_imax_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ iN ⇒ bool" where
	  fun_imax__case_0 :
		"((proj_uN_0 i_1) ≥ (proj_uN_0 i_2)) ⟹
		 fun_imax_underscore v_N U i_1 i_2 i_1"
	| fun_imax__case_1 :
		"((proj_uN_0 i_1) < (proj_uN_0 i_2)) ⟹
		 fun_imax_underscore v_N U i_1 i_2 i_2"
	| fun_imax__case_2 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) ⟹
		 fun_imax_underscore v_N S i_1 i_2 (if (var_0 ≥ var_1) then i_1 else i_2)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:136.6-136.16 *)
inductive fun_iadd_sat_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ iN ⇒ bool" where
	  fun_iadd_sat__case_0 :
		"fun_iadd_sat_underscore v_N U i_1 i_2 (mk_uN (sat_u_underscore v_N (((proj_uN_0 i_1) + (proj_uN_0 i_2)) :: nat)))"
	| fun_iadd_sat__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_2) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_1) ⟹
		 (fun_inv_signed_underscore v_N (sat_s_underscore v_N (var_1 + var_2)) var_0) ⟹
		 fun_iadd_sat_underscore v_N S i_1 i_2 (mk_uN var_0)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:137.6-137.16 *)
inductive fun_isub_sat_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ iN ⇒ bool" where
	  fun_isub_sat__case_0 :
		"fun_isub_sat_underscore v_N U i_1 i_2 (mk_uN (sat_u_underscore v_N (((proj_uN_0 i_1) :: nat) - ((proj_uN_0 i_2) :: nat))))"
	| fun_isub_sat__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_2) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_1) ⟹
		 (fun_inv_signed_underscore v_N (sat_s_underscore v_N (var_1 - var_2)) var_0) ⟹
		 fun_isub_sat_underscore v_N S i_1 i_2 (mk_uN var_0)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:138.1-138.82 *)
axiomatization iavgr_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:139.1-139.90 *)
axiomatization iq15mulr_sat_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ iN"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:221.1-221.38 *)
axiomatization fpmin_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:222.1-222.38 *)
axiomatization fpmax_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.1-324.27 *)
function (sequential) packnum_underscore :: "lanetype ⇒ num_underscore ⇒ lane_underscore" where
		  "packnum_underscore lanetype_I32 c = (mk_lane__0 I32 c)"
		| "packnum_underscore lanetype_I64 c = (mk_lane__0 I64 c)"
		| "packnum_underscore lanetype_F32 c = (mk_lane__0 F32 c)"
		| "packnum_underscore lanetype_F64 c = (mk_lane__0 F64 c)"
		| "packnum_underscore lanetype_I8 (mk_num__0 Inn_I32 c) = (mk_lane__1 I8 (wrap__underscore (the ((size (valtype_numtype (unpack (lanetype_packtype I8)))))) (psize I8) c))"
		| "packnum_underscore lanetype_I16 (mk_num__0 Inn_I32 c) = (mk_lane__1 I16 (wrap__underscore (the ((size (valtype_numtype (unpack (lanetype_packtype I16)))))) (psize I16) c))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:328.1-329.29 *)
function (sequential) unpacknum_underscore :: "lanetype ⇒ lane_underscore ⇒ num_underscore" where
		  "unpacknum_underscore lanetype_I32 (mk_lane__0 I32 c) = c"
		| "unpacknum_underscore lanetype_I64 (mk_lane__0 I64 c) = c"
		| "unpacknum_underscore lanetype_F32 (mk_lane__0 F32 c) = c"
		| "unpacknum_underscore lanetype_F64 (mk_lane__0 F64 c) = c"
		| "unpacknum_underscore lanetype_I8 (mk_lane__1 I8 c) = (mk_num__0 Inn_I32 (extend__underscore (psize I8) (the ((size (valtype_numtype (unpack (lanetype_packtype I8)))))) U c))"
		| "unpacknum_underscore lanetype_I16 (mk_lane__1 I16 c) = (mk_num__0 Inn_I32 (extend__underscore (psize I16) (the ((size (valtype_numtype (unpack (lanetype_packtype I16)))))) U c))"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:336.1-336.84 *)
axiomatization lanes_underscore :: "shape ⇒ vec_underscore ⇒ (lane_underscore list)"

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:339.1-340.36 *)
axiomatization inv_lanes_underscore :: "shape ⇒ (lane_underscore list) ⇒ vec_underscore"

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:343.1-343.28 *)
function (sequential) zeroop :: "vcvtop ⇒ (zero option)" where
		  "zeroop (vcvtop_EXTEND v_half v_sx) = None"
		| "zeroop (vcvtop_CONVERT half_opt v_sx) = None"
		| "zeroop (vcvtop_TRUNC_SAT v_sx zero_opt) = zero_opt"
		| "zeroop (vcvtop_DEMOTE v_zero) = (Some v_zero)"
		| "zeroop PROMOTELOW = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:350.1-350.28 *)
function (sequential) halfop :: "vcvtop ⇒ (half option)" where
		  "halfop (vcvtop_EXTEND v_half v_sx) = (Some v_half)"
		| "halfop (vcvtop_CONVERT half_opt v_sx) = half_opt"
		| "halfop (vcvtop_TRUNC_SAT v_sx zero_opt) = None"
		| "halfop (vcvtop_DEMOTE v_zero) = None"
		| "halfop PROMOTELOW = (Some LOW)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:357.1-357.32 *)
function (sequential) fun_half :: "half ⇒ nat ⇒ nat ⇒ nat" where
		  "fun_half LOW i j = i"
		| "fun_half HIGH i j = j"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:362.1-363.28 *)
function (sequential) vvunop_underscore :: "vectype ⇒ vvunop ⇒ vec_underscore ⇒ vec_underscore" where
		  "vvunop_underscore V128 NOT v128 = (inot_underscore (the ((size valtype_V128))) v128)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:364.1-365.31 *)
function (sequential) vvbinop_underscore :: "vectype ⇒ vvbinop ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore" where
		  "vvbinop_underscore V128 vvbinop_AND v128_1 v128_2 = (iand_underscore (the ((size valtype_V128))) v128_1 v128_2)"
		| "vvbinop_underscore V128 ANDNOT v128_1 v128_2 = (iandnot_underscore (the ((size valtype_V128))) v128_1 v128_2)"
		| "vvbinop_underscore V128 vvbinop_OR v128_1 v128_2 = (ior_underscore (the ((size valtype_V128))) v128_1 v128_2)"
		| "vvbinop_underscore V128 vvbinop_XOR v128_1 v128_2 = (ixor_underscore (the ((size valtype_V128))) v128_1 v128_2)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:366.1-367.34 *)
function (sequential) vvternop_underscore :: "vectype ⇒ vvternop ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore" where
		  "vvternop_underscore V128 BITSELECT v128_1 v128_2 v128_3 = (ibitselect_underscore (the ((size valtype_V128))) v128_1 v128_2 v128_3)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:377.6-377.13 *)
inductive fun_vunop_underscore :: "shape ⇒ vunop_underscore ⇒ vec_underscore ⇒ (vec_underscore list) ⇒ bool" where
	  fun_vunop__case_0 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 list_all (λ (lane_1_4 :: lane_underscore). ((proj_lane__2 lane_1_4) ≠ None)) lane_1_lst ⟹
		 list_all2 (λ (var_2 :: uN) (lane_1_4 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_4))) var_2)) var_2_lst lane_1_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 list_all (λ (lane_1_2 :: lane_underscore). ((proj_lane__2 lane_1_2) ≠ None)) lane_1_lst ⟹
		 list_all2 (λ (var_1 :: uN) (lane_1_2 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_2))) var_1)) var_1_lst lane_1_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 list_all (λ (lane_1_1 :: lane_underscore). ((proj_lane__2 lane_1_1) ≠ None)) lane_1_lst ⟹
		 list_all2 (λ (var_0 :: uN) (lane_1_1 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_1))) var_0)) var_0_lst lane_1_lst ⟹
		 list_all (λ (iter_1 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_1)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I32 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 M_0 vunop_Jnn_N_ABS) v128_1 [v128]"
	| fun_vunop__case_1 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 list_all (λ (lane_1_8 :: lane_underscore). ((proj_lane__2 lane_1_8) ≠ None)) lane_1_lst ⟹
		 list_all2 (λ (var_2 :: uN) (lane_1_8 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_8))) var_2)) var_2_lst lane_1_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 list_all (λ (lane_1_6 :: lane_underscore). ((proj_lane__2 lane_1_6) ≠ None)) lane_1_lst ⟹
		 list_all2 (λ (var_1 :: uN) (lane_1_6 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_6))) var_1)) var_1_lst lane_1_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 list_all (λ (lane_1_5 :: lane_underscore). ((proj_lane__2 lane_1_5) ≠ None)) lane_1_lst ⟹
		 list_all2 (λ (var_0 :: uN) (lane_1_5 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_5))) var_0)) var_0_lst lane_1_lst ⟹
		 list_all (λ (iter_2 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_2)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I64 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 M_0 vunop_Jnn_N_ABS) v128_1 [v128]"
	| fun_vunop__case_2 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 list_all (λ (lane_1_12 :: lane_underscore). ((proj_lane__2 lane_1_12) ≠ None)) lane_1_lst ⟹
		 list_all2 (λ (var_2 :: uN) (lane_1_12 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_12))) var_2)) var_2_lst lane_1_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 list_all (λ (lane_1_10 :: lane_underscore). ((proj_lane__2 lane_1_10) ≠ None)) lane_1_lst ⟹
		 list_all2 (λ (var_1 :: uN) (lane_1_10 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_10))) var_1)) var_1_lst lane_1_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 list_all (λ (lane_1_9 :: lane_underscore). ((proj_lane__2 lane_1_9) ≠ None)) lane_1_lst ⟹
		 list_all2 (λ (var_0 :: uN) (lane_1_9 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_9))) var_0)) var_0_lst lane_1_lst ⟹
		 list_all (λ (iter_3 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_3)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I8 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 M_0 vunop_Jnn_N_ABS) v128_1 [v128]"
	| fun_vunop__case_3 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 list_all (λ (lane_1_16 :: lane_underscore). ((proj_lane__2 lane_1_16) ≠ None)) lane_1_lst ⟹
		 list_all2 (λ (var_2 :: uN) (lane_1_16 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_16))) var_2)) var_2_lst lane_1_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 list_all (λ (lane_1_14 :: lane_underscore). ((proj_lane__2 lane_1_14) ≠ None)) lane_1_lst ⟹
		 list_all2 (λ (var_1 :: uN) (lane_1_14 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_14))) var_1)) var_1_lst lane_1_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 list_all (λ (lane_1_13 :: lane_underscore). ((proj_lane__2 lane_1_13) ≠ None)) lane_1_lst ⟹
		 list_all2 (λ (var_0 :: uN) (lane_1_13 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_13))) var_0)) var_0_lst lane_1_lst ⟹
		 list_all (λ (iter_4 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_4)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I16 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 M_0 vunop_Jnn_N_ABS) v128_1 [v128]"
	| fun_vunop__case_4 :
		"list_all (λ (iter_5 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_5)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (lane_1_17 :: lane_underscore). ((proj_lane__2 lane_1_17) ≠ None)) lane_1_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_1_17 :: lane_underscore). (mk_lane__2 Jnn_I32 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_17)))))) lane_1_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_18 :: lane_underscore). ((proj_lane__2 lane_1_18) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_18 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_18))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 list_all (λ (lane_1_20 :: lane_underscore). ((proj_lane__2 lane_1_20) ≠ None)) lane_1_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_1_20 :: lane_underscore). (mk_lane__2 Jnn_I32 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_20)))))) lane_1_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 M_0 vunop_Jnn_N_NEG) v128_1 [v128]"
	| fun_vunop__case_5 :
		"list_all (λ (iter_6 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_6)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (lane_1_21 :: lane_underscore). ((proj_lane__2 lane_1_21) ≠ None)) lane_1_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_1_21 :: lane_underscore). (mk_lane__2 Jnn_I64 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_21)))))) lane_1_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_22 :: lane_underscore). ((proj_lane__2 lane_1_22) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_22 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_22))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 list_all (λ (lane_1_24 :: lane_underscore). ((proj_lane__2 lane_1_24) ≠ None)) lane_1_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_1_24 :: lane_underscore). (mk_lane__2 Jnn_I64 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_24)))))) lane_1_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 M_0 vunop_Jnn_N_NEG) v128_1 [v128]"
	| fun_vunop__case_6 :
		"list_all (λ (iter_7 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_7)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (lane_1_25 :: lane_underscore). ((proj_lane__2 lane_1_25) ≠ None)) lane_1_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_1_25 :: lane_underscore). (mk_lane__2 Jnn_I8 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_25)))))) lane_1_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_26 :: lane_underscore). ((proj_lane__2 lane_1_26) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_26 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_26))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 list_all (λ (lane_1_28 :: lane_underscore). ((proj_lane__2 lane_1_28) ≠ None)) lane_1_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_1_28 :: lane_underscore). (mk_lane__2 Jnn_I8 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_28)))))) lane_1_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 M_0 vunop_Jnn_N_NEG) v128_1 [v128]"
	| fun_vunop__case_7 :
		"list_all (λ (iter_8 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_8)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (lane_1_29 :: lane_underscore). ((proj_lane__2 lane_1_29) ≠ None)) lane_1_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_1_29 :: lane_underscore). (mk_lane__2 Jnn_I16 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_29)))))) lane_1_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_30 :: lane_underscore). ((proj_lane__2 lane_1_30) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_30 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_30))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 list_all (λ (lane_1_32 :: lane_underscore). ((proj_lane__2 lane_1_32) ≠ None)) lane_1_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_1_32 :: lane_underscore). (mk_lane__2 Jnn_I16 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_32)))))) lane_1_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 M_0 vunop_Jnn_N_NEG) v128_1 [v128]"
	| fun_vunop__case_8 :
		"list_all (λ (iter_9 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_9)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (lane_1_33 :: lane_underscore). ((proj_lane__2 lane_1_33) ≠ None)) lane_1_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_1_33 :: lane_underscore). (mk_lane__2 Jnn_I32 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_33)))))) lane_1_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_34 :: lane_underscore). ((proj_lane__2 lane_1_34) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_34 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_34))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 list_all (λ (lane_1_36 :: lane_underscore). ((proj_lane__2 lane_1_36) ≠ None)) lane_1_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_1_36 :: lane_underscore). (mk_lane__2 Jnn_I32 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_36)))))) lane_1_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 M_0 vunop_Jnn_N_POPCNT) v128_1 [v128]"
	| fun_vunop__case_9 :
		"list_all (λ (iter_10 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_10)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (lane_1_37 :: lane_underscore). ((proj_lane__2 lane_1_37) ≠ None)) lane_1_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_1_37 :: lane_underscore). (mk_lane__2 Jnn_I64 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_37)))))) lane_1_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_38 :: lane_underscore). ((proj_lane__2 lane_1_38) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_38 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_38))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 list_all (λ (lane_1_40 :: lane_underscore). ((proj_lane__2 lane_1_40) ≠ None)) lane_1_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_1_40 :: lane_underscore). (mk_lane__2 Jnn_I64 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_40)))))) lane_1_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 M_0 vunop_Jnn_N_POPCNT) v128_1 [v128]"
	| fun_vunop__case_10 :
		"list_all (λ (iter_11 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_11)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (lane_1_41 :: lane_underscore). ((proj_lane__2 lane_1_41) ≠ None)) lane_1_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_1_41 :: lane_underscore). (mk_lane__2 Jnn_I8 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_41)))))) lane_1_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_42 :: lane_underscore). ((proj_lane__2 lane_1_42) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_42 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_42))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 list_all (λ (lane_1_44 :: lane_underscore). ((proj_lane__2 lane_1_44) ≠ None)) lane_1_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_1_44 :: lane_underscore). (mk_lane__2 Jnn_I8 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_44)))))) lane_1_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 M_0 vunop_Jnn_N_POPCNT) v128_1 [v128]"
	| fun_vunop__case_11 :
		"list_all (λ (iter_12 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_12)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (lane_1_45 :: lane_underscore). ((proj_lane__2 lane_1_45) ≠ None)) lane_1_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_1_45 :: lane_underscore). (mk_lane__2 Jnn_I16 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_45)))))) lane_1_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_46 :: lane_underscore). ((proj_lane__2 lane_1_46) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_46 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_46))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 list_all (λ (lane_1_48 :: lane_underscore). ((proj_lane__2 lane_1_48) ≠ None)) lane_1_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_1_48 :: lane_underscore). (mk_lane__2 Jnn_I16 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_48)))))) lane_1_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 M_0 vunop_Jnn_N_POPCNT) v128_1 [v128]"
	| fun_vunop__case_12 :
		"list_all (λ (lane_lst_1 :: (lane_underscore list)). list_all (λ (lane_1 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_1)) lane_lst_1) lane_lst_lst ⟹
		 list_all (λ (iter_13 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_13)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_14 :: (lane_underscore list)). list_all (λ (iter_15 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_15)) iter_14) (setproduct_underscore  (map (λ (lane_1_49 :: lane_underscore). (map (λ (iter_0_49 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_49))) (fabs_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_49))))))))) lane_1_lst)) ⟹
		 list_all (λ (lane_1_50 :: lane_underscore). list_all (λ (iter_16 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_16)) (fabs_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_50)))))))) lane_1_lst ⟹
		 list_all (λ (lane_lst_2 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_2))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_51 :: lane_underscore). list_all (λ (iter_0_50 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_50)))) (fabs_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_51)))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (map (λ (lane_1_53 :: lane_underscore). (map (λ (iter_0_51 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_51))) (fabs_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_53))))))))) lane_1_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_4 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_4)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_ABS) v128_1 v128_lst"
	| fun_vunop__case_13 :
		"list_all (λ (lane_lst_5 :: (lane_underscore list)). list_all (λ (lane_5 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_5)) lane_lst_5) lane_lst_lst ⟹
		 list_all (λ (iter_17 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_17)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_18 :: (lane_underscore list)). list_all (λ (iter_19 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_19)) iter_18) (setproduct_underscore  (map (λ (lane_1_54 :: lane_underscore). (map (λ (iter_0_52 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_52))) (fabs_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_54))))))))) lane_1_lst)) ⟹
		 list_all (λ (lane_1_55 :: lane_underscore). list_all (λ (iter_20 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_20)) (fabs_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_55)))))))) lane_1_lst ⟹
		 list_all (λ (lane_lst_6 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_6))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_56 :: lane_underscore). list_all (λ (iter_0_53 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_53)))) (fabs_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_56)))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (map (λ (lane_1_58 :: lane_underscore). (map (λ (iter_0_54 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_54))) (fabs_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_58))))))))) lane_1_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_8 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_8)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_ABS) v128_1 v128_lst"
	| fun_vunop__case_14 :
		"list_all (λ (lane_lst_9 :: (lane_underscore list)). list_all (λ (lane_9 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_9)) lane_lst_9) lane_lst_lst ⟹
		 list_all (λ (iter_21 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_21)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_22 :: (lane_underscore list)). list_all (λ (iter_23 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_23)) iter_22) (setproduct_underscore  (map (λ (lane_1_59 :: lane_underscore). (map (λ (iter_0_55 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_55))) (fneg_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_59))))))))) lane_1_lst)) ⟹
		 list_all (λ (lane_1_60 :: lane_underscore). list_all (λ (iter_24 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_24)) (fneg_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_60)))))))) lane_1_lst ⟹
		 list_all (λ (lane_lst_10 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_10))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_61 :: lane_underscore). list_all (λ (iter_0_56 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_56)))) (fneg_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_61)))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (map (λ (lane_1_63 :: lane_underscore). (map (λ (iter_0_57 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_57))) (fneg_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_63))))))))) lane_1_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_12 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_12)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_NEG) v128_1 v128_lst"
	| fun_vunop__case_15 :
		"list_all (λ (lane_lst_13 :: (lane_underscore list)). list_all (λ (lane_13 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_13)) lane_lst_13) lane_lst_lst ⟹
		 list_all (λ (iter_25 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_25)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_26 :: (lane_underscore list)). list_all (λ (iter_27 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_27)) iter_26) (setproduct_underscore  (map (λ (lane_1_64 :: lane_underscore). (map (λ (iter_0_58 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_58))) (fneg_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_64))))))))) lane_1_lst)) ⟹
		 list_all (λ (lane_1_65 :: lane_underscore). list_all (λ (iter_28 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_28)) (fneg_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_65)))))))) lane_1_lst ⟹
		 list_all (λ (lane_lst_14 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_14))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_66 :: lane_underscore). list_all (λ (iter_0_59 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_59)))) (fneg_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_66)))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (map (λ (lane_1_68 :: lane_underscore). (map (λ (iter_0_60 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_60))) (fneg_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_68))))))))) lane_1_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_16 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_16)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_NEG) v128_1 v128_lst"
	| fun_vunop__case_16 :
		"list_all (λ (lane_lst_17 :: (lane_underscore list)). list_all (λ (lane_17 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_17)) lane_lst_17) lane_lst_lst ⟹
		 list_all (λ (iter_29 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_29)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_30 :: (lane_underscore list)). list_all (λ (iter_31 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_31)) iter_30) (setproduct_underscore  (map (λ (lane_1_69 :: lane_underscore). (map (λ (iter_0_61 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_61))) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_69))))))))) lane_1_lst)) ⟹
		 list_all (λ (lane_1_70 :: lane_underscore). list_all (λ (iter_32 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_32)) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_70)))))))) lane_1_lst ⟹
		 list_all (λ (lane_lst_18 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_18))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_71 :: lane_underscore). list_all (λ (iter_0_62 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_62)))) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_71)))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (map (λ (lane_1_73 :: lane_underscore). (map (λ (iter_0_63 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_63))) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_73))))))))) lane_1_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_20 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_20)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_SQRT) v128_1 v128_lst"
	| fun_vunop__case_17 :
		"list_all (λ (lane_lst_21 :: (lane_underscore list)). list_all (λ (lane_21 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_21)) lane_lst_21) lane_lst_lst ⟹
		 list_all (λ (iter_33 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_33)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_34 :: (lane_underscore list)). list_all (λ (iter_35 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_35)) iter_34) (setproduct_underscore  (map (λ (lane_1_74 :: lane_underscore). (map (λ (iter_0_64 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_64))) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_74))))))))) lane_1_lst)) ⟹
		 list_all (λ (lane_1_75 :: lane_underscore). list_all (λ (iter_36 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_36)) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_75)))))))) lane_1_lst ⟹
		 list_all (λ (lane_lst_22 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_22))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_76 :: lane_underscore). list_all (λ (iter_0_65 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_65)))) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_76)))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (map (λ (lane_1_78 :: lane_underscore). (map (λ (iter_0_66 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_66))) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_78))))))))) lane_1_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_24 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_24)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_SQRT) v128_1 v128_lst"
	| fun_vunop__case_18 :
		"list_all (λ (lane_lst_25 :: (lane_underscore list)). list_all (λ (lane_25 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_25)) lane_lst_25) lane_lst_lst ⟹
		 list_all (λ (iter_37 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_37)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_38 :: (lane_underscore list)). list_all (λ (iter_39 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_39)) iter_38) (setproduct_underscore  (map (λ (lane_1_79 :: lane_underscore). (map (λ (iter_0_67 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_67))) (fceil_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_79))))))))) lane_1_lst)) ⟹
		 list_all (λ (lane_1_80 :: lane_underscore). list_all (λ (iter_40 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_40)) (fceil_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_80)))))))) lane_1_lst ⟹
		 list_all (λ (lane_lst_26 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_26))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_81 :: lane_underscore). list_all (λ (iter_0_68 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_68)))) (fceil_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_81)))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (map (λ (lane_1_83 :: lane_underscore). (map (λ (iter_0_69 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_69))) (fceil_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_83))))))))) lane_1_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_28 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_28)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_CEIL) v128_1 v128_lst"
	| fun_vunop__case_19 :
		"list_all (λ (lane_lst_29 :: (lane_underscore list)). list_all (λ (lane_29 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_29)) lane_lst_29) lane_lst_lst ⟹
		 list_all (λ (iter_41 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_41)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_42 :: (lane_underscore list)). list_all (λ (iter_43 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_43)) iter_42) (setproduct_underscore  (map (λ (lane_1_84 :: lane_underscore). (map (λ (iter_0_70 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_70))) (fceil_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_84))))))))) lane_1_lst)) ⟹
		 list_all (λ (lane_1_85 :: lane_underscore). list_all (λ (iter_44 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_44)) (fceil_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_85)))))))) lane_1_lst ⟹
		 list_all (λ (lane_lst_30 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_30))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_86 :: lane_underscore). list_all (λ (iter_0_71 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_71)))) (fceil_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_86)))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (map (λ (lane_1_88 :: lane_underscore). (map (λ (iter_0_72 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_72))) (fceil_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_88))))))))) lane_1_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_32 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_32)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_CEIL) v128_1 v128_lst"
	| fun_vunop__case_20 :
		"list_all (λ (lane_lst_33 :: (lane_underscore list)). list_all (λ (lane_33 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_33)) lane_lst_33) lane_lst_lst ⟹
		 list_all (λ (iter_45 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_45)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_46 :: (lane_underscore list)). list_all (λ (iter_47 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_47)) iter_46) (setproduct_underscore  (map (λ (lane_1_89 :: lane_underscore). (map (λ (iter_0_73 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_73))) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_89))))))))) lane_1_lst)) ⟹
		 list_all (λ (lane_1_90 :: lane_underscore). list_all (λ (iter_48 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_48)) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_90)))))))) lane_1_lst ⟹
		 list_all (λ (lane_lst_34 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_34))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_91 :: lane_underscore). list_all (λ (iter_0_74 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_74)))) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_91)))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (map (λ (lane_1_93 :: lane_underscore). (map (λ (iter_0_75 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_75))) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_93))))))))) lane_1_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_36 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_36)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_FLOOR) v128_1 v128_lst"
	| fun_vunop__case_21 :
		"list_all (λ (lane_lst_37 :: (lane_underscore list)). list_all (λ (lane_37 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_37)) lane_lst_37) lane_lst_lst ⟹
		 list_all (λ (iter_49 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_49)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_50 :: (lane_underscore list)). list_all (λ (iter_51 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_51)) iter_50) (setproduct_underscore  (map (λ (lane_1_94 :: lane_underscore). (map (λ (iter_0_76 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_76))) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_94))))))))) lane_1_lst)) ⟹
		 list_all (λ (lane_1_95 :: lane_underscore). list_all (λ (iter_52 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_52)) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_95)))))))) lane_1_lst ⟹
		 list_all (λ (lane_lst_38 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_38))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_96 :: lane_underscore). list_all (λ (iter_0_77 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_77)))) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_96)))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (map (λ (lane_1_98 :: lane_underscore). (map (λ (iter_0_78 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_78))) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_98))))))))) lane_1_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_40 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_40)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_FLOOR) v128_1 v128_lst"
	| fun_vunop__case_22 :
		"list_all (λ (lane_lst_41 :: (lane_underscore list)). list_all (λ (lane_41 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_41)) lane_lst_41) lane_lst_lst ⟹
		 list_all (λ (iter_53 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_53)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_54 :: (lane_underscore list)). list_all (λ (iter_55 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_55)) iter_54) (setproduct_underscore  (map (λ (lane_1_99 :: lane_underscore). (map (λ (iter_0_79 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_79))) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_99))))))))) lane_1_lst)) ⟹
		 list_all (λ (lane_1_100 :: lane_underscore). list_all (λ (iter_56 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_56)) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_100)))))))) lane_1_lst ⟹
		 list_all (λ (lane_lst_42 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_42))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_101 :: lane_underscore). list_all (λ (iter_0_80 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_80)))) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_101)))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (map (λ (lane_1_103 :: lane_underscore). (map (λ (iter_0_81 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_81))) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_103))))))))) lane_1_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_44 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_44)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_TRUNC) v128_1 v128_lst"
	| fun_vunop__case_23 :
		"list_all (λ (lane_lst_45 :: (lane_underscore list)). list_all (λ (lane_45 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_45)) lane_lst_45) lane_lst_lst ⟹
		 list_all (λ (iter_57 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_57)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_58 :: (lane_underscore list)). list_all (λ (iter_59 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_59)) iter_58) (setproduct_underscore  (map (λ (lane_1_104 :: lane_underscore). (map (λ (iter_0_82 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_82))) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_104))))))))) lane_1_lst)) ⟹
		 list_all (λ (lane_1_105 :: lane_underscore). list_all (λ (iter_60 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_60)) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_105)))))))) lane_1_lst ⟹
		 list_all (λ (lane_lst_46 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_46))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_106 :: lane_underscore). list_all (λ (iter_0_83 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_83)))) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_106)))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (map (λ (lane_1_108 :: lane_underscore). (map (λ (iter_0_84 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_84))) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_108))))))))) lane_1_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_48 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_48)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_TRUNC) v128_1 v128_lst"
	| fun_vunop__case_24 :
		"list_all (λ (lane_lst_49 :: (lane_underscore list)). list_all (λ (lane_49 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_49)) lane_lst_49) lane_lst_lst ⟹
		 list_all (λ (iter_61 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_61)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_62 :: (lane_underscore list)). list_all (λ (iter_63 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_63)) iter_62) (setproduct_underscore  (map (λ (lane_1_109 :: lane_underscore). (map (λ (iter_0_85 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_85))) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_109))))))))) lane_1_lst)) ⟹
		 list_all (λ (lane_1_110 :: lane_underscore). list_all (λ (iter_64 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_64)) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_110)))))))) lane_1_lst ⟹
		 list_all (λ (lane_lst_50 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_50))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_111 :: lane_underscore). list_all (λ (iter_0_86 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_86)))) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_111)))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (map (λ (lane_1_113 :: lane_underscore). (map (λ (iter_0_87 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_87))) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_113))))))))) lane_1_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_52 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_52)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_NEAREST) v128_1 v128_lst"
	| fun_vunop__case_25 :
		"list_all (λ (lane_lst_53 :: (lane_underscore list)). list_all (λ (lane_53 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_53)) lane_lst_53) lane_lst_lst ⟹
		 list_all (λ (iter_65 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_65)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_66 :: (lane_underscore list)). list_all (λ (iter_67 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_67)) iter_66) (setproduct_underscore  (map (λ (lane_1_114 :: lane_underscore). (map (λ (iter_0_88 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_88))) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_114))))))))) lane_1_lst)) ⟹
		 list_all (λ (lane_1_115 :: lane_underscore). list_all (λ (iter_68 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_68)) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_115)))))))) lane_1_lst ⟹
		 list_all (λ (lane_lst_54 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_54))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_116 :: lane_underscore). list_all (λ (iter_0_89 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_89)))) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_116)))))))) lane_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (map (λ (lane_1_118 :: lane_underscore). (map (λ (iter_0_90 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_90))) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_118))))))))) lane_1_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_56 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_56)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_NEAREST) v128_1 v128_lst"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:379.6-379.14 *)
inductive fun_vbinop_underscore :: "shape ⇒ vbinop_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ (vec_underscore list) ⇒ bool" where
	  fun_vbinop__case_0 :
		"list_all (λ (iter_69 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_69)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_70 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_70)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_119 :: lane_underscore). ((proj_lane__2 lane_1_119) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_1 :: lane_underscore). ((proj_lane__2 lane_2_1) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (λ (lane_1_119 :: lane_underscore) (lane_2_1 :: lane_underscore). (mk_lane__2 Jnn_I32 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_119))) (the ((proj_lane__2 lane_2_1)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_120 :: lane_underscore). ((proj_lane__2 lane_1_120) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_2 :: lane_underscore). ((proj_lane__2 lane_2_2) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_120 :: lane_underscore) (lane_2_2 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_120))) (the ((proj_lane__2 lane_2_2))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_122 :: lane_underscore). ((proj_lane__2 lane_1_122) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_4 :: lane_underscore). ((proj_lane__2 lane_2_4) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (λ (lane_1_122 :: lane_underscore) (lane_2_4 :: lane_underscore). (mk_lane__2 Jnn_I32 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_122))) (the ((proj_lane__2 lane_2_4)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 vbinop_Jnn_N_ADD) v128_1 v128_2 [v128]"
	| fun_vbinop__case_1 :
		"list_all (λ (iter_71 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_71)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_72 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_72)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_123 :: lane_underscore). ((proj_lane__2 lane_1_123) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_5 :: lane_underscore). ((proj_lane__2 lane_2_5) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (λ (lane_1_123 :: lane_underscore) (lane_2_5 :: lane_underscore). (mk_lane__2 Jnn_I64 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_123))) (the ((proj_lane__2 lane_2_5)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_124 :: lane_underscore). ((proj_lane__2 lane_1_124) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_6 :: lane_underscore). ((proj_lane__2 lane_2_6) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_124 :: lane_underscore) (lane_2_6 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_124))) (the ((proj_lane__2 lane_2_6))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_126 :: lane_underscore). ((proj_lane__2 lane_1_126) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_8 :: lane_underscore). ((proj_lane__2 lane_2_8) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (λ (lane_1_126 :: lane_underscore) (lane_2_8 :: lane_underscore). (mk_lane__2 Jnn_I64 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_126))) (the ((proj_lane__2 lane_2_8)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 vbinop_Jnn_N_ADD) v128_1 v128_2 [v128]"
	| fun_vbinop__case_2 :
		"list_all (λ (iter_73 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_73)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_74 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_74)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_127 :: lane_underscore). ((proj_lane__2 lane_1_127) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_9 :: lane_underscore). ((proj_lane__2 lane_2_9) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (λ (lane_1_127 :: lane_underscore) (lane_2_9 :: lane_underscore). (mk_lane__2 Jnn_I8 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_127))) (the ((proj_lane__2 lane_2_9)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_128 :: lane_underscore). ((proj_lane__2 lane_1_128) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_10 :: lane_underscore). ((proj_lane__2 lane_2_10) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_128 :: lane_underscore) (lane_2_10 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_128))) (the ((proj_lane__2 lane_2_10))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_130 :: lane_underscore). ((proj_lane__2 lane_1_130) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_12 :: lane_underscore). ((proj_lane__2 lane_2_12) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (λ (lane_1_130 :: lane_underscore) (lane_2_12 :: lane_underscore). (mk_lane__2 Jnn_I8 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_130))) (the ((proj_lane__2 lane_2_12)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 vbinop_Jnn_N_ADD) v128_1 v128_2 [v128]"
	| fun_vbinop__case_3 :
		"list_all (λ (iter_75 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_75)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_76 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_76)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_131 :: lane_underscore). ((proj_lane__2 lane_1_131) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_13 :: lane_underscore). ((proj_lane__2 lane_2_13) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (λ (lane_1_131 :: lane_underscore) (lane_2_13 :: lane_underscore). (mk_lane__2 Jnn_I16 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_131))) (the ((proj_lane__2 lane_2_13)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_132 :: lane_underscore). ((proj_lane__2 lane_1_132) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_14 :: lane_underscore). ((proj_lane__2 lane_2_14) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_132 :: lane_underscore) (lane_2_14 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_132))) (the ((proj_lane__2 lane_2_14))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_134 :: lane_underscore). ((proj_lane__2 lane_1_134) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_16 :: lane_underscore). ((proj_lane__2 lane_2_16) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (λ (lane_1_134 :: lane_underscore) (lane_2_16 :: lane_underscore). (mk_lane__2 Jnn_I16 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_134))) (the ((proj_lane__2 lane_2_16)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 vbinop_Jnn_N_ADD) v128_1 v128_2 [v128]"
	| fun_vbinop__case_4 :
		"list_all (λ (iter_77 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_77)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_78 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_78)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_135 :: lane_underscore). ((proj_lane__2 lane_1_135) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_17 :: lane_underscore). ((proj_lane__2 lane_2_17) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (λ (lane_1_135 :: lane_underscore) (lane_2_17 :: lane_underscore). (mk_lane__2 Jnn_I32 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_135))) (the ((proj_lane__2 lane_2_17)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_136 :: lane_underscore). ((proj_lane__2 lane_1_136) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_18 :: lane_underscore). ((proj_lane__2 lane_2_18) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_136 :: lane_underscore) (lane_2_18 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_136))) (the ((proj_lane__2 lane_2_18))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_138 :: lane_underscore). ((proj_lane__2 lane_1_138) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_20 :: lane_underscore). ((proj_lane__2 lane_2_20) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (λ (lane_1_138 :: lane_underscore) (lane_2_20 :: lane_underscore). (mk_lane__2 Jnn_I32 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_138))) (the ((proj_lane__2 lane_2_20)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 vbinop_Jnn_N_SUB) v128_1 v128_2 [v128]"
	| fun_vbinop__case_5 :
		"list_all (λ (iter_79 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_79)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_80 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_80)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_139 :: lane_underscore). ((proj_lane__2 lane_1_139) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_21 :: lane_underscore). ((proj_lane__2 lane_2_21) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (λ (lane_1_139 :: lane_underscore) (lane_2_21 :: lane_underscore). (mk_lane__2 Jnn_I64 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_139))) (the ((proj_lane__2 lane_2_21)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_140 :: lane_underscore). ((proj_lane__2 lane_1_140) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_22 :: lane_underscore). ((proj_lane__2 lane_2_22) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_140 :: lane_underscore) (lane_2_22 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_140))) (the ((proj_lane__2 lane_2_22))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_142 :: lane_underscore). ((proj_lane__2 lane_1_142) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_24 :: lane_underscore). ((proj_lane__2 lane_2_24) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (λ (lane_1_142 :: lane_underscore) (lane_2_24 :: lane_underscore). (mk_lane__2 Jnn_I64 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_142))) (the ((proj_lane__2 lane_2_24)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 vbinop_Jnn_N_SUB) v128_1 v128_2 [v128]"
	| fun_vbinop__case_6 :
		"list_all (λ (iter_81 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_81)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_82 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_82)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_143 :: lane_underscore). ((proj_lane__2 lane_1_143) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_25 :: lane_underscore). ((proj_lane__2 lane_2_25) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (λ (lane_1_143 :: lane_underscore) (lane_2_25 :: lane_underscore). (mk_lane__2 Jnn_I8 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_143))) (the ((proj_lane__2 lane_2_25)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_144 :: lane_underscore). ((proj_lane__2 lane_1_144) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_26 :: lane_underscore). ((proj_lane__2 lane_2_26) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_144 :: lane_underscore) (lane_2_26 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_144))) (the ((proj_lane__2 lane_2_26))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_146 :: lane_underscore). ((proj_lane__2 lane_1_146) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_28 :: lane_underscore). ((proj_lane__2 lane_2_28) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (λ (lane_1_146 :: lane_underscore) (lane_2_28 :: lane_underscore). (mk_lane__2 Jnn_I8 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_146))) (the ((proj_lane__2 lane_2_28)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 vbinop_Jnn_N_SUB) v128_1 v128_2 [v128]"
	| fun_vbinop__case_7 :
		"list_all (λ (iter_83 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_83)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_84 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_84)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_147 :: lane_underscore). ((proj_lane__2 lane_1_147) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_29 :: lane_underscore). ((proj_lane__2 lane_2_29) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (λ (lane_1_147 :: lane_underscore) (lane_2_29 :: lane_underscore). (mk_lane__2 Jnn_I16 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_147))) (the ((proj_lane__2 lane_2_29)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_148 :: lane_underscore). ((proj_lane__2 lane_1_148) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_30 :: lane_underscore). ((proj_lane__2 lane_2_30) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_148 :: lane_underscore) (lane_2_30 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_148))) (the ((proj_lane__2 lane_2_30))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_150 :: lane_underscore). ((proj_lane__2 lane_1_150) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_32 :: lane_underscore). ((proj_lane__2 lane_2_32) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (λ (lane_1_150 :: lane_underscore) (lane_2_32 :: lane_underscore). (mk_lane__2 Jnn_I16 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_150))) (the ((proj_lane__2 lane_2_32)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 vbinop_Jnn_N_SUB) v128_1 v128_2 [v128]"
	| fun_vbinop__case_8 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_154 :: lane_underscore). ((proj_lane__2 lane_1_154) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_36 :: lane_underscore). ((proj_lane__2 lane_2_36) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_154 :: lane_underscore) (lane_2_36 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_154))) (the ((proj_lane__2 lane_2_36))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_152 :: lane_underscore). ((proj_lane__2 lane_1_152) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_34 :: lane_underscore). ((proj_lane__2 lane_2_34) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_152 :: lane_underscore) (lane_2_34 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_152))) (the ((proj_lane__2 lane_2_34))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_151 :: lane_underscore). ((proj_lane__2 lane_1_151) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_33 :: lane_underscore). ((proj_lane__2 lane_2_33) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_151 :: lane_underscore) (lane_2_33 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_151))) (the ((proj_lane__2 lane_2_33))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_85 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_85)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_86 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_86)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I32 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_9 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_158 :: lane_underscore). ((proj_lane__2 lane_1_158) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_40 :: lane_underscore). ((proj_lane__2 lane_2_40) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_158 :: lane_underscore) (lane_2_40 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_158))) (the ((proj_lane__2 lane_2_40))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_156 :: lane_underscore). ((proj_lane__2 lane_1_156) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_38 :: lane_underscore). ((proj_lane__2 lane_2_38) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_156 :: lane_underscore) (lane_2_38 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_156))) (the ((proj_lane__2 lane_2_38))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_155 :: lane_underscore). ((proj_lane__2 lane_1_155) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_37 :: lane_underscore). ((proj_lane__2 lane_2_37) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_155 :: lane_underscore) (lane_2_37 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_155))) (the ((proj_lane__2 lane_2_37))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_87 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_87)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_88 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_88)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I64 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_10 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_162 :: lane_underscore). ((proj_lane__2 lane_1_162) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_44 :: lane_underscore). ((proj_lane__2 lane_2_44) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_162 :: lane_underscore) (lane_2_44 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_162))) (the ((proj_lane__2 lane_2_44))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_160 :: lane_underscore). ((proj_lane__2 lane_1_160) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_42 :: lane_underscore). ((proj_lane__2 lane_2_42) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_160 :: lane_underscore) (lane_2_42 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_160))) (the ((proj_lane__2 lane_2_42))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_159 :: lane_underscore). ((proj_lane__2 lane_1_159) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_41 :: lane_underscore). ((proj_lane__2 lane_2_41) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_159 :: lane_underscore) (lane_2_41 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_159))) (the ((proj_lane__2 lane_2_41))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_89 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_89)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_90 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_90)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I8 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_11 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_166 :: lane_underscore). ((proj_lane__2 lane_1_166) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_48 :: lane_underscore). ((proj_lane__2 lane_2_48) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_166 :: lane_underscore) (lane_2_48 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_166))) (the ((proj_lane__2 lane_2_48))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_164 :: lane_underscore). ((proj_lane__2 lane_1_164) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_46 :: lane_underscore). ((proj_lane__2 lane_2_46) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_164 :: lane_underscore) (lane_2_46 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_164))) (the ((proj_lane__2 lane_2_46))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_163 :: lane_underscore). ((proj_lane__2 lane_1_163) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_45 :: lane_underscore). ((proj_lane__2 lane_2_45) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_163 :: lane_underscore) (lane_2_45 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_163))) (the ((proj_lane__2 lane_2_45))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_91 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_91)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_92 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_92)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I16 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_12 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_170 :: lane_underscore). ((proj_lane__2 lane_1_170) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_52 :: lane_underscore). ((proj_lane__2 lane_2_52) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_170 :: lane_underscore) (lane_2_52 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_170))) (the ((proj_lane__2 lane_2_52))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_168 :: lane_underscore). ((proj_lane__2 lane_1_168) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_50 :: lane_underscore). ((proj_lane__2 lane_2_50) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_168 :: lane_underscore) (lane_2_50 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_168))) (the ((proj_lane__2 lane_2_50))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_167 :: lane_underscore). ((proj_lane__2 lane_1_167) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_49 :: lane_underscore). ((proj_lane__2 lane_2_49) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_167 :: lane_underscore) (lane_2_49 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_167))) (the ((proj_lane__2 lane_2_49))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_93 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_93)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_94 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_94)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I32 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_13 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_174 :: lane_underscore). ((proj_lane__2 lane_1_174) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_56 :: lane_underscore). ((proj_lane__2 lane_2_56) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_174 :: lane_underscore) (lane_2_56 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_174))) (the ((proj_lane__2 lane_2_56))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_172 :: lane_underscore). ((proj_lane__2 lane_1_172) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_54 :: lane_underscore). ((proj_lane__2 lane_2_54) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_172 :: lane_underscore) (lane_2_54 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_172))) (the ((proj_lane__2 lane_2_54))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_171 :: lane_underscore). ((proj_lane__2 lane_1_171) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_53 :: lane_underscore). ((proj_lane__2 lane_2_53) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_171 :: lane_underscore) (lane_2_53 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_171))) (the ((proj_lane__2 lane_2_53))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_95 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_95)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_96 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_96)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I64 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_14 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_178 :: lane_underscore). ((proj_lane__2 lane_1_178) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_60 :: lane_underscore). ((proj_lane__2 lane_2_60) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_178 :: lane_underscore) (lane_2_60 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_178))) (the ((proj_lane__2 lane_2_60))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_176 :: lane_underscore). ((proj_lane__2 lane_1_176) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_58 :: lane_underscore). ((proj_lane__2 lane_2_58) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_176 :: lane_underscore) (lane_2_58 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_176))) (the ((proj_lane__2 lane_2_58))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_175 :: lane_underscore). ((proj_lane__2 lane_1_175) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_57 :: lane_underscore). ((proj_lane__2 lane_2_57) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_175 :: lane_underscore) (lane_2_57 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_175))) (the ((proj_lane__2 lane_2_57))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_97 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_97)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_98 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_98)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I8 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_15 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_182 :: lane_underscore). ((proj_lane__2 lane_1_182) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_64 :: lane_underscore). ((proj_lane__2 lane_2_64) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_182 :: lane_underscore) (lane_2_64 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_182))) (the ((proj_lane__2 lane_2_64))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_180 :: lane_underscore). ((proj_lane__2 lane_1_180) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_62 :: lane_underscore). ((proj_lane__2 lane_2_62) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_180 :: lane_underscore) (lane_2_62 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_180))) (the ((proj_lane__2 lane_2_62))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_179 :: lane_underscore). ((proj_lane__2 lane_1_179) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_61 :: lane_underscore). ((proj_lane__2 lane_2_61) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_179 :: lane_underscore) (lane_2_61 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_179))) (the ((proj_lane__2 lane_2_61))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_99 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_99)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_100 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_100)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I16 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_16 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_186 :: lane_underscore). ((proj_lane__2 lane_1_186) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_68 :: lane_underscore). ((proj_lane__2 lane_2_68) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_186 :: lane_underscore) (lane_2_68 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_186))) (the ((proj_lane__2 lane_2_68))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_184 :: lane_underscore). ((proj_lane__2 lane_1_184) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_66 :: lane_underscore). ((proj_lane__2 lane_2_66) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_184 :: lane_underscore) (lane_2_66 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_184))) (the ((proj_lane__2 lane_2_66))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_183 :: lane_underscore). ((proj_lane__2 lane_1_183) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_65 :: lane_underscore). ((proj_lane__2 lane_2_65) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_183 :: lane_underscore) (lane_2_65 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_183))) (the ((proj_lane__2 lane_2_65))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_101 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_101)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_102 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_102)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I32 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (ADD_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_17 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_190 :: lane_underscore). ((proj_lane__2 lane_1_190) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_72 :: lane_underscore). ((proj_lane__2 lane_2_72) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_190 :: lane_underscore) (lane_2_72 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_190))) (the ((proj_lane__2 lane_2_72))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_188 :: lane_underscore). ((proj_lane__2 lane_1_188) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_70 :: lane_underscore). ((proj_lane__2 lane_2_70) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_188 :: lane_underscore) (lane_2_70 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_188))) (the ((proj_lane__2 lane_2_70))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_187 :: lane_underscore). ((proj_lane__2 lane_1_187) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_69 :: lane_underscore). ((proj_lane__2 lane_2_69) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_187 :: lane_underscore) (lane_2_69 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_187))) (the ((proj_lane__2 lane_2_69))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_103 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_103)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_104 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_104)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I64 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (ADD_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_18 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_194 :: lane_underscore). ((proj_lane__2 lane_1_194) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_76 :: lane_underscore). ((proj_lane__2 lane_2_76) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_194 :: lane_underscore) (lane_2_76 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_194))) (the ((proj_lane__2 lane_2_76))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_192 :: lane_underscore). ((proj_lane__2 lane_1_192) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_74 :: lane_underscore). ((proj_lane__2 lane_2_74) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_192 :: lane_underscore) (lane_2_74 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_192))) (the ((proj_lane__2 lane_2_74))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_191 :: lane_underscore). ((proj_lane__2 lane_1_191) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_73 :: lane_underscore). ((proj_lane__2 lane_2_73) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_191 :: lane_underscore) (lane_2_73 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_191))) (the ((proj_lane__2 lane_2_73))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_105 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_105)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_106 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_106)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I8 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (ADD_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_19 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_198 :: lane_underscore). ((proj_lane__2 lane_1_198) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_80 :: lane_underscore). ((proj_lane__2 lane_2_80) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_198 :: lane_underscore) (lane_2_80 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_198))) (the ((proj_lane__2 lane_2_80))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_196 :: lane_underscore). ((proj_lane__2 lane_1_196) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_78 :: lane_underscore). ((proj_lane__2 lane_2_78) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_196 :: lane_underscore) (lane_2_78 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_196))) (the ((proj_lane__2 lane_2_78))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_195 :: lane_underscore). ((proj_lane__2 lane_1_195) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_77 :: lane_underscore). ((proj_lane__2 lane_2_77) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_195 :: lane_underscore) (lane_2_77 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_195))) (the ((proj_lane__2 lane_2_77))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_107 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_107)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_108 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_108)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I16 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (ADD_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_20 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_202 :: lane_underscore). ((proj_lane__2 lane_1_202) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_84 :: lane_underscore). ((proj_lane__2 lane_2_84) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_202 :: lane_underscore) (lane_2_84 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_202))) (the ((proj_lane__2 lane_2_84))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_200 :: lane_underscore). ((proj_lane__2 lane_1_200) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_82 :: lane_underscore). ((proj_lane__2 lane_2_82) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_200 :: lane_underscore) (lane_2_82 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_200))) (the ((proj_lane__2 lane_2_82))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_199 :: lane_underscore). ((proj_lane__2 lane_1_199) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_81 :: lane_underscore). ((proj_lane__2 lane_2_81) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_199 :: lane_underscore) (lane_2_81 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_199))) (the ((proj_lane__2 lane_2_81))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_109 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_109)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_110 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_110)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I32 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (SUB_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_21 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_206 :: lane_underscore). ((proj_lane__2 lane_1_206) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_88 :: lane_underscore). ((proj_lane__2 lane_2_88) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_206 :: lane_underscore) (lane_2_88 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_206))) (the ((proj_lane__2 lane_2_88))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_204 :: lane_underscore). ((proj_lane__2 lane_1_204) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_86 :: lane_underscore). ((proj_lane__2 lane_2_86) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_204 :: lane_underscore) (lane_2_86 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_204))) (the ((proj_lane__2 lane_2_86))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_203 :: lane_underscore). ((proj_lane__2 lane_1_203) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_85 :: lane_underscore). ((proj_lane__2 lane_2_85) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_203 :: lane_underscore) (lane_2_85 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_203))) (the ((proj_lane__2 lane_2_85))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_111 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_111)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_112 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_112)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I64 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (SUB_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_22 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_210 :: lane_underscore). ((proj_lane__2 lane_1_210) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_92 :: lane_underscore). ((proj_lane__2 lane_2_92) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_210 :: lane_underscore) (lane_2_92 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_210))) (the ((proj_lane__2 lane_2_92))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_208 :: lane_underscore). ((proj_lane__2 lane_1_208) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_90 :: lane_underscore). ((proj_lane__2 lane_2_90) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_208 :: lane_underscore) (lane_2_90 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_208))) (the ((proj_lane__2 lane_2_90))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_207 :: lane_underscore). ((proj_lane__2 lane_1_207) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_89 :: lane_underscore). ((proj_lane__2 lane_2_89) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_207 :: lane_underscore) (lane_2_89 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_207))) (the ((proj_lane__2 lane_2_89))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_113 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_113)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_114 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_114)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I8 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (SUB_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_23 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_214 :: lane_underscore). ((proj_lane__2 lane_1_214) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_96 :: lane_underscore). ((proj_lane__2 lane_2_96) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_214 :: lane_underscore) (lane_2_96 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_214))) (the ((proj_lane__2 lane_2_96))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_212 :: lane_underscore). ((proj_lane__2 lane_1_212) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_94 :: lane_underscore). ((proj_lane__2 lane_2_94) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_212 :: lane_underscore) (lane_2_94 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_212))) (the ((proj_lane__2 lane_2_94))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_211 :: lane_underscore). ((proj_lane__2 lane_1_211) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_93 :: lane_underscore). ((proj_lane__2 lane_2_93) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_211 :: lane_underscore) (lane_2_93 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_211))) (the ((proj_lane__2 lane_2_93))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_115 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_115)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_116 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_116)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (var_0 :: uN). (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (var_2 :: uN). (mk_lane__2 Jnn_I16 var_2)) var_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (SUB_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_24 :
		"list_all (λ (iter_117 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_117)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_118 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_118)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_215 :: lane_underscore). ((proj_lane__2 lane_1_215) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_97 :: lane_underscore). ((proj_lane__2 lane_2_97) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (λ (lane_1_215 :: lane_underscore) (lane_2_97 :: lane_underscore). (mk_lane__2 Jnn_I32 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_215))) (the ((proj_lane__2 lane_2_97)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_216 :: lane_underscore). ((proj_lane__2 lane_1_216) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_98 :: lane_underscore). ((proj_lane__2 lane_2_98) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_216 :: lane_underscore) (lane_2_98 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_216))) (the ((proj_lane__2 lane_2_98))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_218 :: lane_underscore). ((proj_lane__2 lane_1_218) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_100 :: lane_underscore). ((proj_lane__2 lane_2_100) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (λ (lane_1_218 :: lane_underscore) (lane_2_100 :: lane_underscore). (mk_lane__2 Jnn_I32 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_218))) (the ((proj_lane__2 lane_2_100)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 vbinop_Jnn_N_MUL) v128_1 v128_2 [v128]"
	| fun_vbinop__case_25 :
		"list_all (λ (iter_119 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_119)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_120 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_120)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_219 :: lane_underscore). ((proj_lane__2 lane_1_219) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_101 :: lane_underscore). ((proj_lane__2 lane_2_101) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (λ (lane_1_219 :: lane_underscore) (lane_2_101 :: lane_underscore). (mk_lane__2 Jnn_I64 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_219))) (the ((proj_lane__2 lane_2_101)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_220 :: lane_underscore). ((proj_lane__2 lane_1_220) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_102 :: lane_underscore). ((proj_lane__2 lane_2_102) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_220 :: lane_underscore) (lane_2_102 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_220))) (the ((proj_lane__2 lane_2_102))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_222 :: lane_underscore). ((proj_lane__2 lane_1_222) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_104 :: lane_underscore). ((proj_lane__2 lane_2_104) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (λ (lane_1_222 :: lane_underscore) (lane_2_104 :: lane_underscore). (mk_lane__2 Jnn_I64 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_222))) (the ((proj_lane__2 lane_2_104)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 vbinop_Jnn_N_MUL) v128_1 v128_2 [v128]"
	| fun_vbinop__case_26 :
		"list_all (λ (iter_121 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_121)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_122 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_122)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_223 :: lane_underscore). ((proj_lane__2 lane_1_223) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_105 :: lane_underscore). ((proj_lane__2 lane_2_105) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (λ (lane_1_223 :: lane_underscore) (lane_2_105 :: lane_underscore). (mk_lane__2 Jnn_I8 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_223))) (the ((proj_lane__2 lane_2_105)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_224 :: lane_underscore). ((proj_lane__2 lane_1_224) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_106 :: lane_underscore). ((proj_lane__2 lane_2_106) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_224 :: lane_underscore) (lane_2_106 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_224))) (the ((proj_lane__2 lane_2_106))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_226 :: lane_underscore). ((proj_lane__2 lane_1_226) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_108 :: lane_underscore). ((proj_lane__2 lane_2_108) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (λ (lane_1_226 :: lane_underscore) (lane_2_108 :: lane_underscore). (mk_lane__2 Jnn_I8 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_226))) (the ((proj_lane__2 lane_2_108)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 vbinop_Jnn_N_MUL) v128_1 v128_2 [v128]"
	| fun_vbinop__case_27 :
		"list_all (λ (iter_123 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_123)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_124 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_124)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_227 :: lane_underscore). ((proj_lane__2 lane_1_227) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_109 :: lane_underscore). ((proj_lane__2 lane_2_109) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (λ (lane_1_227 :: lane_underscore) (lane_2_109 :: lane_underscore). (mk_lane__2 Jnn_I16 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_227))) (the ((proj_lane__2 lane_2_109)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_228 :: lane_underscore). ((proj_lane__2 lane_1_228) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_110 :: lane_underscore). ((proj_lane__2 lane_2_110) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_228 :: lane_underscore) (lane_2_110 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_228))) (the ((proj_lane__2 lane_2_110))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_230 :: lane_underscore). ((proj_lane__2 lane_1_230) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_112 :: lane_underscore). ((proj_lane__2 lane_2_112) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (λ (lane_1_230 :: lane_underscore) (lane_2_112 :: lane_underscore). (mk_lane__2 Jnn_I16 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_230))) (the ((proj_lane__2 lane_2_112)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 vbinop_Jnn_N_MUL) v128_1 v128_2 [v128]"
	| fun_vbinop__case_28 :
		"list_all (λ (iter_125 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_125)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_126 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_126)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_231 :: lane_underscore). ((proj_lane__2 lane_1_231) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_113 :: lane_underscore). ((proj_lane__2 lane_2_113) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (λ (lane_1_231 :: lane_underscore) (lane_2_113 :: lane_underscore). (mk_lane__2 Jnn_I32 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I32)) U (the ((proj_lane__2 lane_1_231))) (the ((proj_lane__2 lane_2_113)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_232 :: lane_underscore). ((proj_lane__2 lane_1_232) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_114 :: lane_underscore). ((proj_lane__2 lane_2_114) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_232 :: lane_underscore) (lane_2_114 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I32)) U (the ((proj_lane__2 lane_1_232))) (the ((proj_lane__2 lane_2_114))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_234 :: lane_underscore). ((proj_lane__2 lane_1_234) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_116 :: lane_underscore). ((proj_lane__2 lane_2_116) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (λ (lane_1_234 :: lane_underscore) (lane_2_116 :: lane_underscore). (mk_lane__2 Jnn_I32 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I32)) U (the ((proj_lane__2 lane_1_234))) (the ((proj_lane__2 lane_2_116)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 AVGRU) v128_1 v128_2 [v128]"
	| fun_vbinop__case_29 :
		"list_all (λ (iter_127 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_127)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_128 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_128)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_235 :: lane_underscore). ((proj_lane__2 lane_1_235) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_117 :: lane_underscore). ((proj_lane__2 lane_2_117) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (λ (lane_1_235 :: lane_underscore) (lane_2_117 :: lane_underscore). (mk_lane__2 Jnn_I64 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I64)) U (the ((proj_lane__2 lane_1_235))) (the ((proj_lane__2 lane_2_117)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_236 :: lane_underscore). ((proj_lane__2 lane_1_236) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_118 :: lane_underscore). ((proj_lane__2 lane_2_118) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_236 :: lane_underscore) (lane_2_118 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I64)) U (the ((proj_lane__2 lane_1_236))) (the ((proj_lane__2 lane_2_118))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_238 :: lane_underscore). ((proj_lane__2 lane_1_238) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_120 :: lane_underscore). ((proj_lane__2 lane_2_120) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (λ (lane_1_238 :: lane_underscore) (lane_2_120 :: lane_underscore). (mk_lane__2 Jnn_I64 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I64)) U (the ((proj_lane__2 lane_1_238))) (the ((proj_lane__2 lane_2_120)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 AVGRU) v128_1 v128_2 [v128]"
	| fun_vbinop__case_30 :
		"list_all (λ (iter_129 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_129)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_130 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_130)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_239 :: lane_underscore). ((proj_lane__2 lane_1_239) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_121 :: lane_underscore). ((proj_lane__2 lane_2_121) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (λ (lane_1_239 :: lane_underscore) (lane_2_121 :: lane_underscore). (mk_lane__2 Jnn_I8 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I8)) U (the ((proj_lane__2 lane_1_239))) (the ((proj_lane__2 lane_2_121)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_240 :: lane_underscore). ((proj_lane__2 lane_1_240) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_122 :: lane_underscore). ((proj_lane__2 lane_2_122) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_240 :: lane_underscore) (lane_2_122 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I8)) U (the ((proj_lane__2 lane_1_240))) (the ((proj_lane__2 lane_2_122))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_242 :: lane_underscore). ((proj_lane__2 lane_1_242) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_124 :: lane_underscore). ((proj_lane__2 lane_2_124) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (λ (lane_1_242 :: lane_underscore) (lane_2_124 :: lane_underscore). (mk_lane__2 Jnn_I8 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I8)) U (the ((proj_lane__2 lane_1_242))) (the ((proj_lane__2 lane_2_124)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 AVGRU) v128_1 v128_2 [v128]"
	| fun_vbinop__case_31 :
		"list_all (λ (iter_131 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_131)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_132 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_132)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_243 :: lane_underscore). ((proj_lane__2 lane_1_243) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_125 :: lane_underscore). ((proj_lane__2 lane_2_125) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (λ (lane_1_243 :: lane_underscore) (lane_2_125 :: lane_underscore). (mk_lane__2 Jnn_I16 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I16)) U (the ((proj_lane__2 lane_1_243))) (the ((proj_lane__2 lane_2_125)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_244 :: lane_underscore). ((proj_lane__2 lane_1_244) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_126 :: lane_underscore). ((proj_lane__2 lane_2_126) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_244 :: lane_underscore) (lane_2_126 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I16)) U (the ((proj_lane__2 lane_1_244))) (the ((proj_lane__2 lane_2_126))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_246 :: lane_underscore). ((proj_lane__2 lane_1_246) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_128 :: lane_underscore). ((proj_lane__2 lane_2_128) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (λ (lane_1_246 :: lane_underscore) (lane_2_128 :: lane_underscore). (mk_lane__2 Jnn_I16 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I16)) U (the ((proj_lane__2 lane_1_246))) (the ((proj_lane__2 lane_2_128)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 AVGRU) v128_1 v128_2 [v128]"
	| fun_vbinop__case_32 :
		"list_all (λ (iter_133 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_133)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_134 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_134)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_247 :: lane_underscore). ((proj_lane__2 lane_1_247) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_129 :: lane_underscore). ((proj_lane__2 lane_2_129) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (λ (lane_1_247 :: lane_underscore) (lane_2_129 :: lane_underscore). (mk_lane__2 Jnn_I32 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) S (the ((proj_lane__2 lane_1_247))) (the ((proj_lane__2 lane_2_129)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_248 :: lane_underscore). ((proj_lane__2 lane_1_248) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_130 :: lane_underscore). ((proj_lane__2 lane_2_130) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_248 :: lane_underscore) (lane_2_130 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) S (the ((proj_lane__2 lane_1_248))) (the ((proj_lane__2 lane_2_130))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_250 :: lane_underscore). ((proj_lane__2 lane_1_250) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_132 :: lane_underscore). ((proj_lane__2 lane_2_132) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (λ (lane_1_250 :: lane_underscore) (lane_2_132 :: lane_underscore). (mk_lane__2 Jnn_I32 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) S (the ((proj_lane__2 lane_1_250))) (the ((proj_lane__2 lane_2_132)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 Q15MULR_SATS) v128_1 v128_2 [v128]"
	| fun_vbinop__case_33 :
		"list_all (λ (iter_135 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_135)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_136 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_136)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_251 :: lane_underscore). ((proj_lane__2 lane_1_251) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_133 :: lane_underscore). ((proj_lane__2 lane_2_133) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (λ (lane_1_251 :: lane_underscore) (lane_2_133 :: lane_underscore). (mk_lane__2 Jnn_I64 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) S (the ((proj_lane__2 lane_1_251))) (the ((proj_lane__2 lane_2_133)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_252 :: lane_underscore). ((proj_lane__2 lane_1_252) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_134 :: lane_underscore). ((proj_lane__2 lane_2_134) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_252 :: lane_underscore) (lane_2_134 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) S (the ((proj_lane__2 lane_1_252))) (the ((proj_lane__2 lane_2_134))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_254 :: lane_underscore). ((proj_lane__2 lane_1_254) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_136 :: lane_underscore). ((proj_lane__2 lane_2_136) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (λ (lane_1_254 :: lane_underscore) (lane_2_136 :: lane_underscore). (mk_lane__2 Jnn_I64 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) S (the ((proj_lane__2 lane_1_254))) (the ((proj_lane__2 lane_2_136)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 Q15MULR_SATS) v128_1 v128_2 [v128]"
	| fun_vbinop__case_34 :
		"list_all (λ (iter_137 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_137)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_138 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_138)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_255 :: lane_underscore). ((proj_lane__2 lane_1_255) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_137 :: lane_underscore). ((proj_lane__2 lane_2_137) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (λ (lane_1_255 :: lane_underscore) (lane_2_137 :: lane_underscore). (mk_lane__2 Jnn_I8 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) S (the ((proj_lane__2 lane_1_255))) (the ((proj_lane__2 lane_2_137)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_256 :: lane_underscore). ((proj_lane__2 lane_1_256) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_138 :: lane_underscore). ((proj_lane__2 lane_2_138) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_256 :: lane_underscore) (lane_2_138 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) S (the ((proj_lane__2 lane_1_256))) (the ((proj_lane__2 lane_2_138))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_258 :: lane_underscore). ((proj_lane__2 lane_1_258) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_140 :: lane_underscore). ((proj_lane__2 lane_2_140) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (λ (lane_1_258 :: lane_underscore) (lane_2_140 :: lane_underscore). (mk_lane__2 Jnn_I8 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) S (the ((proj_lane__2 lane_1_258))) (the ((proj_lane__2 lane_2_140)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 Q15MULR_SATS) v128_1 v128_2 [v128]"
	| fun_vbinop__case_35 :
		"list_all (λ (iter_139 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_139)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_140 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_140)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (lane_1_259 :: lane_underscore). ((proj_lane__2 lane_1_259) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_141 :: lane_underscore). ((proj_lane__2 lane_2_141) ≠ None)) lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (λ (lane_1_259 :: lane_underscore) (lane_2_141 :: lane_underscore). (mk_lane__2 Jnn_I16 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) S (the ((proj_lane__2 lane_1_259))) (the ((proj_lane__2 lane_2_141)))))) lane_1_lst lane_2_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_260 :: lane_underscore). ((proj_lane__2 lane_1_260) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_142 :: lane_underscore). ((proj_lane__2 lane_2_142) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_260 :: lane_underscore) (lane_2_142 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) S (the ((proj_lane__2 lane_1_260))) (the ((proj_lane__2 lane_2_142))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_262 :: lane_underscore). ((proj_lane__2 lane_1_262) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_144 :: lane_underscore). ((proj_lane__2 lane_2_144) ≠ None)) lane_2_lst ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (λ (lane_1_262 :: lane_underscore) (lane_2_144 :: lane_underscore). (mk_lane__2 Jnn_I16 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) S (the ((proj_lane__2 lane_1_262))) (the ((proj_lane__2 lane_2_144)))))) lane_1_lst lane_2_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 Q15MULR_SATS) v128_1 v128_2 [v128]"
	| fun_vbinop__case_36 :
		"list_all (λ (lane_lst_57 :: (lane_underscore list)). list_all (λ (lane_57 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_57)) lane_lst_57) lane_lst_lst ⟹
		 list_all (λ (iter_141 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_141)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_142 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_142)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_143 :: (lane_underscore list)). list_all (λ (iter_144 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_144)) iter_143) (setproduct_underscore  (list_zipWith (λ (lane_1_263 :: lane_underscore) (lane_2_145 :: lane_underscore). (map (λ (iter_0_91 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_91))) (fadd_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_263)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_145))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_264 :: lane_underscore) (lane_2_146 :: lane_underscore). list_all (λ (iter_145 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_145)) (fadd_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_264)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_146)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_58 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_58))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_265 :: lane_underscore) (lane_2_147 :: lane_underscore). list_all (λ (iter_0_92 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_92)))) (fadd_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_265)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_147)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_267 :: lane_underscore) (lane_2_149 :: lane_underscore). (map (λ (iter_0_93 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_93))) (fadd_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_267)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_149))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_60 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_60)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_ADD) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_37 :
		"list_all (λ (lane_lst_61 :: (lane_underscore list)). list_all (λ (lane_61 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_61)) lane_lst_61) lane_lst_lst ⟹
		 list_all (λ (iter_146 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_146)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_147 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_147)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_148 :: (lane_underscore list)). list_all (λ (iter_149 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_149)) iter_148) (setproduct_underscore  (list_zipWith (λ (lane_1_268 :: lane_underscore) (lane_2_150 :: lane_underscore). (map (λ (iter_0_94 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_94))) (fadd_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_268)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_150))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_269 :: lane_underscore) (lane_2_151 :: lane_underscore). list_all (λ (iter_150 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_150)) (fadd_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_269)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_151)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_62 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_62))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_270 :: lane_underscore) (lane_2_152 :: lane_underscore). list_all (λ (iter_0_95 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_95)))) (fadd_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_270)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_152)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_272 :: lane_underscore) (lane_2_154 :: lane_underscore). (map (λ (iter_0_96 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_96))) (fadd_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_272)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_154))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_64 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_64)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_ADD) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_38 :
		"list_all (λ (lane_lst_65 :: (lane_underscore list)). list_all (λ (lane_65 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_65)) lane_lst_65) lane_lst_lst ⟹
		 list_all (λ (iter_151 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_151)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_152 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_152)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_153 :: (lane_underscore list)). list_all (λ (iter_154 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_154)) iter_153) (setproduct_underscore  (list_zipWith (λ (lane_1_273 :: lane_underscore) (lane_2_155 :: lane_underscore). (map (λ (iter_0_97 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_97))) (fsub_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_273)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_155))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_274 :: lane_underscore) (lane_2_156 :: lane_underscore). list_all (λ (iter_155 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_155)) (fsub_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_274)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_156)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_66 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_66))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_275 :: lane_underscore) (lane_2_157 :: lane_underscore). list_all (λ (iter_0_98 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_98)))) (fsub_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_275)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_157)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_277 :: lane_underscore) (lane_2_159 :: lane_underscore). (map (λ (iter_0_99 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_99))) (fsub_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_277)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_159))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_68 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_68)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_SUB) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_39 :
		"list_all (λ (lane_lst_69 :: (lane_underscore list)). list_all (λ (lane_69 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_69)) lane_lst_69) lane_lst_lst ⟹
		 list_all (λ (iter_156 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_156)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_157 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_157)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_158 :: (lane_underscore list)). list_all (λ (iter_159 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_159)) iter_158) (setproduct_underscore  (list_zipWith (λ (lane_1_278 :: lane_underscore) (lane_2_160 :: lane_underscore). (map (λ (iter_0_100 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_100))) (fsub_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_278)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_160))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_279 :: lane_underscore) (lane_2_161 :: lane_underscore). list_all (λ (iter_160 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_160)) (fsub_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_279)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_161)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_70 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_70))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_280 :: lane_underscore) (lane_2_162 :: lane_underscore). list_all (λ (iter_0_101 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_101)))) (fsub_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_280)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_162)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_282 :: lane_underscore) (lane_2_164 :: lane_underscore). (map (λ (iter_0_102 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_102))) (fsub_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_282)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_164))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_72 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_72)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_SUB) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_40 :
		"list_all (λ (lane_lst_73 :: (lane_underscore list)). list_all (λ (lane_73 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_73)) lane_lst_73) lane_lst_lst ⟹
		 list_all (λ (iter_161 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_161)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_162 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_162)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_163 :: (lane_underscore list)). list_all (λ (iter_164 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_164)) iter_163) (setproduct_underscore  (list_zipWith (λ (lane_1_283 :: lane_underscore) (lane_2_165 :: lane_underscore). (map (λ (iter_0_103 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_103))) (fmul_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_283)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_165))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_284 :: lane_underscore) (lane_2_166 :: lane_underscore). list_all (λ (iter_165 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_165)) (fmul_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_284)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_166)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_74 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_74))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_285 :: lane_underscore) (lane_2_167 :: lane_underscore). list_all (λ (iter_0_104 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_104)))) (fmul_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_285)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_167)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_287 :: lane_underscore) (lane_2_169 :: lane_underscore). (map (λ (iter_0_105 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_105))) (fmul_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_287)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_169))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_76 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_76)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_MUL) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_41 :
		"list_all (λ (lane_lst_77 :: (lane_underscore list)). list_all (λ (lane_77 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_77)) lane_lst_77) lane_lst_lst ⟹
		 list_all (λ (iter_166 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_166)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_167 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_167)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_168 :: (lane_underscore list)). list_all (λ (iter_169 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_169)) iter_168) (setproduct_underscore  (list_zipWith (λ (lane_1_288 :: lane_underscore) (lane_2_170 :: lane_underscore). (map (λ (iter_0_106 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_106))) (fmul_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_288)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_170))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_289 :: lane_underscore) (lane_2_171 :: lane_underscore). list_all (λ (iter_170 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_170)) (fmul_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_289)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_171)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_78 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_78))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_290 :: lane_underscore) (lane_2_172 :: lane_underscore). list_all (λ (iter_0_107 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_107)))) (fmul_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_290)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_172)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_292 :: lane_underscore) (lane_2_174 :: lane_underscore). (map (λ (iter_0_108 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_108))) (fmul_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_292)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_174))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_80 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_80)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_MUL) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_42 :
		"list_all (λ (lane_lst_81 :: (lane_underscore list)). list_all (λ (lane_81 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_81)) lane_lst_81) lane_lst_lst ⟹
		 list_all (λ (iter_171 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_171)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_172 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_172)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_173 :: (lane_underscore list)). list_all (λ (iter_174 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_174)) iter_173) (setproduct_underscore  (list_zipWith (λ (lane_1_293 :: lane_underscore) (lane_2_175 :: lane_underscore). (map (λ (iter_0_109 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_109))) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_293)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_175))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_294 :: lane_underscore) (lane_2_176 :: lane_underscore). list_all (λ (iter_175 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_175)) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_294)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_176)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_82 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_82))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_295 :: lane_underscore) (lane_2_177 :: lane_underscore). list_all (λ (iter_0_110 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_110)))) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_295)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_177)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_297 :: lane_underscore) (lane_2_179 :: lane_underscore). (map (λ (iter_0_111 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_111))) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_297)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_179))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_84 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_84)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_DIV) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_43 :
		"list_all (λ (lane_lst_85 :: (lane_underscore list)). list_all (λ (lane_85 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_85)) lane_lst_85) lane_lst_lst ⟹
		 list_all (λ (iter_176 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_176)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_177 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_177)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_178 :: (lane_underscore list)). list_all (λ (iter_179 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_179)) iter_178) (setproduct_underscore  (list_zipWith (λ (lane_1_298 :: lane_underscore) (lane_2_180 :: lane_underscore). (map (λ (iter_0_112 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_112))) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_298)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_180))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_299 :: lane_underscore) (lane_2_181 :: lane_underscore). list_all (λ (iter_180 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_180)) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_299)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_181)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_86 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_86))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_300 :: lane_underscore) (lane_2_182 :: lane_underscore). list_all (λ (iter_0_113 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_113)))) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_300)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_182)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_302 :: lane_underscore) (lane_2_184 :: lane_underscore). (map (λ (iter_0_114 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_114))) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_302)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_184))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_88 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_88)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_DIV) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_44 :
		"list_all (λ (lane_lst_89 :: (lane_underscore list)). list_all (λ (lane_89 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_89)) lane_lst_89) lane_lst_lst ⟹
		 list_all (λ (iter_181 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_181)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_182 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_182)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_183 :: (lane_underscore list)). list_all (λ (iter_184 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_184)) iter_183) (setproduct_underscore  (list_zipWith (λ (lane_1_303 :: lane_underscore) (lane_2_185 :: lane_underscore). (map (λ (iter_0_115 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_115))) (fmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_303)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_185))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_304 :: lane_underscore) (lane_2_186 :: lane_underscore). list_all (λ (iter_185 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_185)) (fmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_304)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_186)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_90 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_90))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_305 :: lane_underscore) (lane_2_187 :: lane_underscore). list_all (λ (iter_0_116 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_116)))) (fmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_305)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_187)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_307 :: lane_underscore) (lane_2_189 :: lane_underscore). (map (λ (iter_0_117 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_117))) (fmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_307)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_189))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_92 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_92)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_MIN) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_45 :
		"list_all (λ (lane_lst_93 :: (lane_underscore list)). list_all (λ (lane_93 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_93)) lane_lst_93) lane_lst_lst ⟹
		 list_all (λ (iter_186 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_186)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_187 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_187)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_188 :: (lane_underscore list)). list_all (λ (iter_189 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_189)) iter_188) (setproduct_underscore  (list_zipWith (λ (lane_1_308 :: lane_underscore) (lane_2_190 :: lane_underscore). (map (λ (iter_0_118 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_118))) (fmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_308)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_190))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_309 :: lane_underscore) (lane_2_191 :: lane_underscore). list_all (λ (iter_190 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_190)) (fmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_309)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_191)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_94 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_94))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_310 :: lane_underscore) (lane_2_192 :: lane_underscore). list_all (λ (iter_0_119 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_119)))) (fmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_310)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_192)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_312 :: lane_underscore) (lane_2_194 :: lane_underscore). (map (λ (iter_0_120 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_120))) (fmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_312)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_194))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_96 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_96)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_MIN) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_46 :
		"list_all (λ (lane_lst_97 :: (lane_underscore list)). list_all (λ (lane_97 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_97)) lane_lst_97) lane_lst_lst ⟹
		 list_all (λ (iter_191 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_191)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_192 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_192)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_193 :: (lane_underscore list)). list_all (λ (iter_194 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_194)) iter_193) (setproduct_underscore  (list_zipWith (λ (lane_1_313 :: lane_underscore) (lane_2_195 :: lane_underscore). (map (λ (iter_0_121 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_121))) (fmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_313)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_195))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_314 :: lane_underscore) (lane_2_196 :: lane_underscore). list_all (λ (iter_195 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_195)) (fmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_314)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_196)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_98 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_98))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_315 :: lane_underscore) (lane_2_197 :: lane_underscore). list_all (λ (iter_0_122 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_122)))) (fmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_315)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_197)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_317 :: lane_underscore) (lane_2_199 :: lane_underscore). (map (λ (iter_0_123 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_123))) (fmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_317)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_199))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_100 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_100)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_MAX) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_47 :
		"list_all (λ (lane_lst_101 :: (lane_underscore list)). list_all (λ (lane_101 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_101)) lane_lst_101) lane_lst_lst ⟹
		 list_all (λ (iter_196 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_196)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_197 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_197)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_198 :: (lane_underscore list)). list_all (λ (iter_199 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_199)) iter_198) (setproduct_underscore  (list_zipWith (λ (lane_1_318 :: lane_underscore) (lane_2_200 :: lane_underscore). (map (λ (iter_0_124 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_124))) (fmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_318)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_200))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_319 :: lane_underscore) (lane_2_201 :: lane_underscore). list_all (λ (iter_200 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_200)) (fmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_319)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_201)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_102 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_102))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_320 :: lane_underscore) (lane_2_202 :: lane_underscore). list_all (λ (iter_0_125 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_125)))) (fmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_320)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_202)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_322 :: lane_underscore) (lane_2_204 :: lane_underscore). (map (λ (iter_0_126 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_126))) (fmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_322)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_204))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_104 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_104)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_MAX) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_48 :
		"list_all (λ (lane_lst_105 :: (lane_underscore list)). list_all (λ (lane_105 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_105)) lane_lst_105) lane_lst_lst ⟹
		 list_all (λ (iter_201 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_201)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_202 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_202)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_203 :: (lane_underscore list)). list_all (λ (iter_204 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_204)) iter_203) (setproduct_underscore  (list_zipWith (λ (lane_1_323 :: lane_underscore) (lane_2_205 :: lane_underscore). (map (λ (iter_0_127 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_127))) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_323)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_205))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_324 :: lane_underscore) (lane_2_206 :: lane_underscore). list_all (λ (iter_205 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_205)) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_324)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_206)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_106 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_106))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_325 :: lane_underscore) (lane_2_207 :: lane_underscore). list_all (λ (iter_0_128 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_128)))) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_325)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_207)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_327 :: lane_underscore) (lane_2_209 :: lane_underscore). (map (λ (iter_0_129 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_129))) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_327)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_209))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_108 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_108)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 PMIN) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_49 :
		"list_all (λ (lane_lst_109 :: (lane_underscore list)). list_all (λ (lane_109 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_109)) lane_lst_109) lane_lst_lst ⟹
		 list_all (λ (iter_206 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_206)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_207 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_207)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_208 :: (lane_underscore list)). list_all (λ (iter_209 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_209)) iter_208) (setproduct_underscore  (list_zipWith (λ (lane_1_328 :: lane_underscore) (lane_2_210 :: lane_underscore). (map (λ (iter_0_130 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_130))) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_328)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_210))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_329 :: lane_underscore) (lane_2_211 :: lane_underscore). list_all (λ (iter_210 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_210)) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_329)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_211)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_110 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_110))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_330 :: lane_underscore) (lane_2_212 :: lane_underscore). list_all (λ (iter_0_131 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_131)))) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_330)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_212)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_332 :: lane_underscore) (lane_2_214 :: lane_underscore). (map (λ (iter_0_132 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_132))) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_332)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_214))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_112 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_112)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 PMIN) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_50 :
		"list_all (λ (lane_lst_113 :: (lane_underscore list)). list_all (λ (lane_113 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) lane_113)) lane_lst_113) lane_lst_lst ⟹
		 list_all (λ (iter_211 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_211)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_212 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_212)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_213 :: (lane_underscore list)). list_all (λ (iter_214 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F32) iter_214)) iter_213) (setproduct_underscore  (list_zipWith (λ (lane_1_333 :: lane_underscore) (lane_2_215 :: lane_underscore). (map (λ (iter_0_133 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_133))) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_333)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_215))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_334 :: lane_underscore) (lane_2_216 :: lane_underscore). list_all (λ (iter_215 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F32)) iter_215)) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_334)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_216)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_114 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_114))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_335 :: lane_underscore) (lane_2_217 :: lane_underscore). list_all (λ (iter_0_134 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_134)))) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_335)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_217)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_337 :: lane_underscore) (lane_2_219 :: lane_underscore). (map (λ (iter_0_135 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_135))) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_337)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_219))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_116 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_116)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 PMAX) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_51 :
		"list_all (λ (lane_lst_117 :: (lane_underscore list)). list_all (λ (lane_117 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) lane_117)) lane_lst_117) lane_lst_lst ⟹
		 list_all (λ (iter_216 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_216)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_217 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_217)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (iter_218 :: (lane_underscore list)). list_all (λ (iter_219 :: lane_underscore). (wf_lane_underscore (lanetype_Fnn Fnn_F64) iter_219)) iter_218) (setproduct_underscore  (list_zipWith (λ (lane_1_338 :: lane_underscore) (lane_2_220 :: lane_underscore). (map (λ (iter_0_136 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_136))) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_338)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_220))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all2 (λ (lane_1_339 :: lane_underscore) (lane_2_221 :: lane_underscore). list_all (λ (iter_220 :: fN). (wf_fN (sizenn (numtype_Fnn Fnn_F64)) iter_220)) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_339)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_221)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_lst_118 :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_118))) lane_lst_lst ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all2 (λ (lane_1_340 :: lane_underscore) (lane_2_222 :: lane_underscore). list_all (λ (iter_0_137 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_137)))) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_340)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_222)))))))) lane_1_lst lane_2_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ⟹
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (λ (lane_1_342 :: lane_underscore) (lane_2_224 :: lane_underscore). (map (λ (iter_0_138 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_138))) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_342)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_224))))))))) lane_1_lst lane_2_lst))) ⟹
		 (v128_lst = (map (λ (lane_lst_120 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_120)) lane_lst_lst)) ⟹
		 (v_M = M_0) ⟹
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 PMAX) v128_1 v128_2 v128_lst"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:381.6-381.14 *)
inductive fun_vrelop_underscore :: "shape ⇒ vrelop_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ bool" where
	  fun_vrelop__case_0 :
		"list_all (λ (iter_221 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_221)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_222 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_222)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_343 :: lane_underscore). ((proj_lane__2 lane_1_343) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_225 :: lane_underscore). ((proj_lane__2 lane_2_225) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_343 :: lane_underscore) (lane_2_225 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I32)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_343))) (the ((proj_lane__2 lane_2_225))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_3_1 :: iN). (mk_lane__2 Jnn_I32 lane_3_1)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_344 :: lane_underscore). ((proj_lane__2 lane_1_344) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_226 :: lane_underscore). ((proj_lane__2 lane_2_226) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_344 :: lane_underscore) (lane_2_226 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_344))) (the ((proj_lane__2 lane_2_226)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_3_2 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_2))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_346 :: lane_underscore). ((proj_lane__2 lane_1_346) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_228 :: lane_underscore). ((proj_lane__2 lane_2_228) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_346 :: lane_underscore) (lane_2_228 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_346))) (the ((proj_lane__2 lane_2_228)))))))) lane_1_lst lane_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_3_4 :: iN). (mk_lane__2 Jnn_I32 lane_3_4)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 vrelop_Jnn_N_EQ) v128_1 v128_2 v128"
	| fun_vrelop__case_1 :
		"list_all (λ (iter_223 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_223)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_224 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_224)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_347 :: lane_underscore). ((proj_lane__2 lane_1_347) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_229 :: lane_underscore). ((proj_lane__2 lane_2_229) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_347 :: lane_underscore) (lane_2_229 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I64)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_347))) (the ((proj_lane__2 lane_2_229))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_3_5 :: iN). (mk_lane__2 Jnn_I64 lane_3_5)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_348 :: lane_underscore). ((proj_lane__2 lane_1_348) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_230 :: lane_underscore). ((proj_lane__2 lane_2_230) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_348 :: lane_underscore) (lane_2_230 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_348))) (the ((proj_lane__2 lane_2_230)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_3_6 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_6))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_350 :: lane_underscore). ((proj_lane__2 lane_1_350) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_232 :: lane_underscore). ((proj_lane__2 lane_2_232) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_350 :: lane_underscore) (lane_2_232 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_350))) (the ((proj_lane__2 lane_2_232)))))))) lane_1_lst lane_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_3_8 :: iN). (mk_lane__2 Jnn_I64 lane_3_8)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 vrelop_Jnn_N_EQ) v128_1 v128_2 v128"
	| fun_vrelop__case_2 :
		"list_all (λ (iter_225 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_225)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_226 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_226)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_351 :: lane_underscore). ((proj_lane__2 lane_1_351) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_233 :: lane_underscore). ((proj_lane__2 lane_2_233) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_351 :: lane_underscore) (lane_2_233 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I8)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_351))) (the ((proj_lane__2 lane_2_233))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_3_9 :: iN). (mk_lane__2 Jnn_I8 lane_3_9)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_352 :: lane_underscore). ((proj_lane__2 lane_1_352) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_234 :: lane_underscore). ((proj_lane__2 lane_2_234) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_352 :: lane_underscore) (lane_2_234 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_352))) (the ((proj_lane__2 lane_2_234)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_3_10 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_10))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_354 :: lane_underscore). ((proj_lane__2 lane_1_354) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_236 :: lane_underscore). ((proj_lane__2 lane_2_236) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_354 :: lane_underscore) (lane_2_236 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_354))) (the ((proj_lane__2 lane_2_236)))))))) lane_1_lst lane_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_3_12 :: iN). (mk_lane__2 Jnn_I8 lane_3_12)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 vrelop_Jnn_N_EQ) v128_1 v128_2 v128"
	| fun_vrelop__case_3 :
		"list_all (λ (iter_227 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_227)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_228 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_228)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_355 :: lane_underscore). ((proj_lane__2 lane_1_355) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_237 :: lane_underscore). ((proj_lane__2 lane_2_237) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_355 :: lane_underscore) (lane_2_237 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I16)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_355))) (the ((proj_lane__2 lane_2_237))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_3_13 :: iN). (mk_lane__2 Jnn_I16 lane_3_13)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_356 :: lane_underscore). ((proj_lane__2 lane_1_356) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_238 :: lane_underscore). ((proj_lane__2 lane_2_238) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_356 :: lane_underscore) (lane_2_238 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_356))) (the ((proj_lane__2 lane_2_238)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_3_14 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_14))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_358 :: lane_underscore). ((proj_lane__2 lane_1_358) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_240 :: lane_underscore). ((proj_lane__2 lane_2_240) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_358 :: lane_underscore) (lane_2_240 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_358))) (the ((proj_lane__2 lane_2_240)))))))) lane_1_lst lane_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_3_16 :: iN). (mk_lane__2 Jnn_I16 lane_3_16)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 vrelop_Jnn_N_EQ) v128_1 v128_2 v128"
	| fun_vrelop__case_4 :
		"list_all (λ (iter_229 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_229)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_230 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_230)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_359 :: lane_underscore). ((proj_lane__2 lane_1_359) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_241 :: lane_underscore). ((proj_lane__2 lane_2_241) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_359 :: lane_underscore) (lane_2_241 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I32)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_359))) (the ((proj_lane__2 lane_2_241))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_3_17 :: iN). (mk_lane__2 Jnn_I32 lane_3_17)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_360 :: lane_underscore). ((proj_lane__2 lane_1_360) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_242 :: lane_underscore). ((proj_lane__2 lane_2_242) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_360 :: lane_underscore) (lane_2_242 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_360))) (the ((proj_lane__2 lane_2_242)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_3_18 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_18))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_362 :: lane_underscore). ((proj_lane__2 lane_1_362) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_244 :: lane_underscore). ((proj_lane__2 lane_2_244) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_362 :: lane_underscore) (lane_2_244 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_362))) (the ((proj_lane__2 lane_2_244)))))))) lane_1_lst lane_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_3_20 :: iN). (mk_lane__2 Jnn_I32 lane_3_20)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 vrelop_Jnn_N_NE) v128_1 v128_2 v128"
	| fun_vrelop__case_5 :
		"list_all (λ (iter_231 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_231)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_232 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_232)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_363 :: lane_underscore). ((proj_lane__2 lane_1_363) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_245 :: lane_underscore). ((proj_lane__2 lane_2_245) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_363 :: lane_underscore) (lane_2_245 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I64)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_363))) (the ((proj_lane__2 lane_2_245))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_3_21 :: iN). (mk_lane__2 Jnn_I64 lane_3_21)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_364 :: lane_underscore). ((proj_lane__2 lane_1_364) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_246 :: lane_underscore). ((proj_lane__2 lane_2_246) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_364 :: lane_underscore) (lane_2_246 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_364))) (the ((proj_lane__2 lane_2_246)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_3_22 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_22))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_366 :: lane_underscore). ((proj_lane__2 lane_1_366) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_248 :: lane_underscore). ((proj_lane__2 lane_2_248) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_366 :: lane_underscore) (lane_2_248 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_366))) (the ((proj_lane__2 lane_2_248)))))))) lane_1_lst lane_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_3_24 :: iN). (mk_lane__2 Jnn_I64 lane_3_24)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 vrelop_Jnn_N_NE) v128_1 v128_2 v128"
	| fun_vrelop__case_6 :
		"list_all (λ (iter_233 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_233)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_234 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_234)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_367 :: lane_underscore). ((proj_lane__2 lane_1_367) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_249 :: lane_underscore). ((proj_lane__2 lane_2_249) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_367 :: lane_underscore) (lane_2_249 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I8)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_367))) (the ((proj_lane__2 lane_2_249))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_3_25 :: iN). (mk_lane__2 Jnn_I8 lane_3_25)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_368 :: lane_underscore). ((proj_lane__2 lane_1_368) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_250 :: lane_underscore). ((proj_lane__2 lane_2_250) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_368 :: lane_underscore) (lane_2_250 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_368))) (the ((proj_lane__2 lane_2_250)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_3_26 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_26))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_370 :: lane_underscore). ((proj_lane__2 lane_1_370) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_252 :: lane_underscore). ((proj_lane__2 lane_2_252) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_370 :: lane_underscore) (lane_2_252 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_370))) (the ((proj_lane__2 lane_2_252)))))))) lane_1_lst lane_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_3_28 :: iN). (mk_lane__2 Jnn_I8 lane_3_28)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 vrelop_Jnn_N_NE) v128_1 v128_2 v128"
	| fun_vrelop__case_7 :
		"list_all (λ (iter_235 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_235)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_236 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_236)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_371 :: lane_underscore). ((proj_lane__2 lane_1_371) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_253 :: lane_underscore). ((proj_lane__2 lane_2_253) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_371 :: lane_underscore) (lane_2_253 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_I16)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_371))) (the ((proj_lane__2 lane_2_253))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_3_29 :: iN). (mk_lane__2 Jnn_I16 lane_3_29)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_372 :: lane_underscore). ((proj_lane__2 lane_1_372) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_254 :: lane_underscore). ((proj_lane__2 lane_2_254) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_372 :: lane_underscore) (lane_2_254 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_372))) (the ((proj_lane__2 lane_2_254)))))))) lane_1_lst lane_2_lst ⟹
		 list_all (λ (lane_3_30 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_30))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_374 :: lane_underscore). ((proj_lane__2 lane_1_374) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_256 :: lane_underscore). ((proj_lane__2 lane_2_256) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_374 :: lane_underscore) (lane_2_256 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_374))) (the ((proj_lane__2 lane_2_256)))))))) lane_1_lst lane_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_3_32 :: iN). (mk_lane__2 Jnn_I16 lane_3_32)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 vrelop_Jnn_N_NE) v128_1 v128_2 v128"
	| fun_vrelop__case_8 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_378 :: lane_underscore). ((proj_lane__2 lane_1_378) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_260 :: lane_underscore). ((proj_lane__2 lane_2_260) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_378 :: lane_underscore) (lane_2_260 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_378))) (the ((proj_lane__2 lane_2_260))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_376 :: lane_underscore). ((proj_lane__2 lane_1_376) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_258 :: lane_underscore). ((proj_lane__2 lane_2_258) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_376 :: lane_underscore) (lane_2_258 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_376))) (the ((proj_lane__2 lane_2_258))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_375 :: lane_underscore). ((proj_lane__2 lane_1_375) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_257 :: lane_underscore). ((proj_lane__2 lane_2_257) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_375 :: lane_underscore) (lane_2_257 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_375))) (the ((proj_lane__2 lane_2_257))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_237 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_237)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_238 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_238)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I32)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_3_33 :: iN). (mk_lane__2 Jnn_I32 lane_3_33)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_34 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_34))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_3_36 :: iN). (mk_lane__2 Jnn_I32 lane_3_36)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_9 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_382 :: lane_underscore). ((proj_lane__2 lane_1_382) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_264 :: lane_underscore). ((proj_lane__2 lane_2_264) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_382 :: lane_underscore) (lane_2_264 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_382))) (the ((proj_lane__2 lane_2_264))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_380 :: lane_underscore). ((proj_lane__2 lane_1_380) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_262 :: lane_underscore). ((proj_lane__2 lane_2_262) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_380 :: lane_underscore) (lane_2_262 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_380))) (the ((proj_lane__2 lane_2_262))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_379 :: lane_underscore). ((proj_lane__2 lane_1_379) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_261 :: lane_underscore). ((proj_lane__2 lane_2_261) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_379 :: lane_underscore) (lane_2_261 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_379))) (the ((proj_lane__2 lane_2_261))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_239 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_239)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_240 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_240)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I64)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_3_37 :: iN). (mk_lane__2 Jnn_I64 lane_3_37)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_38 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_38))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_3_40 :: iN). (mk_lane__2 Jnn_I64 lane_3_40)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_10 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_386 :: lane_underscore). ((proj_lane__2 lane_1_386) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_268 :: lane_underscore). ((proj_lane__2 lane_2_268) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_386 :: lane_underscore) (lane_2_268 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_386))) (the ((proj_lane__2 lane_2_268))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_384 :: lane_underscore). ((proj_lane__2 lane_1_384) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_266 :: lane_underscore). ((proj_lane__2 lane_2_266) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_384 :: lane_underscore) (lane_2_266 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_384))) (the ((proj_lane__2 lane_2_266))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_383 :: lane_underscore). ((proj_lane__2 lane_1_383) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_265 :: lane_underscore). ((proj_lane__2 lane_2_265) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_383 :: lane_underscore) (lane_2_265 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_383))) (the ((proj_lane__2 lane_2_265))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_241 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_241)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_242 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_242)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I8)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_3_41 :: iN). (mk_lane__2 Jnn_I8 lane_3_41)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_42 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_42))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_3_44 :: iN). (mk_lane__2 Jnn_I8 lane_3_44)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_11 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_390 :: lane_underscore). ((proj_lane__2 lane_1_390) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_272 :: lane_underscore). ((proj_lane__2 lane_2_272) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_390 :: lane_underscore) (lane_2_272 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_390))) (the ((proj_lane__2 lane_2_272))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_388 :: lane_underscore). ((proj_lane__2 lane_1_388) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_270 :: lane_underscore). ((proj_lane__2 lane_2_270) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_388 :: lane_underscore) (lane_2_270 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_388))) (the ((proj_lane__2 lane_2_270))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_387 :: lane_underscore). ((proj_lane__2 lane_1_387) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_269 :: lane_underscore). ((proj_lane__2 lane_2_269) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_387 :: lane_underscore) (lane_2_269 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_387))) (the ((proj_lane__2 lane_2_269))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_243 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_243)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_244 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_244)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I16)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_3_45 :: iN). (mk_lane__2 Jnn_I16 lane_3_45)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_46 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_46))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_3_48 :: iN). (mk_lane__2 Jnn_I16 lane_3_48)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_12 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_394 :: lane_underscore). ((proj_lane__2 lane_1_394) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_276 :: lane_underscore). ((proj_lane__2 lane_2_276) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_394 :: lane_underscore) (lane_2_276 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_394))) (the ((proj_lane__2 lane_2_276))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_392 :: lane_underscore). ((proj_lane__2 lane_1_392) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_274 :: lane_underscore). ((proj_lane__2 lane_2_274) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_392 :: lane_underscore) (lane_2_274 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_392))) (the ((proj_lane__2 lane_2_274))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_391 :: lane_underscore). ((proj_lane__2 lane_1_391) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_273 :: lane_underscore). ((proj_lane__2 lane_2_273) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_391 :: lane_underscore) (lane_2_273 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_391))) (the ((proj_lane__2 lane_2_273))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_245 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_245)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_246 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_246)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I32)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_3_49 :: iN). (mk_lane__2 Jnn_I32 lane_3_49)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_50 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_50))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_3_52 :: iN). (mk_lane__2 Jnn_I32 lane_3_52)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_13 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_398 :: lane_underscore). ((proj_lane__2 lane_1_398) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_280 :: lane_underscore). ((proj_lane__2 lane_2_280) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_398 :: lane_underscore) (lane_2_280 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_398))) (the ((proj_lane__2 lane_2_280))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_396 :: lane_underscore). ((proj_lane__2 lane_1_396) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_278 :: lane_underscore). ((proj_lane__2 lane_2_278) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_396 :: lane_underscore) (lane_2_278 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_396))) (the ((proj_lane__2 lane_2_278))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_395 :: lane_underscore). ((proj_lane__2 lane_1_395) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_277 :: lane_underscore). ((proj_lane__2 lane_2_277) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_395 :: lane_underscore) (lane_2_277 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_395))) (the ((proj_lane__2 lane_2_277))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_247 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_247)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_248 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_248)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I64)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_3_53 :: iN). (mk_lane__2 Jnn_I64 lane_3_53)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_54 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_54))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_3_56 :: iN). (mk_lane__2 Jnn_I64 lane_3_56)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_14 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_402 :: lane_underscore). ((proj_lane__2 lane_1_402) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_284 :: lane_underscore). ((proj_lane__2 lane_2_284) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_402 :: lane_underscore) (lane_2_284 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_402))) (the ((proj_lane__2 lane_2_284))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_400 :: lane_underscore). ((proj_lane__2 lane_1_400) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_282 :: lane_underscore). ((proj_lane__2 lane_2_282) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_400 :: lane_underscore) (lane_2_282 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_400))) (the ((proj_lane__2 lane_2_282))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_399 :: lane_underscore). ((proj_lane__2 lane_1_399) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_281 :: lane_underscore). ((proj_lane__2 lane_2_281) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_399 :: lane_underscore) (lane_2_281 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_399))) (the ((proj_lane__2 lane_2_281))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_249 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_249)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_250 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_250)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I8)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_3_57 :: iN). (mk_lane__2 Jnn_I8 lane_3_57)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_58 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_58))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_3_60 :: iN). (mk_lane__2 Jnn_I8 lane_3_60)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_15 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_406 :: lane_underscore). ((proj_lane__2 lane_1_406) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_288 :: lane_underscore). ((proj_lane__2 lane_2_288) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_406 :: lane_underscore) (lane_2_288 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_406))) (the ((proj_lane__2 lane_2_288))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_404 :: lane_underscore). ((proj_lane__2 lane_1_404) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_286 :: lane_underscore). ((proj_lane__2 lane_2_286) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_404 :: lane_underscore) (lane_2_286 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_404))) (the ((proj_lane__2 lane_2_286))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_403 :: lane_underscore). ((proj_lane__2 lane_1_403) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_285 :: lane_underscore). ((proj_lane__2 lane_2_285) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_403 :: lane_underscore) (lane_2_285 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_403))) (the ((proj_lane__2 lane_2_285))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_251 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_251)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_252 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_252)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I16)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_3_61 :: iN). (mk_lane__2 Jnn_I16 lane_3_61)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_62 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_62))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_3_64 :: iN). (mk_lane__2 Jnn_I16 lane_3_64)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_16 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_410 :: lane_underscore). ((proj_lane__2 lane_1_410) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_292 :: lane_underscore). ((proj_lane__2 lane_2_292) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_410 :: lane_underscore) (lane_2_292 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_410))) (the ((proj_lane__2 lane_2_292))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_408 :: lane_underscore). ((proj_lane__2 lane_1_408) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_290 :: lane_underscore). ((proj_lane__2 lane_2_290) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_408 :: lane_underscore) (lane_2_290 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_408))) (the ((proj_lane__2 lane_2_290))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_407 :: lane_underscore). ((proj_lane__2 lane_1_407) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_289 :: lane_underscore). ((proj_lane__2 lane_2_289) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_407 :: lane_underscore) (lane_2_289 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_407))) (the ((proj_lane__2 lane_2_289))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_253 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_253)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_254 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_254)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I32)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_3_65 :: iN). (mk_lane__2 Jnn_I32 lane_3_65)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_66 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_66))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_3_68 :: iN). (mk_lane__2 Jnn_I32 lane_3_68)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_17 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_414 :: lane_underscore). ((proj_lane__2 lane_1_414) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_296 :: lane_underscore). ((proj_lane__2 lane_2_296) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_414 :: lane_underscore) (lane_2_296 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_414))) (the ((proj_lane__2 lane_2_296))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_412 :: lane_underscore). ((proj_lane__2 lane_1_412) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_294 :: lane_underscore). ((proj_lane__2 lane_2_294) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_412 :: lane_underscore) (lane_2_294 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_412))) (the ((proj_lane__2 lane_2_294))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_411 :: lane_underscore). ((proj_lane__2 lane_1_411) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_293 :: lane_underscore). ((proj_lane__2 lane_2_293) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_411 :: lane_underscore) (lane_2_293 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_411))) (the ((proj_lane__2 lane_2_293))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_255 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_255)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_256 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_256)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I64)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_3_69 :: iN). (mk_lane__2 Jnn_I64 lane_3_69)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_70 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_70))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_3_72 :: iN). (mk_lane__2 Jnn_I64 lane_3_72)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_18 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_418 :: lane_underscore). ((proj_lane__2 lane_1_418) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_300 :: lane_underscore). ((proj_lane__2 lane_2_300) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_418 :: lane_underscore) (lane_2_300 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_418))) (the ((proj_lane__2 lane_2_300))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_416 :: lane_underscore). ((proj_lane__2 lane_1_416) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_298 :: lane_underscore). ((proj_lane__2 lane_2_298) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_416 :: lane_underscore) (lane_2_298 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_416))) (the ((proj_lane__2 lane_2_298))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_415 :: lane_underscore). ((proj_lane__2 lane_1_415) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_297 :: lane_underscore). ((proj_lane__2 lane_2_297) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_415 :: lane_underscore) (lane_2_297 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_415))) (the ((proj_lane__2 lane_2_297))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_257 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_257)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_258 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_258)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I8)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_3_73 :: iN). (mk_lane__2 Jnn_I8 lane_3_73)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_74 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_74))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_3_76 :: iN). (mk_lane__2 Jnn_I8 lane_3_76)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_19 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_422 :: lane_underscore). ((proj_lane__2 lane_1_422) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_304 :: lane_underscore). ((proj_lane__2 lane_2_304) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_422 :: lane_underscore) (lane_2_304 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_422))) (the ((proj_lane__2 lane_2_304))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_420 :: lane_underscore). ((proj_lane__2 lane_1_420) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_302 :: lane_underscore). ((proj_lane__2 lane_2_302) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_420 :: lane_underscore) (lane_2_302 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_420))) (the ((proj_lane__2 lane_2_302))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_419 :: lane_underscore). ((proj_lane__2 lane_1_419) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_301 :: lane_underscore). ((proj_lane__2 lane_2_301) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_419 :: lane_underscore) (lane_2_301 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_419))) (the ((proj_lane__2 lane_2_301))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_259 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_259)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_260 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_260)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I16)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_3_77 :: iN). (mk_lane__2 Jnn_I16 lane_3_77)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_78 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_78))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_3_80 :: iN). (mk_lane__2 Jnn_I16 lane_3_80)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_20 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_426 :: lane_underscore). ((proj_lane__2 lane_1_426) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_308 :: lane_underscore). ((proj_lane__2 lane_2_308) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_426 :: lane_underscore) (lane_2_308 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_426))) (the ((proj_lane__2 lane_2_308))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_424 :: lane_underscore). ((proj_lane__2 lane_1_424) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_306 :: lane_underscore). ((proj_lane__2 lane_2_306) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_424 :: lane_underscore) (lane_2_306 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_424))) (the ((proj_lane__2 lane_2_306))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_423 :: lane_underscore). ((proj_lane__2 lane_1_423) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_305 :: lane_underscore). ((proj_lane__2 lane_2_305) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_423 :: lane_underscore) (lane_2_305 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_423))) (the ((proj_lane__2 lane_2_305))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_261 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_261)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_262 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) iter_262)) (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I32)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_3_81 :: iN). (mk_lane__2 Jnn_I32 lane_3_81)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_82 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_82))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (λ (lane_3_84 :: iN). (mk_lane__2 Jnn_I32 lane_3_84)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_21 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_430 :: lane_underscore). ((proj_lane__2 lane_1_430) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_312 :: lane_underscore). ((proj_lane__2 lane_2_312) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_430 :: lane_underscore) (lane_2_312 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_430))) (the ((proj_lane__2 lane_2_312))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_428 :: lane_underscore). ((proj_lane__2 lane_1_428) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_310 :: lane_underscore). ((proj_lane__2 lane_2_310) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_428 :: lane_underscore) (lane_2_310 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_428))) (the ((proj_lane__2 lane_2_310))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_427 :: lane_underscore). ((proj_lane__2 lane_1_427) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_309 :: lane_underscore). ((proj_lane__2 lane_2_309) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_427 :: lane_underscore) (lane_2_309 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_427))) (the ((proj_lane__2 lane_2_309))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_263 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_263)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_264 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) iter_264)) (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I64)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_3_85 :: iN). (mk_lane__2 Jnn_I64 lane_3_85)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_86 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_86))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (λ (lane_3_88 :: iN). (mk_lane__2 Jnn_I64 lane_3_88)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_22 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_434 :: lane_underscore). ((proj_lane__2 lane_1_434) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_316 :: lane_underscore). ((proj_lane__2 lane_2_316) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_434 :: lane_underscore) (lane_2_316 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_434))) (the ((proj_lane__2 lane_2_316))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_432 :: lane_underscore). ((proj_lane__2 lane_1_432) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_314 :: lane_underscore). ((proj_lane__2 lane_2_314) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_432 :: lane_underscore) (lane_2_314 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_432))) (the ((proj_lane__2 lane_2_314))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_431 :: lane_underscore). ((proj_lane__2 lane_1_431) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_313 :: lane_underscore). ((proj_lane__2 lane_2_313) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_431 :: lane_underscore) (lane_2_313 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_431))) (the ((proj_lane__2 lane_2_313))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_265 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_265)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_266 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) iter_266)) (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I8)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_3_89 :: iN). (mk_lane__2 Jnn_I8 lane_3_89)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_90 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_90))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (λ (lane_3_92 :: iN). (mk_lane__2 Jnn_I8 lane_3_92)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_23 :
		"((length var_2_lst) = (length lane_1_lst)) ⟹
		 ((length var_2_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_438 :: lane_underscore). ((proj_lane__2 lane_1_438) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_320 :: lane_underscore). ((proj_lane__2 lane_2_320) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_2 :: uN) (lane_1_438 :: lane_underscore) (lane_2_320 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_438))) (the ((proj_lane__2 lane_2_320))) var_2)) var_2_lst lane_1_lst lane_2_lst ⟹
		 ((length var_1_lst) = (length lane_1_lst)) ⟹
		 ((length var_1_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_436 :: lane_underscore). ((proj_lane__2 lane_1_436) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_318 :: lane_underscore). ((proj_lane__2 lane_2_318) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_1 :: uN) (lane_1_436 :: lane_underscore) (lane_2_318 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_436))) (the ((proj_lane__2 lane_2_318))) var_1)) var_1_lst lane_1_lst lane_2_lst ⟹
		 ((length var_0_lst) = (length lane_1_lst)) ⟹
		 ((length var_0_lst) = (length lane_2_lst)) ⟹
		 list_all (λ (lane_1_435 :: lane_underscore). ((proj_lane__2 lane_1_435) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_317 :: lane_underscore). ((proj_lane__2 lane_2_317) ≠ None)) lane_2_lst ⟹
		 list_all3 (λ (var_0 :: uN) (lane_1_435 :: lane_underscore) (lane_2_317 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_435))) (the ((proj_lane__2 lane_2_317))) var_0)) var_0_lst lane_1_lst lane_2_lst ⟹
		 list_all (λ (iter_267 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_267)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_268 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) iter_268)) (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2) ⟹
		 list_all (λ (var_0 :: uN). (wf_uN (lsize (lanetype_Jnn Jnn_I16)) (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0))))) var_0_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_3_93 :: iN). (mk_lane__2 Jnn_I16 lane_3_93)) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) ⟹
		 list_all (λ (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst ⟹
		 list_all (λ (lane_3_94 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_94))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) ⟹
		 (lane_3_lst = (map (λ (var_2 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_2)))) var_2_lst)) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (λ (lane_3_96 :: iN). (mk_lane__2 Jnn_I16 lane_3_96)) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_24 :
		"list_all (λ (iter_269 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_269)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_270 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_270)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 ((size (valtype_Fnn Fnn_F32)) ≠ None) ⟹
		 list_all (λ (lane_1_439 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_439)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_439 :: lane_underscore). ((proj_lane__0 lane_1_439) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_321 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_321)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_321 :: lane_underscore). ((proj_lane__0 lane_2_321) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_439 :: lane_underscore) (lane_2_321 :: lane_underscore). (wf_uN (the ((size (valtype_Fnn Fnn_F32)))) (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (feq_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_439)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_321)))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_97 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_97))))) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_440 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_440)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_440 :: lane_underscore). ((proj_lane__0 lane_1_440) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_322 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_322)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_322 :: lane_underscore). ((proj_lane__0 lane_2_322) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_440 :: lane_underscore) (lane_2_322 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (feq_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_440)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_322))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ⟹
		 list_all (λ (lane_3_98 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_98)))))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_442 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_442)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_442 :: lane_underscore). ((proj_lane__0 lane_1_442) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_324 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_324)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_324 :: lane_underscore). ((proj_lane__0 lane_2_324) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_442 :: lane_underscore) (lane_2_324 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (feq_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_442)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_324))))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F32))))) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_100 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_100))))) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_EQ) v128_1 v128_2 v128"
	| fun_vrelop__case_25 :
		"list_all (λ (iter_271 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_271)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_272 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_272)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 ((size (valtype_Fnn Fnn_F64)) ≠ None) ⟹
		 list_all (λ (lane_1_443 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_443)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_443 :: lane_underscore). ((proj_lane__0 lane_1_443) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_325 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_325)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_325 :: lane_underscore). ((proj_lane__0 lane_2_325) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_443 :: lane_underscore) (lane_2_325 :: lane_underscore). (wf_uN (the ((size (valtype_Fnn Fnn_F64)))) (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (feq_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_443)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_325)))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_101 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_101))))) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_444 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_444)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_444 :: lane_underscore). ((proj_lane__0 lane_1_444) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_326 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_326)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_326 :: lane_underscore). ((proj_lane__0 lane_2_326) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_444 :: lane_underscore) (lane_2_326 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (feq_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_444)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_326))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ⟹
		 list_all (λ (lane_3_102 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_102)))))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_446 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_446)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_446 :: lane_underscore). ((proj_lane__0 lane_1_446) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_328 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_328)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_328 :: lane_underscore). ((proj_lane__0 lane_2_328) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_446 :: lane_underscore) (lane_2_328 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (feq_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_446)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_328))))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F64))))) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_104 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_104))))) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_EQ) v128_1 v128_2 v128"
	| fun_vrelop__case_26 :
		"list_all (λ (iter_273 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_273)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_274 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_274)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 ((size (valtype_Fnn Fnn_F32)) ≠ None) ⟹
		 list_all (λ (lane_1_447 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_447)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_447 :: lane_underscore). ((proj_lane__0 lane_1_447) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_329 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_329)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_329 :: lane_underscore). ((proj_lane__0 lane_2_329) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_447 :: lane_underscore) (lane_2_329 :: lane_underscore). (wf_uN (the ((size (valtype_Fnn Fnn_F32)))) (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fne_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_447)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_329)))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_105 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_105))))) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_448 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_448)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_448 :: lane_underscore). ((proj_lane__0 lane_1_448) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_330 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_330)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_330 :: lane_underscore). ((proj_lane__0 lane_2_330) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_448 :: lane_underscore) (lane_2_330 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fne_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_448)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_330))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ⟹
		 list_all (λ (lane_3_106 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_106)))))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_450 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_450)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_450 :: lane_underscore). ((proj_lane__0 lane_1_450) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_332 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_332)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_332 :: lane_underscore). ((proj_lane__0 lane_2_332) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_450 :: lane_underscore) (lane_2_332 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fne_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_450)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_332))))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F32))))) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_108 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_108))))) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_NE) v128_1 v128_2 v128"
	| fun_vrelop__case_27 :
		"list_all (λ (iter_275 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_275)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_276 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_276)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 ((size (valtype_Fnn Fnn_F64)) ≠ None) ⟹
		 list_all (λ (lane_1_451 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_451)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_451 :: lane_underscore). ((proj_lane__0 lane_1_451) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_333 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_333)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_333 :: lane_underscore). ((proj_lane__0 lane_2_333) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_451 :: lane_underscore) (lane_2_333 :: lane_underscore). (wf_uN (the ((size (valtype_Fnn Fnn_F64)))) (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fne_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_451)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_333)))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_109 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_109))))) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_452 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_452)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_452 :: lane_underscore). ((proj_lane__0 lane_1_452) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_334 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_334)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_334 :: lane_underscore). ((proj_lane__0 lane_2_334) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_452 :: lane_underscore) (lane_2_334 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fne_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_452)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_334))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ⟹
		 list_all (λ (lane_3_110 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_110)))))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_454 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_454)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_454 :: lane_underscore). ((proj_lane__0 lane_1_454) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_336 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_336)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_336 :: lane_underscore). ((proj_lane__0 lane_2_336) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_454 :: lane_underscore) (lane_2_336 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fne_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_454)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_336))))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F64))))) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_112 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_112))))) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_NE) v128_1 v128_2 v128"
	| fun_vrelop__case_28 :
		"list_all (λ (iter_277 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_277)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_278 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_278)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 ((size (valtype_Fnn Fnn_F32)) ≠ None) ⟹
		 list_all (λ (lane_1_455 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_455)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_455 :: lane_underscore). ((proj_lane__0 lane_1_455) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_337 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_337)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_337 :: lane_underscore). ((proj_lane__0 lane_2_337) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_455 :: lane_underscore) (lane_2_337 :: lane_underscore). (wf_uN (the ((size (valtype_Fnn Fnn_F32)))) (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (flt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_455)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_337)))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_113 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_113))))) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_456 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_456)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_456 :: lane_underscore). ((proj_lane__0 lane_1_456) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_338 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_338)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_338 :: lane_underscore). ((proj_lane__0 lane_2_338) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_456 :: lane_underscore) (lane_2_338 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (flt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_456)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_338))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ⟹
		 list_all (λ (lane_3_114 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_114)))))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_458 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_458)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_458 :: lane_underscore). ((proj_lane__0 lane_1_458) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_340 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_340)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_340 :: lane_underscore). ((proj_lane__0 lane_2_340) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_458 :: lane_underscore) (lane_2_340 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (flt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_458)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_340))))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F32))))) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_116 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_116))))) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_LT) v128_1 v128_2 v128"
	| fun_vrelop__case_29 :
		"list_all (λ (iter_279 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_279)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_280 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_280)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 ((size (valtype_Fnn Fnn_F64)) ≠ None) ⟹
		 list_all (λ (lane_1_459 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_459)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_459 :: lane_underscore). ((proj_lane__0 lane_1_459) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_341 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_341)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_341 :: lane_underscore). ((proj_lane__0 lane_2_341) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_459 :: lane_underscore) (lane_2_341 :: lane_underscore). (wf_uN (the ((size (valtype_Fnn Fnn_F64)))) (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (flt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_459)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_341)))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_117 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_117))))) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_460 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_460)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_460 :: lane_underscore). ((proj_lane__0 lane_1_460) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_342 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_342)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_342 :: lane_underscore). ((proj_lane__0 lane_2_342) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_460 :: lane_underscore) (lane_2_342 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (flt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_460)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_342))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ⟹
		 list_all (λ (lane_3_118 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_118)))))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_462 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_462)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_462 :: lane_underscore). ((proj_lane__0 lane_1_462) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_344 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_344)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_344 :: lane_underscore). ((proj_lane__0 lane_2_344) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_462 :: lane_underscore) (lane_2_344 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (flt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_462)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_344))))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F64))))) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_120 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_120))))) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_LT) v128_1 v128_2 v128"
	| fun_vrelop__case_30 :
		"list_all (λ (iter_281 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_281)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_282 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_282)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 ((size (valtype_Fnn Fnn_F32)) ≠ None) ⟹
		 list_all (λ (lane_1_463 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_463)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_463 :: lane_underscore). ((proj_lane__0 lane_1_463) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_345 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_345)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_345 :: lane_underscore). ((proj_lane__0 lane_2_345) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_463 :: lane_underscore) (lane_2_345 :: lane_underscore). (wf_uN (the ((size (valtype_Fnn Fnn_F32)))) (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fgt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_463)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_345)))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_121 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_121))))) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_464 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_464)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_464 :: lane_underscore). ((proj_lane__0 lane_1_464) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_346 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_346)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_346 :: lane_underscore). ((proj_lane__0 lane_2_346) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_464 :: lane_underscore) (lane_2_346 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fgt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_464)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_346))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ⟹
		 list_all (λ (lane_3_122 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_122)))))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_466 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_466)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_466 :: lane_underscore). ((proj_lane__0 lane_1_466) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_348 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_348)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_348 :: lane_underscore). ((proj_lane__0 lane_2_348) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_466 :: lane_underscore) (lane_2_348 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fgt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_466)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_348))))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F32))))) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_124 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_124))))) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_GT) v128_1 v128_2 v128"
	| fun_vrelop__case_31 :
		"list_all (λ (iter_283 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_283)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_284 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_284)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 ((size (valtype_Fnn Fnn_F64)) ≠ None) ⟹
		 list_all (λ (lane_1_467 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_467)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_467 :: lane_underscore). ((proj_lane__0 lane_1_467) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_349 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_349)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_349 :: lane_underscore). ((proj_lane__0 lane_2_349) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_467 :: lane_underscore) (lane_2_349 :: lane_underscore). (wf_uN (the ((size (valtype_Fnn Fnn_F64)))) (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fgt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_467)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_349)))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_125 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_125))))) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_468 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_468)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_468 :: lane_underscore). ((proj_lane__0 lane_1_468) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_350 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_350)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_350 :: lane_underscore). ((proj_lane__0 lane_2_350) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_468 :: lane_underscore) (lane_2_350 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fgt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_468)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_350))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ⟹
		 list_all (λ (lane_3_126 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_126)))))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_470 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_470)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_470 :: lane_underscore). ((proj_lane__0 lane_1_470) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_352 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_352)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_352 :: lane_underscore). ((proj_lane__0 lane_2_352) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_470 :: lane_underscore) (lane_2_352 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fgt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_470)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_352))))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F64))))) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_128 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_128))))) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_GT) v128_1 v128_2 v128"
	| fun_vrelop__case_32 :
		"list_all (λ (iter_285 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_285)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_286 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_286)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 ((size (valtype_Fnn Fnn_F32)) ≠ None) ⟹
		 list_all (λ (lane_1_471 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_471)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_471 :: lane_underscore). ((proj_lane__0 lane_1_471) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_353 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_353)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_353 :: lane_underscore). ((proj_lane__0 lane_2_353) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_471 :: lane_underscore) (lane_2_353 :: lane_underscore). (wf_uN (the ((size (valtype_Fnn Fnn_F32)))) (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fle_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_471)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_353)))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_129 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_129))))) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_472 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_472)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_472 :: lane_underscore). ((proj_lane__0 lane_1_472) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_354 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_354)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_354 :: lane_underscore). ((proj_lane__0 lane_2_354) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_472 :: lane_underscore) (lane_2_354 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fle_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_472)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_354))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ⟹
		 list_all (λ (lane_3_130 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_130)))))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_474 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_474)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_474 :: lane_underscore). ((proj_lane__0 lane_1_474) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_356 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_356)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_356 :: lane_underscore). ((proj_lane__0 lane_2_356) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_474 :: lane_underscore) (lane_2_356 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fle_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_474)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_356))))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F32))))) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_132 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_132))))) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_LE) v128_1 v128_2 v128"
	| fun_vrelop__case_33 :
		"list_all (λ (iter_287 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_287)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_288 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_288)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 ((size (valtype_Fnn Fnn_F64)) ≠ None) ⟹
		 list_all (λ (lane_1_475 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_475)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_475 :: lane_underscore). ((proj_lane__0 lane_1_475) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_357 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_357)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_357 :: lane_underscore). ((proj_lane__0 lane_2_357) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_475 :: lane_underscore) (lane_2_357 :: lane_underscore). (wf_uN (the ((size (valtype_Fnn Fnn_F64)))) (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fle_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_475)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_357)))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_133 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_133))))) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_476 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_476)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_476 :: lane_underscore). ((proj_lane__0 lane_1_476) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_358 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_358)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_358 :: lane_underscore). ((proj_lane__0 lane_2_358) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_476 :: lane_underscore) (lane_2_358 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fle_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_476)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_358))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ⟹
		 list_all (λ (lane_3_134 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_134)))))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_478 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_478)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_478 :: lane_underscore). ((proj_lane__0 lane_1_478) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_360 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_360)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_360 :: lane_underscore). ((proj_lane__0 lane_2_360) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_478 :: lane_underscore) (lane_2_360 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fle_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_478)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_360))))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F64))))) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_136 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_136))))) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_LE) v128_1 v128_2 v128"
	| fun_vrelop__case_34 :
		"list_all (λ (iter_289 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_289)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_290 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) iter_290)) (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 ((size (valtype_Fnn Fnn_F32)) ≠ None) ⟹
		 list_all (λ (lane_1_479 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_479)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_479 :: lane_underscore). ((proj_lane__0 lane_1_479) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_361 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_361)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_361 :: lane_underscore). ((proj_lane__0 lane_2_361) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_479 :: lane_underscore) (lane_2_361 :: lane_underscore). (wf_uN (the ((size (valtype_Fnn Fnn_F32)))) (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fge_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_479)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_361)))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_137 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_137))))) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_480 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_480)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_480 :: lane_underscore). ((proj_lane__0 lane_1_480) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_362 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_362)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_362 :: lane_underscore). ((proj_lane__0 lane_2_362) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_480 :: lane_underscore) (lane_2_362 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fge_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_480)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_362))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ⟹
		 list_all (λ (lane_3_138 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_138)))))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_482 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_482)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_482 :: lane_underscore). ((proj_lane__0 lane_1_482) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_364 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_364)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_364 :: lane_underscore). ((proj_lane__0 lane_2_364) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_482 :: lane_underscore) (lane_2_364 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fge_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_482)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_364))))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F32))))) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_140 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_140))))) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_GE) v128_1 v128_2 v128"
	| fun_vrelop__case_35 :
		"list_all (λ (iter_291 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_291)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1) ⟹
		 list_all (λ (iter_292 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) iter_292)) (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2) ⟹
		 ((length lane_1_lst) = (length lane_2_lst)) ⟹
		 ((size (valtype_Fnn Fnn_F64)) ≠ None) ⟹
		 list_all (λ (lane_1_483 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_483)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_483 :: lane_underscore). ((proj_lane__0 lane_1_483) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_365 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_365)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_365 :: lane_underscore). ((proj_lane__0 lane_2_365) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_483 :: lane_underscore) (lane_2_365 :: lane_underscore). (wf_uN (the ((size (valtype_Fnn Fnn_F64)))) (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fge_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_483)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_365)))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_141 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_141))))) lane_3_lst))) ⟹
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) ⟹
		 list_all (λ (lane_1_484 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_484)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_484 :: lane_underscore). ((proj_lane__0 lane_1_484) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_366 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_366)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_366 :: lane_underscore). ((proj_lane__0 lane_2_366) ≠ None)) lane_2_lst ⟹
		 list_all2 (λ (lane_1_484 :: lane_underscore) (lane_2_366 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fge_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_484)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_366))))))))))) lane_1_lst lane_2_lst ⟹
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) ⟹
		 list_all (λ (lane_3_142 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_142)))))) lane_3_lst ⟹
		 (lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) ⟹
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) ⟹
		 list_all (λ (lane_1_486 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_486)))) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_1_486 :: lane_underscore). ((proj_lane__0 lane_1_486) ≠ None)) lane_1_lst ⟹
		 list_all (λ (lane_2_368 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_368)))) ≠ None)) lane_2_lst ⟹
		 list_all (λ (lane_2_368 :: lane_underscore). ((proj_lane__0 lane_2_368) ≠ None)) lane_2_lst ⟹
		 (lane_3_lst = (list_zipWith (λ (lane_1_486 :: lane_underscore) (lane_2_368 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fge_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_486)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_368))))))))))) lane_1_lst lane_2_lst)) ⟹
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F64))))) ⟹
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (λ (lane_3_144 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_144))))) lane_3_lst))) ⟹
		 (v_M = M_0) ⟹
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_GE) v128_1 v128_2 v128"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.6-383.15 *)
inductive fun_vcvtop__underscore :: "shape ⇒ shape ⇒ vcvtop ⇒ lane_underscore ⇒ (lane_underscore list) ⇒ bool" where
	  fun_vcvtop___case_0 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I32)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I32 iN_1) [(mk_lane__2 Jnn_I32 iN_2)]"
	| fun_vcvtop___case_1 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I32)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I64 iN_1) [(mk_lane__2 Jnn_I32 iN_2)]"
	| fun_vcvtop___case_2 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I32)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I8 iN_1) [(mk_lane__2 Jnn_I32 iN_2)]"
	| fun_vcvtop___case_3 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I32)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I16 iN_1) [(mk_lane__2 Jnn_I32 iN_2)]"
	| fun_vcvtop___case_4 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I64)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I32 iN_1) [(mk_lane__2 Jnn_I64 iN_2)]"
	| fun_vcvtop___case_5 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I64)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I64 iN_1) [(mk_lane__2 Jnn_I64 iN_2)]"
	| fun_vcvtop___case_6 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I64)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I8 iN_1) [(mk_lane__2 Jnn_I64 iN_2)]"
	| fun_vcvtop___case_7 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I64)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I16 iN_1) [(mk_lane__2 Jnn_I64 iN_2)]"
	| fun_vcvtop___case_8 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I8)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I32 iN_1) [(mk_lane__2 Jnn_I8 iN_2)]"
	| fun_vcvtop___case_9 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I8)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I64 iN_1) [(mk_lane__2 Jnn_I8 iN_2)]"
	| fun_vcvtop___case_10 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I8)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I8 iN_1) [(mk_lane__2 Jnn_I8 iN_2)]"
	| fun_vcvtop___case_11 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I8)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_I8 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I16 iN_1) [(mk_lane__2 Jnn_I8 iN_2)]"
	| fun_vcvtop___case_12 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I16)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I32 iN_1) [(mk_lane__2 Jnn_I16 iN_2)]"
	| fun_vcvtop___case_13 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I16)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I64 iN_1) [(mk_lane__2 Jnn_I16 iN_2)]"
	| fun_vcvtop___case_14 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I16)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I8 iN_1) [(mk_lane__2 Jnn_I16 iN_2)]"
	| fun_vcvtop___case_15 :
		"(wf_uN (lsize (lanetype_Jnn Jnn_I16)) (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1)) ⟹
		 (iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_I16 (mk_dim M_2)) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I16 iN_1) [(mk_lane__2 Jnn_I16 iN_2)]"
	| fun_vcvtop___case_16 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1)) ⟹
		 (fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I32 iN_1) [(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))]"
	| fun_vcvtop___case_17 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1)) ⟹
		 (fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I64 iN_1) [(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))]"
	| fun_vcvtop___case_18 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1)) ⟹
		 (fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I8 iN_1) [(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))]"
	| fun_vcvtop___case_19 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1)) ⟹
		 (fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I16 iN_1) [(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))]"
	| fun_vcvtop___case_20 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1)) ⟹
		 (fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I32 iN_1) [(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))]"
	| fun_vcvtop___case_21 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1)) ⟹
		 (fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I64 iN_1) [(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))]"
	| fun_vcvtop___case_22 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1)) ⟹
		 (fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I8 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I8 iN_1) [(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))]"
	| fun_vcvtop___case_23 :
		"(wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1)) ⟹
		 (fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_I16 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I16 iN_1) [(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))]"
	| fun_vcvtop___case_24 :
		"((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 list_all (λ (iter_293 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I32)))) iter_293)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1)) ⟹
		 (iN_2_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (list_underscore  (map_option (λ (iN_2_2 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_2))) iN_2_opt))"
	| fun_vcvtop___case_25 :
		"((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 list_all (λ (iter_294 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I32)))) iter_294)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1)) ⟹
		 (iN_2_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (list_underscore  (map_option (λ (iN_2_4 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_4))) iN_2_opt))"
	| fun_vcvtop___case_26 :
		"((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 list_all (λ (iter_295 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I64)))) iter_295)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1)) ⟹
		 (iN_2_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (list_underscore  (map_option (λ (iN_2_6 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_6))) iN_2_opt))"
	| fun_vcvtop___case_27 :
		"((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 list_all (λ (iter_296 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I64)))) iter_296)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1)) ⟹
		 (iN_2_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (list_underscore  (map_option (λ (iN_2_8 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_8))) iN_2_opt))"
	| fun_vcvtop___case_28 :
		"((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 list_all (λ (iter_297 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I32)))) iter_297)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1)) ⟹
		 (iN_2_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (list_underscore  (map_option (λ (iN_2_10 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_10))) iN_2_opt))"
	| fun_vcvtop___case_29 :
		"((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 list_all (λ (iter_298 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I32)))) iter_298)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1)) ⟹
		 (iN_2_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I32 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (list_underscore  (map_option (λ (iN_2_12 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_12))) iN_2_opt))"
	| fun_vcvtop___case_30 :
		"((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 list_all (λ (iter_299 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I64)))) iter_299)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1)) ⟹
		 (iN_2_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (list_underscore  (map_option (λ (iN_2_14 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_14))) iN_2_opt))"
	| fun_vcvtop___case_31 :
		"((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 list_all (λ (iter_300 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I64)))) iter_300)) (option_to_list (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1)) ⟹
		 (iN_2_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_I64 (mk_dim M_2)) (vcvtop_TRUNC_SAT v_sx zero_opt) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (list_underscore  (map_option (λ (iN_2_16 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_16))) iN_2_opt))"
	| fun_vcvtop___case_32 :
		"list_all (λ (iter_301 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_301)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) ⟹
		 (fN_2_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (map (λ (fN_2_2 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_2))) fN_2_lst)"
	| fun_vcvtop___case_33 :
		"list_all (λ (iter_302 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_302)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) ⟹
		 (fN_2_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (map (λ (fN_2_4 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_4))) fN_2_lst)"
	| fun_vcvtop___case_34 :
		"list_all (λ (iter_303 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_303)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) ⟹
		 (fN_2_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (map (λ (fN_2_6 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_6))) fN_2_lst)"
	| fun_vcvtop___case_35 :
		"list_all (λ (iter_304 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_304)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) ⟹
		 (fN_2_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (map (λ (fN_2_8 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_8))) fN_2_lst)"
	| fun_vcvtop___case_36 :
		"list_all (λ (iter_305 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_305)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) ⟹
		 (fN_2_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (map (λ (fN_2_10 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_10))) fN_2_lst)"
	| fun_vcvtop___case_37 :
		"list_all (λ (iter_306 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_306)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) ⟹
		 (fN_2_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (map (λ (fN_2_12 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_12))) fN_2_lst)"
	| fun_vcvtop___case_38 :
		"list_all (λ (iter_307 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_307)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) ⟹
		 (fN_2_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (map (λ (fN_2_14 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_14))) fN_2_lst)"
	| fun_vcvtop___case_39 :
		"list_all (λ (iter_308 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_308)) (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) ⟹
		 (fN_2_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) (vcvtop_DEMOTE ZERO) (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (map (λ (fN_2_16 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_16))) fN_2_lst)"
	| fun_vcvtop___case_40 :
		"list_all (λ (iter_309 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_309)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) ⟹
		 (fN_2_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (map (λ (fN_2_18 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_18))) fN_2_lst)"
	| fun_vcvtop___case_41 :
		"list_all (λ (iter_310 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_310)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) ⟹
		 (fN_2_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (map (λ (fN_2_20 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_20))) fN_2_lst)"
	| fun_vcvtop___case_42 :
		"list_all (λ (iter_311 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_311)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) ⟹
		 (fN_2_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (map (λ (fN_2_22 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_22))) fN_2_lst)"
	| fun_vcvtop___case_43 :
		"list_all (λ (iter_312 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_312)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) ⟹
		 (fN_2_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F32 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) (map (λ (fN_2_24 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_24))) fN_2_lst)"
	| fun_vcvtop___case_44 :
		"list_all (λ (iter_313 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_313)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) ⟹
		 (fN_2_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (map (λ (fN_2_26 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_26))) fN_2_lst)"
	| fun_vcvtop___case_45 :
		"list_all (λ (iter_314 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F32)) iter_314)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) ⟹
		 (fN_2_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F32 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (map (λ (fN_2_28 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_28))) fN_2_lst)"
	| fun_vcvtop___case_46 :
		"list_all (λ (iter_315 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_315)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) ⟹
		 (fN_2_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (map (λ (fN_2_30 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_30))) fN_2_lst)"
	| fun_vcvtop___case_47 :
		"list_all (λ (iter_316 :: fN). (wf_fN (lsizenn2 (lanetype_Fnn Fnn_F64)) iter_316)) (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) ⟹
		 (fN_2_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1)) ⟹
		 fun_vcvtop__underscore (X lanetype_F64 (mk_dim M_1)) (X lanetype_F64 (mk_dim M_2)) PROMOTELOW (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) (map (λ (fN_2_32 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_32))) fN_2_lst)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:583.6-583.17 *)
inductive fun_vextunop__underscore :: "ishape ⇒ ishape ⇒ vextunop_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ bool" where
	  fun_vextunop___case_0 :
		"list_all (λ (ci_1 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_1)) ci_lst ⟹
		 list_all (λ (iter_317 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_317)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) ⟹
		 ((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 list_all (λ (iter_318 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I32)))) iter_318)) (concat_underscore  (list_zipWith (λ (cj_1_1 :: iN) (cj_2_1 :: iN). [cj_1_1, cj_2_1]) cj_1_lst cj_2_lst)) ⟹
		 list_all (λ (ci_2 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_2 :: lane_underscore). ((proj_lane__0 ci_2) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_2 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2))))))))) ci_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_2 :: iN) (cj_2_2 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_2 cj_2_2)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_3 :: iN) (cj_2_3 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_3 cj_2_3))))) cj_1_lst cj_2_lst ⟹
		 (ci_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ⟹
		 list_all (λ (ci_4 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_4)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_4 :: lane_underscore). ((proj_lane__0 ci_4) ≠ None)) ci_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_4 :: iN) (cj_2_4 :: iN). [cj_1_4, cj_2_4]) cj_1_lst cj_2_lst)) = (map (λ (ci_4 :: lane_underscore). (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_4)))))))) ci_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_5 :: iN) (cj_2_5 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_5 cj_2_5)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextunop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextunop__0 Jnn_I32 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c"
	| fun_vextunop___case_1 :
		"list_all (λ (ci_5 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_5)) ci_lst ⟹
		 list_all (λ (iter_319 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_319)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) ⟹
		 ((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 list_all (λ (iter_320 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I32)))) iter_320)) (concat_underscore  (list_zipWith (λ (cj_1_6 :: iN) (cj_2_6 :: iN). [cj_1_6, cj_2_6]) cj_1_lst cj_2_lst)) ⟹
		 list_all (λ (ci_6 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_6)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_6 :: lane_underscore). ((proj_lane__0 ci_6) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_6 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_6))))))))) ci_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_7 :: iN) (cj_2_7 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_7 cj_2_7)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_8 :: iN) (cj_2_8 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_8 cj_2_8))))) cj_1_lst cj_2_lst ⟹
		 (ci_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ⟹
		 list_all (λ (ci_8 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_8)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_8 :: lane_underscore). ((proj_lane__0 ci_8) ≠ None)) ci_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_9 :: iN) (cj_2_9 :: iN). [cj_1_9, cj_2_9]) cj_1_lst cj_2_lst)) = (map (λ (ci_8 :: lane_underscore). (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_8)))))))) ci_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_10 :: iN) (cj_2_10 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_10 cj_2_10)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextunop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextunop__0 Jnn_I32 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c"
	| fun_vextunop___case_2 :
		"list_all (λ (ci_9 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_9)) ci_lst ⟹
		 list_all (λ (iter_321 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_321)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) ⟹
		 ((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 list_all (λ (iter_322 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I32)))) iter_322)) (concat_underscore  (list_zipWith (λ (cj_1_11 :: iN) (cj_2_11 :: iN). [cj_1_11, cj_2_11]) cj_1_lst cj_2_lst)) ⟹
		 list_all (λ (ci_10 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_10)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_10 :: lane_underscore). ((proj_lane__0 ci_10) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_10 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_10))))))))) ci_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_12 :: iN) (cj_2_12 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_12 cj_2_12)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_13 :: iN) (cj_2_13 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_13 cj_2_13))))) cj_1_lst cj_2_lst ⟹
		 (ci_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ⟹
		 list_all (λ (ci_12 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_12)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_12 :: lane_underscore). ((proj_lane__0 ci_12) ≠ None)) ci_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_14 :: iN) (cj_2_14 :: iN). [cj_1_14, cj_2_14]) cj_1_lst cj_2_lst)) = (map (λ (ci_12 :: lane_underscore). (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_12)))))))) ci_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_15 :: iN) (cj_2_15 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_15 cj_2_15)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextunop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextunop__0 Jnn_I32 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c"
	| fun_vextunop___case_3 :
		"list_all (λ (ci_13 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_13)) ci_lst ⟹
		 list_all (λ (iter_323 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_323)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) ⟹
		 ((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 list_all (λ (iter_324 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I32)))) iter_324)) (concat_underscore  (list_zipWith (λ (cj_1_16 :: iN) (cj_2_16 :: iN). [cj_1_16, cj_2_16]) cj_1_lst cj_2_lst)) ⟹
		 list_all (λ (ci_14 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_14)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_14 :: lane_underscore). ((proj_lane__0 ci_14) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_14 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_14))))))))) ci_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_17 :: iN) (cj_2_17 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_17 cj_2_17)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_18 :: iN) (cj_2_18 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_18 cj_2_18))))) cj_1_lst cj_2_lst ⟹
		 (ci_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ⟹
		 list_all (λ (ci_16 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_16)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_16 :: lane_underscore). ((proj_lane__0 ci_16) ≠ None)) ci_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_19 :: iN) (cj_2_19 :: iN). [cj_1_19, cj_2_19]) cj_1_lst cj_2_lst)) = (map (λ (ci_16 :: lane_underscore). (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_16)))))))) ci_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_20 :: iN) (cj_2_20 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_20 cj_2_20)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextunop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextunop__0 Jnn_I32 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c"
	| fun_vextunop___case_4 :
		"list_all (λ (ci_17 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_17)) ci_lst ⟹
		 list_all (λ (iter_325 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_325)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) ⟹
		 ((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 list_all (λ (iter_326 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I64)))) iter_326)) (concat_underscore  (list_zipWith (λ (cj_1_21 :: iN) (cj_2_21 :: iN). [cj_1_21, cj_2_21]) cj_1_lst cj_2_lst)) ⟹
		 list_all (λ (ci_18 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_18)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_18 :: lane_underscore). ((proj_lane__0 ci_18) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_18 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_18))))))))) ci_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_22 :: iN) (cj_2_22 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_22 cj_2_22)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_23 :: iN) (cj_2_23 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_23 cj_2_23))))) cj_1_lst cj_2_lst ⟹
		 (ci_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ⟹
		 list_all (λ (ci_20 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_20)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_20 :: lane_underscore). ((proj_lane__0 ci_20) ≠ None)) ci_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_24 :: iN) (cj_2_24 :: iN). [cj_1_24, cj_2_24]) cj_1_lst cj_2_lst)) = (map (λ (ci_20 :: lane_underscore). (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_20)))))))) ci_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_25 :: iN) (cj_2_25 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_25 cj_2_25)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextunop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextunop__0 Jnn_I64 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c"
	| fun_vextunop___case_5 :
		"list_all (λ (ci_21 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_21)) ci_lst ⟹
		 list_all (λ (iter_327 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_327)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) ⟹
		 ((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 list_all (λ (iter_328 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I64)))) iter_328)) (concat_underscore  (list_zipWith (λ (cj_1_26 :: iN) (cj_2_26 :: iN). [cj_1_26, cj_2_26]) cj_1_lst cj_2_lst)) ⟹
		 list_all (λ (ci_22 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_22)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_22 :: lane_underscore). ((proj_lane__0 ci_22) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_22 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_22))))))))) ci_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_27 :: iN) (cj_2_27 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_27 cj_2_27)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_28 :: iN) (cj_2_28 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_28 cj_2_28))))) cj_1_lst cj_2_lst ⟹
		 (ci_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ⟹
		 list_all (λ (ci_24 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_24)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_24 :: lane_underscore). ((proj_lane__0 ci_24) ≠ None)) ci_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_29 :: iN) (cj_2_29 :: iN). [cj_1_29, cj_2_29]) cj_1_lst cj_2_lst)) = (map (λ (ci_24 :: lane_underscore). (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_24)))))))) ci_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_30 :: iN) (cj_2_30 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_30 cj_2_30)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextunop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextunop__0 Jnn_I64 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c"
	| fun_vextunop___case_6 :
		"list_all (λ (ci_25 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_25)) ci_lst ⟹
		 list_all (λ (iter_329 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_329)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) ⟹
		 ((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 list_all (λ (iter_330 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I64)))) iter_330)) (concat_underscore  (list_zipWith (λ (cj_1_31 :: iN) (cj_2_31 :: iN). [cj_1_31, cj_2_31]) cj_1_lst cj_2_lst)) ⟹
		 list_all (λ (ci_26 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_26)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_26 :: lane_underscore). ((proj_lane__0 ci_26) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_26 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_26))))))))) ci_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_32 :: iN) (cj_2_32 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_32 cj_2_32)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_33 :: iN) (cj_2_33 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_33 cj_2_33))))) cj_1_lst cj_2_lst ⟹
		 (ci_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ⟹
		 list_all (λ (ci_28 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_28)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_28 :: lane_underscore). ((proj_lane__0 ci_28) ≠ None)) ci_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_34 :: iN) (cj_2_34 :: iN). [cj_1_34, cj_2_34]) cj_1_lst cj_2_lst)) = (map (λ (ci_28 :: lane_underscore). (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_28)))))))) ci_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_35 :: iN) (cj_2_35 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_35 cj_2_35)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextunop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextunop__0 Jnn_I64 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c"
	| fun_vextunop___case_7 :
		"list_all (λ (ci_29 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_29)) ci_lst ⟹
		 list_all (λ (iter_331 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_331)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) ⟹
		 ((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 list_all (λ (iter_332 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I64)))) iter_332)) (concat_underscore  (list_zipWith (λ (cj_1_36 :: iN) (cj_2_36 :: iN). [cj_1_36, cj_2_36]) cj_1_lst cj_2_lst)) ⟹
		 list_all (λ (ci_30 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_30)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_30 :: lane_underscore). ((proj_lane__0 ci_30) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_30 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_30))))))))) ci_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_37 :: iN) (cj_2_37 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_37 cj_2_37)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_38 :: iN) (cj_2_38 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_38 cj_2_38))))) cj_1_lst cj_2_lst ⟹
		 (ci_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ⟹
		 list_all (λ (ci_32 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_32)))) ≠ None)) ci_lst ⟹
		 list_all (λ (ci_32 :: lane_underscore). ((proj_lane__0 ci_32) ≠ None)) ci_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_39 :: iN) (cj_2_39 :: iN). [cj_1_39, cj_2_39]) cj_1_lst cj_2_lst)) = (map (λ (ci_32 :: lane_underscore). (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_32)))))))) ci_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_40 :: iN) (cj_2_40 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_40 cj_2_40)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextunop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextunop__0 Jnn_I64 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:585.6-585.18 *)
inductive fun_vextbinop__underscore :: "ishape ⇒ ishape ⇒ vextbinop_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ vec_underscore ⇒ bool" where
	  fun_vextbinop___case_0 :
		"list_all (λ (iter_333 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_333)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_334 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_334)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) ⟹
		 list_all (λ (ci_1_1 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_1)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_1 :: lane_underscore). ((proj_lane__0 ci_1_1) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_1 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_1)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_1 :: lane_underscore). ((proj_lane__0 ci_2_1) ≠ None)) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (ci_1_1 :: lane_underscore) (ci_2_1 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_1))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_1))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_2 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_2)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_2 :: lane_underscore). ((proj_lane__0 ci_1_2) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_2 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_2)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_2 :: lane_underscore). ((proj_lane__0 ci_2_2) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_2 :: lane_underscore) (ci_2_2 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_2))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_2)))))))))))) ci_1_lst ci_2_lst ⟹
		 (ci_1_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ⟹
		 (ci_2_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ⟹
		 list_all (λ (ci_1_4 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_4)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_4 :: lane_underscore). ((proj_lane__0 ci_1_4) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_4 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_4)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_4 :: lane_underscore). ((proj_lane__0 ci_2_4) ≠ None)) ci_2_lst ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (ci_1_4 :: lane_underscore) (ci_2_4 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_4))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_4))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c"
	| fun_vextbinop___case_1 :
		"list_all (λ (iter_335 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_335)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_336 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_336)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) ⟹
		 list_all (λ (ci_1_5 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_5)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_5 :: lane_underscore). ((proj_lane__0 ci_1_5) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_5 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_5)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_5 :: lane_underscore). ((proj_lane__0 ci_2_5) ≠ None)) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (ci_1_5 :: lane_underscore) (ci_2_5 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_5))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_5))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_6 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_6)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_6 :: lane_underscore). ((proj_lane__0 ci_1_6) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_6 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_6)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_6 :: lane_underscore). ((proj_lane__0 ci_2_6) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_6 :: lane_underscore) (ci_2_6 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_6))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_6)))))))))))) ci_1_lst ci_2_lst ⟹
		 (ci_1_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ⟹
		 (ci_2_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ⟹
		 list_all (λ (ci_1_8 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_8)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_8 :: lane_underscore). ((proj_lane__0 ci_1_8) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_8 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_8)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_8 :: lane_underscore). ((proj_lane__0 ci_2_8) ≠ None)) ci_2_lst ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (ci_1_8 :: lane_underscore) (ci_2_8 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_8))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_8))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c"
	| fun_vextbinop___case_2 :
		"list_all (λ (iter_337 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_337)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_338 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_338)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) ⟹
		 list_all (λ (ci_1_9 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_9)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_9 :: lane_underscore). ((proj_lane__0 ci_1_9) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_9 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_9)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_9 :: lane_underscore). ((proj_lane__0 ci_2_9) ≠ None)) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (ci_1_9 :: lane_underscore) (ci_2_9 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_9))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_9))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_10 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_10)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_10 :: lane_underscore). ((proj_lane__0 ci_1_10) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_10 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_10)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_10 :: lane_underscore). ((proj_lane__0 ci_2_10) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_10 :: lane_underscore) (ci_2_10 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_10))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_10)))))))))))) ci_1_lst ci_2_lst ⟹
		 (ci_1_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ⟹
		 (ci_2_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ⟹
		 list_all (λ (ci_1_12 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_12)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_12 :: lane_underscore). ((proj_lane__0 ci_1_12) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_12 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_12)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_12 :: lane_underscore). ((proj_lane__0 ci_2_12) ≠ None)) ci_2_lst ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (ci_1_12 :: lane_underscore) (ci_2_12 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_12))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_12))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c"
	| fun_vextbinop___case_3 :
		"list_all (λ (iter_339 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_339)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_340 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_340)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) ⟹
		 list_all (λ (ci_1_13 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_13)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_13 :: lane_underscore). ((proj_lane__0 ci_1_13) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_13 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_13)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_13 :: lane_underscore). ((proj_lane__0 ci_2_13) ≠ None)) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (ci_1_13 :: lane_underscore) (ci_2_13 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_13))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_13))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_14 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_14)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_14 :: lane_underscore). ((proj_lane__0 ci_1_14) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_14 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_14)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_14 :: lane_underscore). ((proj_lane__0 ci_2_14) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_14 :: lane_underscore) (ci_2_14 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_14))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_14)))))))))))) ci_1_lst ci_2_lst ⟹
		 (ci_1_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ⟹
		 (ci_2_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ⟹
		 list_all (λ (ci_1_16 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_16)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_16 :: lane_underscore). ((proj_lane__0 ci_1_16) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_16 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_16)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_16 :: lane_underscore). ((proj_lane__0 ci_2_16) ≠ None)) ci_2_lst ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (ci_1_16 :: lane_underscore) (ci_2_16 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_16))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_16))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c"
	| fun_vextbinop___case_4 :
		"list_all (λ (iter_341 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_341)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_342 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_342)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) ⟹
		 list_all (λ (ci_1_17 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_17)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_17 :: lane_underscore). ((proj_lane__0 ci_1_17) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_17 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_17)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_17 :: lane_underscore). ((proj_lane__0 ci_2_17) ≠ None)) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (ci_1_17 :: lane_underscore) (ci_2_17 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_17))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_17))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_18 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_18)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_18 :: lane_underscore). ((proj_lane__0 ci_1_18) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_18 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_18)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_18 :: lane_underscore). ((proj_lane__0 ci_2_18) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_18 :: lane_underscore) (ci_2_18 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_18))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_18)))))))))))) ci_1_lst ci_2_lst ⟹
		 (ci_1_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ⟹
		 (ci_2_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ⟹
		 list_all (λ (ci_1_20 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_20)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_20 :: lane_underscore). ((proj_lane__0 ci_1_20) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_20 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_20)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_20 :: lane_underscore). ((proj_lane__0 ci_2_20) ≠ None)) ci_2_lst ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (ci_1_20 :: lane_underscore) (ci_2_20 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_20))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_20))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c"
	| fun_vextbinop___case_5 :
		"list_all (λ (iter_343 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_343)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_344 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_344)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) ⟹
		 list_all (λ (ci_1_21 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_21)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_21 :: lane_underscore). ((proj_lane__0 ci_1_21) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_21 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_21)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_21 :: lane_underscore). ((proj_lane__0 ci_2_21) ≠ None)) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (ci_1_21 :: lane_underscore) (ci_2_21 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_21))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_21))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_22 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_22)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_22 :: lane_underscore). ((proj_lane__0 ci_1_22) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_22 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_22)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_22 :: lane_underscore). ((proj_lane__0 ci_2_22) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_22 :: lane_underscore) (ci_2_22 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_22))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_22)))))))))))) ci_1_lst ci_2_lst ⟹
		 (ci_1_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ⟹
		 (ci_2_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ⟹
		 list_all (λ (ci_1_24 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_24)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_24 :: lane_underscore). ((proj_lane__0 ci_1_24) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_24 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_24)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_24 :: lane_underscore). ((proj_lane__0 ci_2_24) ≠ None)) ci_2_lst ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (ci_1_24 :: lane_underscore) (ci_2_24 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_24))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_24))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c"
	| fun_vextbinop___case_6 :
		"list_all (λ (iter_345 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_345)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_346 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_346)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) ⟹
		 list_all (λ (ci_1_25 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_25)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_25 :: lane_underscore). ((proj_lane__0 ci_1_25) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_25 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_25)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_25 :: lane_underscore). ((proj_lane__0 ci_2_25) ≠ None)) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (ci_1_25 :: lane_underscore) (ci_2_25 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_25))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_25))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_26 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_26)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_26 :: lane_underscore). ((proj_lane__0 ci_1_26) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_26 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_26)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_26 :: lane_underscore). ((proj_lane__0 ci_2_26) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_26 :: lane_underscore) (ci_2_26 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_26))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_26)))))))))))) ci_1_lst ci_2_lst ⟹
		 (ci_1_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ⟹
		 (ci_2_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ⟹
		 list_all (λ (ci_1_28 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_28)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_28 :: lane_underscore). ((proj_lane__0 ci_1_28) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_28 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_28)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_28 :: lane_underscore). ((proj_lane__0 ci_2_28) ≠ None)) ci_2_lst ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (ci_1_28 :: lane_underscore) (ci_2_28 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_28))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_28))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c"
	| fun_vextbinop___case_7 :
		"list_all (λ (iter_347 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_347)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_348 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_348)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) ⟹
		 list_all (λ (ci_1_29 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_29)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_29 :: lane_underscore). ((proj_lane__0 ci_1_29) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_29 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_29)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_29 :: lane_underscore). ((proj_lane__0 ci_2_29) ≠ None)) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (ci_1_29 :: lane_underscore) (ci_2_29 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_29))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_29))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_30 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_30)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_30 :: lane_underscore). ((proj_lane__0 ci_1_30) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_30 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_30)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_30 :: lane_underscore). ((proj_lane__0 ci_2_30) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_30 :: lane_underscore) (ci_2_30 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_30))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_30)))))))))))) ci_1_lst ci_2_lst ⟹
		 (ci_1_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ⟹
		 (ci_2_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ⟹
		 list_all (λ (ci_1_32 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_32)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_32 :: lane_underscore). ((proj_lane__0 ci_1_32) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_32 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_32)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_32 :: lane_underscore). ((proj_lane__0 ci_2_32) ≠ None)) ci_2_lst ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (ci_1_32 :: lane_underscore) (ci_2_32 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_32))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_32))))))))))) ci_1_lst ci_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c"
	| fun_vextbinop___case_8 :
		"list_all (λ (ci_1_33 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_1_33)) ci_1_lst ⟹
		 list_all (λ (ci_2_33 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_2_33)) ci_2_lst ⟹
		 list_all (λ (iter_349 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_349)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_350 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_350)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) ⟹
		 ((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 list_all (λ (iter_351 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I32)))) iter_351)) (concat_underscore  (list_zipWith (λ (cj_1_41 :: iN) (cj_2_41 :: iN). [cj_1_41, cj_2_41]) cj_1_lst cj_2_lst)) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_34 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_34)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_34 :: lane_underscore). ((proj_lane__0 ci_1_34) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_34 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_34)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_34 :: lane_underscore). ((proj_lane__0 ci_2_34) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_34 :: lane_underscore) (ci_2_34 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_34))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_34)))))))))) ci_1_lst ci_2_lst ⟹
		 list_all (λ (ci_1_35 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_35)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_35 :: lane_underscore). ((proj_lane__0 ci_1_35) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_35 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_35))))))))) ci_1_lst ⟹
		 list_all (λ (ci_2_35 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_35)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_35 :: lane_underscore). ((proj_lane__0 ci_2_35) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_35 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_35))))))))) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_42 :: iN) (cj_2_42 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_42 cj_2_42)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_43 :: iN) (cj_2_43 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_43 cj_2_43))))) cj_1_lst cj_2_lst ⟹
		 (ci_1_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ⟹
		 (ci_2_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2)) ⟹
		 list_all (λ (ci_1_37 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_37)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_37 :: lane_underscore). ((proj_lane__0 ci_1_37) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_37 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_37)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_37 :: lane_underscore). ((proj_lane__0 ci_2_37) ≠ None)) ci_2_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_44 :: iN) (cj_2_44 :: iN). [cj_1_44, cj_2_44]) cj_1_lst cj_2_lst)) = (list_zipWith (λ (ci_1_37 :: lane_underscore) (ci_2_37 :: lane_underscore). (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_37))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_37))))))))) ci_1_lst ci_2_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_45 :: iN) (cj_2_45 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_45 cj_2_45)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 DOTS) c_1 c_2 c"
	| fun_vextbinop___case_9 :
		"list_all (λ (ci_1_38 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_1_38)) ci_1_lst ⟹
		 list_all (λ (ci_2_38 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_2_38)) ci_2_lst ⟹
		 list_all (λ (iter_352 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_352)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_353 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_353)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) ⟹
		 ((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 list_all (λ (iter_354 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I32)))) iter_354)) (concat_underscore  (list_zipWith (λ (cj_1_46 :: iN) (cj_2_46 :: iN). [cj_1_46, cj_2_46]) cj_1_lst cj_2_lst)) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_39 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_39)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_39 :: lane_underscore). ((proj_lane__0 ci_1_39) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_39 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_39)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_39 :: lane_underscore). ((proj_lane__0 ci_2_39) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_39 :: lane_underscore) (ci_2_39 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_39))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_39)))))))))) ci_1_lst ci_2_lst ⟹
		 list_all (λ (ci_1_40 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_40)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_40 :: lane_underscore). ((proj_lane__0 ci_1_40) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_40 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_40))))))))) ci_1_lst ⟹
		 list_all (λ (ci_2_40 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_40)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_40 :: lane_underscore). ((proj_lane__0 ci_2_40) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_40 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_40))))))))) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_47 :: iN) (cj_2_47 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_47 cj_2_47)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_48 :: iN) (cj_2_48 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_48 cj_2_48))))) cj_1_lst cj_2_lst ⟹
		 (ci_1_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ⟹
		 (ci_2_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2)) ⟹
		 list_all (λ (ci_1_42 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_42)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_42 :: lane_underscore). ((proj_lane__0 ci_1_42) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_42 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_42)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_42 :: lane_underscore). ((proj_lane__0 ci_2_42) ≠ None)) ci_2_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_49 :: iN) (cj_2_49 :: iN). [cj_1_49, cj_2_49]) cj_1_lst cj_2_lst)) = (list_zipWith (λ (ci_1_42 :: lane_underscore) (ci_2_42 :: lane_underscore). (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_42))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_42))))))))) ci_1_lst ci_2_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_50 :: iN) (cj_2_50 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_50 cj_2_50)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 DOTS) c_1 c_2 c"
	| fun_vextbinop___case_10 :
		"list_all (λ (ci_1_43 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_1_43)) ci_1_lst ⟹
		 list_all (λ (ci_2_43 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_2_43)) ci_2_lst ⟹
		 list_all (λ (iter_355 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_355)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_356 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_356)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) ⟹
		 ((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 list_all (λ (iter_357 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I32)))) iter_357)) (concat_underscore  (list_zipWith (λ (cj_1_51 :: iN) (cj_2_51 :: iN). [cj_1_51, cj_2_51]) cj_1_lst cj_2_lst)) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_44 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_44)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_44 :: lane_underscore). ((proj_lane__0 ci_1_44) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_44 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_44)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_44 :: lane_underscore). ((proj_lane__0 ci_2_44) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_44 :: lane_underscore) (ci_2_44 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_44))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_44)))))))))) ci_1_lst ci_2_lst ⟹
		 list_all (λ (ci_1_45 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_45)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_45 :: lane_underscore). ((proj_lane__0 ci_1_45) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_45 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_45))))))))) ci_1_lst ⟹
		 list_all (λ (ci_2_45 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_45)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_45 :: lane_underscore). ((proj_lane__0 ci_2_45) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_45 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_45))))))))) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_52 :: iN) (cj_2_52 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_52 cj_2_52)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_53 :: iN) (cj_2_53 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_53 cj_2_53))))) cj_1_lst cj_2_lst ⟹
		 (ci_1_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ⟹
		 (ci_2_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2)) ⟹
		 list_all (λ (ci_1_47 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_47)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_47 :: lane_underscore). ((proj_lane__0 ci_1_47) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_47 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_47)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_47 :: lane_underscore). ((proj_lane__0 ci_2_47) ≠ None)) ci_2_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_54 :: iN) (cj_2_54 :: iN). [cj_1_54, cj_2_54]) cj_1_lst cj_2_lst)) = (list_zipWith (λ (ci_1_47 :: lane_underscore) (ci_2_47 :: lane_underscore). (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_47))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_47))))))))) ci_1_lst ci_2_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_55 :: iN) (cj_2_55 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_55 cj_2_55)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 DOTS) c_1 c_2 c"
	| fun_vextbinop___case_11 :
		"list_all (λ (ci_1_48 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_1_48)) ci_1_lst ⟹
		 list_all (λ (ci_2_48 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_2_48)) ci_2_lst ⟹
		 list_all (λ (iter_358 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_358)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_359 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_359)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) ⟹
		 ((size (valtype_Inn Inn_I32)) ≠ None) ⟹
		 list_all (λ (iter_360 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I32)))) iter_360)) (concat_underscore  (list_zipWith (λ (cj_1_56 :: iN) (cj_2_56 :: iN). [cj_1_56, cj_2_56]) cj_1_lst cj_2_lst)) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_49 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_49)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_49 :: lane_underscore). ((proj_lane__0 ci_1_49) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_49 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_49)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_49 :: lane_underscore). ((proj_lane__0 ci_2_49) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_49 :: lane_underscore) (ci_2_49 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_49))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_49)))))))))) ci_1_lst ci_2_lst ⟹
		 list_all (λ (ci_1_50 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_50)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_50 :: lane_underscore). ((proj_lane__0 ci_1_50) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_50 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_50))))))))) ci_1_lst ⟹
		 list_all (λ (ci_2_50 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_50)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_50 :: lane_underscore). ((proj_lane__0 ci_2_50) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_50 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I32)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_50))))))))) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_57 :: iN) (cj_2_57 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_57 cj_2_57)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_58 :: iN) (cj_2_58 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_58 cj_2_58))))) cj_1_lst cj_2_lst ⟹
		 (ci_1_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ⟹
		 (ci_2_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2)) ⟹
		 list_all (λ (ci_1_52 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_52)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_52 :: lane_underscore). ((proj_lane__0 ci_1_52) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_52 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_52)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_52 :: lane_underscore). ((proj_lane__0 ci_2_52) ≠ None)) ci_2_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_59 :: iN) (cj_2_59 :: iN). [cj_1_59, cj_2_59]) cj_1_lst cj_2_lst)) = (list_zipWith (λ (ci_1_52 :: lane_underscore) (ci_2_52 :: lane_underscore). (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_52))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_52))))))))) ci_1_lst ci_2_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (λ (cj_1_60 :: iN) (cj_2_60 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_60 cj_2_60)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 DOTS) c_1 c_2 c"
	| fun_vextbinop___case_12 :
		"list_all (λ (ci_1_53 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_1_53)) ci_1_lst ⟹
		 list_all (λ (ci_2_53 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_2_53)) ci_2_lst ⟹
		 list_all (λ (iter_361 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_361)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_362 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_362)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) ⟹
		 ((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 list_all (λ (iter_363 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I64)))) iter_363)) (concat_underscore  (list_zipWith (λ (cj_1_61 :: iN) (cj_2_61 :: iN). [cj_1_61, cj_2_61]) cj_1_lst cj_2_lst)) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_54 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_54)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_54 :: lane_underscore). ((proj_lane__0 ci_1_54) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_54 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_54)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_54 :: lane_underscore). ((proj_lane__0 ci_2_54) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_54 :: lane_underscore) (ci_2_54 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_54))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_54)))))))))) ci_1_lst ci_2_lst ⟹
		 list_all (λ (ci_1_55 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_55)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_55 :: lane_underscore). ((proj_lane__0 ci_1_55) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_55 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_55))))))))) ci_1_lst ⟹
		 list_all (λ (ci_2_55 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_55)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_55 :: lane_underscore). ((proj_lane__0 ci_2_55) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_55 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_55))))))))) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_62 :: iN) (cj_2_62 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_62 cj_2_62)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_63 :: iN) (cj_2_63 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_63 cj_2_63))))) cj_1_lst cj_2_lst ⟹
		 (ci_1_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ⟹
		 (ci_2_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2)) ⟹
		 list_all (λ (ci_1_57 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_57)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_57 :: lane_underscore). ((proj_lane__0 ci_1_57) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_57 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_57)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_57 :: lane_underscore). ((proj_lane__0 ci_2_57) ≠ None)) ci_2_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_64 :: iN) (cj_2_64 :: iN). [cj_1_64, cj_2_64]) cj_1_lst cj_2_lst)) = (list_zipWith (λ (ci_1_57 :: lane_underscore) (ci_2_57 :: lane_underscore). (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_57))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_57))))))))) ci_1_lst ci_2_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_65 :: iN) (cj_2_65 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_65 cj_2_65)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 DOTS) c_1 c_2 c"
	| fun_vextbinop___case_13 :
		"list_all (λ (ci_1_58 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_1_58)) ci_1_lst ⟹
		 list_all (λ (ci_2_58 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ci_2_58)) ci_2_lst ⟹
		 list_all (λ (iter_364 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_364)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_365 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_2))) iter_365)) (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) ⟹
		 ((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 list_all (λ (iter_366 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I64)))) iter_366)) (concat_underscore  (list_zipWith (λ (cj_1_66 :: iN) (cj_2_66 :: iN). [cj_1_66, cj_2_66]) cj_1_lst cj_2_lst)) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_59 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_59)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_59 :: lane_underscore). ((proj_lane__0 ci_1_59) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_59 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_59)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_59 :: lane_underscore). ((proj_lane__0 ci_2_59) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_59 :: lane_underscore) (ci_2_59 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_59))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_59)))))))))) ci_1_lst ci_2_lst ⟹
		 list_all (λ (ci_1_60 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_60)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_60 :: lane_underscore). ((proj_lane__0 ci_1_60) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_60 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_60))))))))) ci_1_lst ⟹
		 list_all (λ (ci_2_60 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_60)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_60 :: lane_underscore). ((proj_lane__0 ci_2_60) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_60 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_60))))))))) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_67 :: iN) (cj_2_67 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_67 cj_2_67)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_68 :: iN) (cj_2_68 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_68 cj_2_68))))) cj_1_lst cj_2_lst ⟹
		 (ci_1_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) ⟹
		 (ci_2_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2)) ⟹
		 list_all (λ (ci_1_62 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_62)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_62 :: lane_underscore). ((proj_lane__0 ci_1_62) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_62 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_62)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_62 :: lane_underscore). ((proj_lane__0 ci_2_62) ≠ None)) ci_2_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_69 :: iN) (cj_2_69 :: iN). [cj_1_69, cj_2_69]) cj_1_lst cj_2_lst)) = (list_zipWith (λ (ci_1_62 :: lane_underscore) (ci_2_62 :: lane_underscore). (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_62))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_62))))))))) ci_1_lst ci_2_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_70 :: iN) (cj_2_70 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_70 cj_2_70)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 DOTS) c_1 c_2 c"
	| fun_vextbinop___case_14 :
		"list_all (λ (ci_1_63 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_1_63)) ci_1_lst ⟹
		 list_all (λ (ci_2_63 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_2_63)) ci_2_lst ⟹
		 list_all (λ (iter_367 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_367)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_368 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_368)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) ⟹
		 ((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 list_all (λ (iter_369 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I64)))) iter_369)) (concat_underscore  (list_zipWith (λ (cj_1_71 :: iN) (cj_2_71 :: iN). [cj_1_71, cj_2_71]) cj_1_lst cj_2_lst)) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_64 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_64)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_64 :: lane_underscore). ((proj_lane__0 ci_1_64) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_64 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_64)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_64 :: lane_underscore). ((proj_lane__0 ci_2_64) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_64 :: lane_underscore) (ci_2_64 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_64))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_64)))))))))) ci_1_lst ci_2_lst ⟹
		 list_all (λ (ci_1_65 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_65)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_65 :: lane_underscore). ((proj_lane__0 ci_1_65) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_65 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_65))))))))) ci_1_lst ⟹
		 list_all (λ (ci_2_65 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_65)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_65 :: lane_underscore). ((proj_lane__0 ci_2_65) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_65 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_65))))))))) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_72 :: iN) (cj_2_72 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_72 cj_2_72)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_73 :: iN) (cj_2_73 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_73 cj_2_73))))) cj_1_lst cj_2_lst ⟹
		 (ci_1_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ⟹
		 (ci_2_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2)) ⟹
		 list_all (λ (ci_1_67 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_67)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_67 :: lane_underscore). ((proj_lane__0 ci_1_67) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_67 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_67)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_67 :: lane_underscore). ((proj_lane__0 ci_2_67) ≠ None)) ci_2_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_74 :: iN) (cj_2_74 :: iN). [cj_1_74, cj_2_74]) cj_1_lst cj_2_lst)) = (list_zipWith (λ (ci_1_67 :: lane_underscore) (ci_2_67 :: lane_underscore). (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_67))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_67))))))))) ci_1_lst ci_2_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_75 :: iN) (cj_2_75 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_75 cj_2_75)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 DOTS) c_1 c_2 c"
	| fun_vextbinop___case_15 :
		"list_all (λ (ci_1_68 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_1_68)) ci_1_lst ⟹
		 list_all (λ (ci_2_68 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ci_2_68)) ci_2_lst ⟹
		 list_all (λ (iter_370 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_370)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) ⟹
		 list_all (λ (iter_371 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_2))) iter_371)) (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) ⟹
		 ((size (valtype_Inn Inn_I64)) ≠ None) ⟹
		 list_all (λ (iter_372 :: iN). (wf_uN (the ((size (valtype_Inn Inn_I64)))) iter_372)) (concat_underscore  (list_zipWith (λ (cj_1_76 :: iN) (cj_2_76 :: iN). [cj_1_76, cj_2_76]) cj_1_lst cj_2_lst)) ⟹
		 ((length ci_1_lst) = (length ci_2_lst)) ⟹
		 list_all (λ (ci_1_69 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_69)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_69 :: lane_underscore). ((proj_lane__0 ci_1_69) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_69 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_69)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_69 :: lane_underscore). ((proj_lane__0 ci_2_69) ≠ None)) ci_2_lst ⟹
		 list_all2 (λ (ci_1_69 :: lane_underscore) (ci_2_69 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_69))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_69)))))))))) ci_1_lst ci_2_lst ⟹
		 list_all (λ (ci_1_70 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_70)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_70 :: lane_underscore). ((proj_lane__0 ci_1_70) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_70 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_70))))))))) ci_1_lst ⟹
		 list_all (λ (ci_2_70 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_70)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_70 :: lane_underscore). ((proj_lane__0 ci_2_70) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_70 :: lane_underscore). (wf_uN (the ((size (valtype_Inn Inn_I64)))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_70))))))))) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_77 :: iN) (cj_2_77 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_77 cj_2_77)))) cj_1_lst cj_2_lst))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) ⟹
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) ⟹
		 ((length cj_1_lst) = (length cj_2_lst)) ⟹
		 list_all2 (λ (cj_1_78 :: iN) (cj_2_78 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_78 cj_2_78))))) cj_1_lst cj_2_lst ⟹
		 (ci_1_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) ⟹
		 (ci_2_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2)) ⟹
		 list_all (λ (ci_1_72 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_72)))) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1_72 :: lane_underscore). ((proj_lane__0 ci_1_72) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_2_72 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_72)))) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2_72 :: lane_underscore). ((proj_lane__0 ci_2_72) ≠ None)) ci_2_lst ⟹
		 ((concat_underscore  (list_zipWith (λ (cj_1_79 :: iN) (cj_2_79 :: iN). [cj_1_79, cj_2_79]) cj_1_lst cj_2_lst)) = (list_zipWith (λ (ci_1_72 :: lane_underscore) (ci_2_72 :: lane_underscore). (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_72))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_72))))))))) ci_1_lst ci_2_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (λ (cj_1_80 :: iN) (cj_2_80 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_80 cj_2_80)))) cj_1_lst cj_2_lst))) ⟹
		 (M_1 = M_1_0) ⟹
		 fun_vextbinop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 DOTS) c_1 c_2 c"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:608.6-608.16 *)
inductive fun_vshiftop_underscore :: "ishape ⇒ vshiftop_underscore ⇒ lane_underscore ⇒ u32 ⇒ lane_underscore ⇒ bool" where
	  fun_vshiftop__case_0 :
		"(v_Jnn = Jnn_1) ⟹
		 (v_Jnn = Jnn_0) ⟹
		 (v_M = M_0) ⟹
		 fun_vshiftop_underscore (ishape_X v_Jnn (mk_dim v_M)) (mk_vshiftop__0 Jnn_0 M_0 vshiftop_Jnn_N_SHL) (mk_lane__2 Jnn_1 lane) (mk_uN v_n) (mk_lane__2 v_Jnn (ishl_underscore (lsizenn (lanetype_Jnn v_Jnn)) lane (mk_uN v_n)))"
	| fun_vshiftop__case_1 :
		"(v_Jnn = Jnn_1) ⟹
		 (v_Jnn = Jnn_0) ⟹
		 (v_M = M_0) ⟹
		 fun_vshiftop_underscore (ishape_X v_Jnn (mk_dim v_M)) (mk_vshiftop__0 Jnn_0 M_0 (vshiftop_Jnn_N_SHR v_sx)) (mk_lane__2 Jnn_1 lane) (mk_uN v_n) (mk_lane__2 v_Jnn (ishr_underscore (lsizenn (lanetype_Jnn v_Jnn)) v_sx lane (mk_uN v_n)))"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:5.1-5.39 *)
type_synonym addr = "nat"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:6.1-6.53 *)
type_synonym funcaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:7.1-7.53 *)
type_synonym globaladdr = "addr"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:8.1-8.51 *)
type_synonym tableaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:9.1-9.50 *)
type_synonym memaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:10.1-10.49 *)
type_synonym elemaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:11.1-11.49 *)
type_synonym dataaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:12.1-12.49 *)
type_synonym hostaddr = "addr"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:25.1-26.70 *)
datatype externaddr =
	  externaddr_FUNC "funcaddr"
	| externaddr_GLOBAL "globaladdr"
	| externaddr_TABLE "tableaddr"
	| externaddr_MEM "memaddr"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:37.1-38.62 *)
datatype num =
	  num_CONST "numtype" "num_underscore"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:37.8-37.11 *)
inductive wf_num :: "num ⇒ bool" where
	  num_case_0 :
		"(wf_num_underscore v_numtype var_0) ⟹
		 wf_num (num_CONST v_numtype var_0)"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:39.1-40.62 *)
datatype vec =
	  vec_VCONST "vectype" "vec_underscore"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:39.8-39.11 *)
inductive wf_vec :: "vec ⇒ bool" where
	  vec_case_0 :
		"((size (valtype_vectype v_vectype)) ≠ None) ⟹
		 (wf_uN (the ((size (valtype_vectype v_vectype)))) var_0) ⟹
		 wf_vec (vec_VCONST v_vectype var_0)"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:41.1-42.71 *)
datatype ref =
	  ref_REF_NULL "reftype"
	| REF_FUNC_ADDR "funcaddr"
	| REF_HOST_ADDR "hostaddr"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:43.1-44.20 *)
datatype val =
	  val_CONST "numtype" "num_underscore"
	| val_VCONST "vectype" "vec_underscore"
	| val_REF_NULL "reftype"
	| val_REF_FUNC_ADDR "funcaddr"
	| val_REF_HOST_ADDR "hostaddr"

(* Auxiliary Definition at:  *)
function (sequential) val_ref :: "ref ⇒ val" where
		  "val_ref (ref_REF_NULL x0) = (val_REF_NULL x0)"
		| "val_ref (REF_FUNC_ADDR x0) = (val_REF_FUNC_ADDR x0)"
		| "val_ref (REF_HOST_ADDR x0) = (val_REF_HOST_ADDR x0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:43.8-43.11 *)
inductive wf_val :: "val ⇒ bool" where
	  val_case_0 :
		"(wf_num_underscore v_numtype var_0) ⟹
		 wf_val (val_CONST v_numtype var_0)"
	| val_case_1 :
		"((size (valtype_vectype v_vectype)) ≠ None) ⟹
		 (wf_uN (the ((size (valtype_vectype v_vectype)))) var_0) ⟹
		 wf_val (val_VCONST v_vectype var_0)"
	| val_case_2 :
		"wf_val (val_REF_NULL v_reftype)"
	| val_case_3 :
		"wf_val (val_REF_FUNC_ADDR v_funcaddr)"
	| val_case_4 :
		"wf_val (val_REF_HOST_ADDR v_hostaddr)"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:46.1-47.22 *)
datatype result =
	  underscore_VALS "(val list)"
	| TRAP

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:46.8-46.14 *)
inductive wf_result :: "result ⇒ bool" where
	  result_case_0 :
		"list_all (λ (v_val :: val). (wf_val v_val)) val_lst ⟹
		 wf_result (underscore_VALS val_lst)"
	| result_case_1 :
		"wf_result TRAP"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:78.1-80.22 *)
record exportinst =
	NAME :: "name"
	ADDR :: "externaddr"

definition append_exportinst :: "exportinst ⇒ exportinst ⇒ exportinst" where
	"append_exportinst arg1 arg2 = ⦇
		NAME = NAME arg1,
		ADDR = ADDR arg1
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:78.8-78.18 *)
inductive wf_exportinst :: "exportinst ⇒ bool" where
	  exportinst_case_underscore :
		"(wf_name var_0) ⟹
		 wf_exportinst ⦇ NAME = var_0, ADDR = var_1 ⦈"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:82.1-90.26 *)
record moduleinst =
	TYPES :: "(functype list)"
	FUNCS :: "(funcaddr list)"
	GLOBALS :: "(globaladdr list)"
	TABLES :: "(tableaddr list)"
	MEMS :: "(memaddr list)"
	ELEMS :: "(elemaddr list)"
	DATAS :: "(dataaddr list)"
	EXPORTS :: "(exportinst list)"

definition append_moduleinst :: "moduleinst ⇒ moduleinst ⇒ moduleinst" where
	"append_moduleinst arg1 arg2 = ⦇
		TYPES = TYPES arg1 @ TYPES arg2,
		FUNCS = FUNCS arg1 @ FUNCS arg2,
		GLOBALS = GLOBALS arg1 @ GLOBALS arg2,
		TABLES = TABLES arg1 @ TABLES arg2,
		MEMS = MEMS arg1 @ MEMS arg2,
		ELEMS = ELEMS arg1 @ ELEMS arg2,
		DATAS = DATAS arg1 @ DATAS arg2,
		EXPORTS = EXPORTS arg1 @ EXPORTS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:82.8-82.18 *)
inductive wf_moduleinst :: "moduleinst ⇒ bool" where
	  moduleinst_case_underscore :
		"list_all (λ (var_7 :: exportinst). (wf_exportinst var_7)) var_7 ⟹
		 wf_moduleinst ⦇ TYPES = var_0, FUNCS = var_1, GLOBALS = var_2, TABLES = var_3, MEMS = var_4, ELEMS = var_5, DATAS = var_6, EXPORTS = var_7 ⦈"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:60.1-63.16 *)
record funcinst =
	funcinst_TYPE :: "functype"
	funcinst_MODULE :: "moduleinst"
	CODE :: "func"

definition append_funcinst :: "funcinst ⇒ funcinst ⇒ funcinst" where
	"append_funcinst arg1 arg2 = ⦇
		funcinst_TYPE = funcinst_TYPE arg1,
		funcinst_MODULE = append_moduleinst (funcinst_MODULE arg1) (funcinst_MODULE arg2),
		CODE = CODE arg1
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:60.8-60.16 *)
inductive wf_funcinst :: "funcinst ⇒ bool" where
	  funcinst_case_underscore :
		"(wf_moduleinst var_1) ⟹
		 (wf_func var_2) ⟹
		 wf_funcinst ⦇ funcinst_TYPE = var_0, funcinst_MODULE = var_1, CODE = var_2 ⦈"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:64.1-66.16 *)
record globalinst =
	globalinst_TYPE :: "globaltype"
	VALUE :: "val"

definition append_globalinst :: "globalinst ⇒ globalinst ⇒ globalinst" where
	"append_globalinst arg1 arg2 = ⦇
		globalinst_TYPE = globalinst_TYPE arg1,
		VALUE = VALUE arg1
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:64.8-64.18 *)
inductive wf_globalinst :: "globalinst ⇒ bool" where
	  globalinst_case_underscore :
		"(wf_val var_1) ⟹
		 wf_globalinst ⦇ globalinst_TYPE = var_0, VALUE = var_1 ⦈"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:67.1-69.16 *)
record tableinst =
	tableinst_TYPE :: "tabletype"
	REFS :: "(ref list)"

definition append_tableinst :: "tableinst ⇒ tableinst ⇒ tableinst" where
	"append_tableinst arg1 arg2 = ⦇
		tableinst_TYPE = tableinst_TYPE arg1,
		REFS = REFS arg1 @ REFS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:67.8-67.17 *)
inductive wf_tableinst :: "tableinst ⇒ bool" where
	  tableinst_case_underscore :
		"(wf_tabletype var_0) ⟹
		 wf_tableinst ⦇ tableinst_TYPE = var_0, REFS = var_1 ⦈"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:70.1-72.18 *)
record meminst =
	meminst_TYPE :: "memtype"
	BYTES :: "(byte list)"

definition append_meminst :: "meminst ⇒ meminst ⇒ meminst" where
	"append_meminst arg1 arg2 = ⦇
		meminst_TYPE = meminst_TYPE arg1,
		BYTES = BYTES arg1 @ BYTES arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:70.8-70.15 *)
inductive wf_meminst :: "meminst ⇒ bool" where
	  meminst_case_underscore :
		"(wf_memtype var_0) ⟹
		 list_all (λ (var_1 :: byte). (wf_byte var_1)) var_1 ⟹
		 wf_meminst ⦇ meminst_TYPE = var_0, BYTES = var_1 ⦈"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:73.1-75.16 *)
record eleminst =
	eleminst_TYPE :: "elemtype"
	eleminst_REFS :: "(ref list)"

definition append_eleminst :: "eleminst ⇒ eleminst ⇒ eleminst" where
	"append_eleminst arg1 arg2 = ⦇
		eleminst_TYPE = eleminst_TYPE arg1,
		eleminst_REFS = eleminst_REFS arg1 @ eleminst_REFS arg2
	⦈"



(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:76.1-77.18 *)
record datainst =
	datainst_BYTES :: "(byte list)"

definition append_datainst :: "datainst ⇒ datainst ⇒ datainst" where
	"append_datainst arg1 arg2 = ⦇
		datainst_BYTES = datainst_BYTES arg1 @ datainst_BYTES arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:76.8-76.16 *)
inductive wf_datainst :: "datainst ⇒ bool" where
	  datainst_case_underscore :
		"list_all (λ (var_0 :: byte). (wf_byte var_0)) var_0 ⟹
		 wf_datainst ⦇ datainst_BYTES = var_0 ⦈"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:104.1-110.22 *)
record store =
	store_FUNCS :: "(funcinst list)"
	store_GLOBALS :: "(globalinst list)"
	store_TABLES :: "(tableinst list)"
	store_MEMS :: "(meminst list)"
	store_ELEMS :: "(eleminst list)"
	store_DATAS :: "(datainst list)"

definition append_store :: "store ⇒ store ⇒ store" where
	"append_store arg1 arg2 = ⦇
		store_FUNCS = store_FUNCS arg1 @ store_FUNCS arg2,
		store_GLOBALS = store_GLOBALS arg1 @ store_GLOBALS arg2,
		store_TABLES = store_TABLES arg1 @ store_TABLES arg2,
		store_MEMS = store_MEMS arg1 @ store_MEMS arg2,
		store_ELEMS = store_ELEMS arg1 @ store_ELEMS arg2,
		store_DATAS = store_DATAS arg1 @ store_DATAS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:104.8-104.13 *)
inductive wf_store :: "store ⇒ bool" where
	  store_case_underscore :
		"list_all (λ (var_0 :: funcinst). (wf_funcinst var_0)) var_0 ⟹
		 list_all (λ (var_1 :: globalinst). (wf_globalinst var_1)) var_1 ⟹
		 list_all (λ (var_2 :: tableinst). (wf_tableinst var_2)) var_2 ⟹
		 list_all (λ (var_3 :: meminst). (wf_meminst var_3)) var_3 ⟹
		 list_all (λ (var_5 :: datainst). (wf_datainst var_5)) var_5 ⟹
		 wf_store ⦇ store_FUNCS = var_0, store_GLOBALS = var_1, store_TABLES = var_2, store_MEMS = var_3, store_ELEMS = var_4, store_DATAS = var_5 ⦈"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:112.1-114.24 *)
record frame =
	LOCALS :: "(val list)"
	frame_MODULE :: "moduleinst"

definition append_frame :: "frame ⇒ frame ⇒ frame" where
	"append_frame arg1 arg2 = ⦇
		LOCALS = LOCALS arg1 @ LOCALS arg2,
		frame_MODULE = append_moduleinst (frame_MODULE arg1) (frame_MODULE arg2)
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:112.8-112.13 *)
inductive wf_frame :: "frame ⇒ bool" where
	  frame_case_underscore :
		"list_all (λ (var_0 :: val). (wf_val var_0)) var_0 ⟹
		 (wf_moduleinst var_1) ⟹
		 wf_frame ⦇ LOCALS = var_0, frame_MODULE = var_1 ⦈"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:116.1-116.47 *)
datatype state =
	  mk_state "store" "frame"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:116.8-116.13 *)
inductive wf_state :: "state ⇒ bool" where
	  state_case_0 :
		"(wf_store v_store) ⟹
		 (wf_frame v_frame) ⟹
		 wf_state (mk_state v_store v_frame)"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st7 =
	  admininstr_st7_TRAP
	| CALL_ADDR "funcaddr"
	| admininstr_st7_REF_HOST_ADDR "hostaddr"
	| admininstr_st7_REF_FUNC_ADDR "funcaddr"
	| admininstr_st7_DATA_DROP "dataidx"
	| admininstr_st7_MEMORY_INIT "dataidx"
	| admininstr_st7_MEMORY_COPY
	| admininstr_st7_MEMORY_FILL
	| admininstr_st7_MEMORY_GROW

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st6 =
	  admininstr_st6_MEMORY_SIZE
	| admininstr_st6_VSTORE_LANE "vectype" "sz" "memarg" "laneidx"
	| admininstr_st6_VSTORE "vectype" "memarg"
	| admininstr_st6_VLOAD_LANE "vectype" "sz" "memarg" "laneidx"
	| admininstr_st6_VLOAD "vectype" "(vloadop option)" "memarg"
	| admininstr_st6_STORE "numtype" "(sz option)" "memarg"
	| admininstr_st6_LOAD "numtype" "(loadop_underscore option)" "memarg"
	| admininstr_st6_ELEM_DROP "elemidx"
	| admininstr_st6_TABLE_INIT "tableidx" "elemidx"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st5 =
	  admininstr_st5_TABLE_COPY "tableidx" "tableidx"
	| admininstr_st5_TABLE_FILL "tableidx"
	| admininstr_st5_TABLE_GROW "tableidx"
	| admininstr_st5_TABLE_SIZE "tableidx"
	| admininstr_st5_TABLE_SET "tableidx"
	| admininstr_st5_TABLE_GET "tableidx"
	| admininstr_st5_GLOBAL_SET "globalidx"
	| admininstr_st5_GLOBAL_GET "globalidx"
	| admininstr_st5_LOCAL_TEE "localidx"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st4 =
	  admininstr_st4_LOCAL_SET "localidx"
	| admininstr_st4_LOCAL_GET "localidx"
	| admininstr_st4_REF_IS_NULL
	| admininstr_st4_REF_FUNC "funcidx"
	| admininstr_st4_REF_NULL "reftype"
	| admininstr_st4_VCVTOP "shape" "shape" "vcvtop"
	| admininstr_st4_VNARROW "ishape" "ishape" "sx"
	| admininstr_st4_VEXTBINOP "ishape" "ishape" "vextbinop_underscore"
	| admininstr_st4_VEXTUNOP "ishape" "ishape" "vextunop_underscore"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st3 =
	  admininstr_st3_VREPLACE_LANE "shape" "laneidx"
	| admininstr_st3_VEXTRACT_LANE "shape" "(sx option)" "laneidx"
	| admininstr_st3_VSPLAT "shape"
	| admininstr_st3_VSHUFFLE "ishape" "(laneidx list)"
	| admininstr_st3_VSWIZZLE "ishape"
	| admininstr_st3_VBITMASK "ishape"
	| admininstr_st3_VSHIFTOP "ishape" "vshiftop_underscore"
	| admininstr_st3_VRELOP "shape" "vrelop_underscore"
	| admininstr_st3_VTESTOP "shape" "vtestop_underscore"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st2 =
	  admininstr_st2_VBINOP "shape" "vbinop_underscore"
	| admininstr_st2_VUNOP "shape" "vunop_underscore"
	| admininstr_st2_VVTESTOP "vectype" "vvtestop"
	| admininstr_st2_VVTERNOP "vectype" "vvternop"
	| admininstr_st2_VVBINOP "vectype" "vvbinop"
	| admininstr_st2_VVUNOP "vectype" "vvunop"
	| admininstr_st2_VCONST "vectype" "vec_underscore"
	| admininstr_st2_EXTEND "numtype" "n"
	| admininstr_st2_CVTOP "numtype" "numtype" "cvtop"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st1 =
	  admininstr_st1_RELOP "numtype" "relop_underscore"
	| admininstr_st1_TESTOP "numtype" "testop_underscore"
	| admininstr_st1_BINOP "numtype" "binop_underscore"
	| admininstr_st1_UNOP "numtype" "unop_underscore"
	| admininstr_st1_CONST "numtype" "num_underscore"
	| admininstr_st1_RETURN
	| admininstr_st1_CALL_INDIRECT "tableidx" "typeidx"
	| admininstr_st1_CALL "funcidx"
	| admininstr_st1_BR_TABLE "(labelidx list)" "labelidx"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st0 =
	  admininstr_st0_BR_IF "labelidx"
	| admininstr_st0_BR "labelidx"
	| admininstr_st0_IFELSE "blocktype" "(instr list)" "(instr list)"
	| admininstr_st0_LOOP "blocktype" "(instr list)"
	| admininstr_st0_BLOCK "blocktype" "(instr list)"
	| admininstr_st0_SELECT "((valtype list) option)"
	| admininstr_st0_DROP
	| admininstr_st0_UNREACHABLE
	| admininstr_st0_NOP

(* Mutual Recursion at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr =
	  admininstr_sc0 "admininstr_st0"
	| admininstr_sc1 "admininstr_st1"
	| admininstr_sc2 "admininstr_st2"
	| admininstr_sc3 "admininstr_st3"
	| admininstr_sc4 "admininstr_st4"
	| admininstr_sc5 "admininstr_st5"
	| admininstr_sc6 "admininstr_st6"
	| admininstr_sc7 "admininstr_st7"
	| admininstr_sc8 "admininstr_st8"

and

admininstr_st8 =
	  FRAME_underscore "n" "frame" "(admininstr list)"
	| LABEL_underscore "n" "(instr list)" "(admininstr list)"

(* Auxiliary Definition at:  *)
function (sequential) admininstr_instr :: "instr ⇒ admininstr" where
		  "admininstr_instr (instr_sc0 NOP) = (admininstr_sc0 admininstr_st0_NOP)"
		| "admininstr_instr (instr_sc0 UNREACHABLE) = (admininstr_sc0 admininstr_st0_UNREACHABLE)"
		| "admininstr_instr (instr_sc0 DROP) = (admininstr_sc0 admininstr_st0_DROP)"
		| "admininstr_instr (instr_sc0 (SELECT x0)) = (admininstr_sc0 (admininstr_st0_SELECT x0))"
		| "admininstr_instr (instr_sc7 (BLOCK x0 x1)) = (admininstr_sc0 (admininstr_st0_BLOCK x0 x1))"
		| "admininstr_instr (instr_sc7 (LOOP x0 x1)) = (admininstr_sc0 (admininstr_st0_LOOP x0 x1))"
		| "admininstr_instr (instr_sc7 (IFELSE x0 x1 x2)) = (admininstr_sc0 (admininstr_st0_IFELSE x0 x1 x2))"
		| "admininstr_instr (instr_sc0 (BR x0)) = (admininstr_sc0 (admininstr_st0_BR x0))"
		| "admininstr_instr (instr_sc0 (BR_IF x0)) = (admininstr_sc0 (admininstr_st0_BR_IF x0))"
		| "admininstr_instr (instr_sc0 (BR_TABLE x0 x1)) = (admininstr_sc1 (admininstr_st1_BR_TABLE x0 x1))"
		| "admininstr_instr (instr_sc0 (CALL x0)) = (admininstr_sc1 (admininstr_st1_CALL x0))"
		| "admininstr_instr (instr_sc0 (CALL_INDIRECT x0 x1)) = (admininstr_sc1 (admininstr_st1_CALL_INDIRECT x0 x1))"
		| "admininstr_instr (instr_sc1 RETURN) = (admininstr_sc1 admininstr_st1_RETURN)"
		| "admininstr_instr (instr_sc1 (res_CONST x0 x1)) = (admininstr_sc1 (admininstr_st1_CONST x0 x1))"
		| "admininstr_instr (instr_sc1 (UNOP x0 x1)) = (admininstr_sc1 (admininstr_st1_UNOP x0 x1))"
		| "admininstr_instr (instr_sc1 (BINOP x0 x1)) = (admininstr_sc1 (admininstr_st1_BINOP x0 x1))"
		| "admininstr_instr (instr_sc1 (TESTOP x0 x1)) = (admininstr_sc1 (admininstr_st1_TESTOP x0 x1))"
		| "admininstr_instr (instr_sc1 (RELOP x0 x1)) = (admininstr_sc1 (admininstr_st1_RELOP x0 x1))"
		| "admininstr_instr (instr_sc1 (CVTOP x0 x1 x2)) = (admininstr_sc2 (admininstr_st2_CVTOP x0 x1 x2))"
		| "admininstr_instr (instr_sc1 (instr_st1_EXTEND x0 x1)) = (admininstr_sc2 (admininstr_st2_EXTEND x0 x1))"
		| "admininstr_instr (instr_sc1 (VCONST x0 x1)) = (admininstr_sc2 (admininstr_st2_VCONST x0 x1))"
		| "admininstr_instr (instr_sc2 (VVUNOP x0 x1)) = (admininstr_sc2 (admininstr_st2_VVUNOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VVBINOP x0 x1)) = (admininstr_sc2 (admininstr_st2_VVBINOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VVTERNOP x0 x1)) = (admininstr_sc2 (admininstr_st2_VVTERNOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VVTESTOP x0 x1)) = (admininstr_sc2 (admininstr_st2_VVTESTOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VUNOP x0 x1)) = (admininstr_sc2 (admininstr_st2_VUNOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VBINOP x0 x1)) = (admininstr_sc2 (admininstr_st2_VBINOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VTESTOP x0 x1)) = (admininstr_sc3 (admininstr_st3_VTESTOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VRELOP x0 x1)) = (admininstr_sc3 (admininstr_st3_VRELOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VSHIFTOP x0 x1)) = (admininstr_sc3 (admininstr_st3_VSHIFTOP x0 x1))"
		| "admininstr_instr (instr_sc3 (VBITMASK x0)) = (admininstr_sc3 (admininstr_st3_VBITMASK x0))"
		| "admininstr_instr (instr_sc3 (VSWIZZLE x0)) = (admininstr_sc3 (admininstr_st3_VSWIZZLE x0))"
		| "admininstr_instr (instr_sc3 (VSHUFFLE x0 x1)) = (admininstr_sc3 (admininstr_st3_VSHUFFLE x0 x1))"
		| "admininstr_instr (instr_sc3 (VSPLAT x0)) = (admininstr_sc3 (admininstr_st3_VSPLAT x0))"
		| "admininstr_instr (instr_sc3 (VEXTRACT_LANE x0 x1 x2)) = (admininstr_sc3 (admininstr_st3_VEXTRACT_LANE x0 x1 x2))"
		| "admininstr_instr (instr_sc3 (VREPLACE_LANE x0 x1)) = (admininstr_sc3 (admininstr_st3_VREPLACE_LANE x0 x1))"
		| "admininstr_instr (instr_sc3 (VEXTUNOP x0 x1 x2)) = (admininstr_sc4 (admininstr_st4_VEXTUNOP x0 x1 x2))"
		| "admininstr_instr (instr_sc3 (VEXTBINOP x0 x1 x2)) = (admininstr_sc4 (admininstr_st4_VEXTBINOP x0 x1 x2))"
		| "admininstr_instr (instr_sc3 (VNARROW x0 x1 x2)) = (admininstr_sc4 (admininstr_st4_VNARROW x0 x1 x2))"
		| "admininstr_instr (instr_sc4 (VCVTOP x0 x1 x2)) = (admininstr_sc4 (admininstr_st4_VCVTOP x0 x1 x2))"
		| "admininstr_instr (instr_sc4 (REF_NULL x0)) = (admininstr_sc4 (admininstr_st4_REF_NULL x0))"
		| "admininstr_instr (instr_sc4 (REF_FUNC x0)) = (admininstr_sc4 (admininstr_st4_REF_FUNC x0))"
		| "admininstr_instr (instr_sc4 REF_IS_NULL) = (admininstr_sc4 admininstr_st4_REF_IS_NULL)"
		| "admininstr_instr (instr_sc4 (LOCAL_GET x0)) = (admininstr_sc4 (admininstr_st4_LOCAL_GET x0))"
		| "admininstr_instr (instr_sc4 (LOCAL_SET x0)) = (admininstr_sc4 (admininstr_st4_LOCAL_SET x0))"
		| "admininstr_instr (instr_sc4 (LOCAL_TEE x0)) = (admininstr_sc5 (admininstr_st5_LOCAL_TEE x0))"
		| "admininstr_instr (instr_sc4 (GLOBAL_GET x0)) = (admininstr_sc5 (admininstr_st5_GLOBAL_GET x0))"
		| "admininstr_instr (instr_sc4 (GLOBAL_SET x0)) = (admininstr_sc5 (admininstr_st5_GLOBAL_SET x0))"
		| "admininstr_instr (instr_sc5 (TABLE_GET x0)) = (admininstr_sc5 (admininstr_st5_TABLE_GET x0))"
		| "admininstr_instr (instr_sc5 (TABLE_SET x0)) = (admininstr_sc5 (admininstr_st5_TABLE_SET x0))"
		| "admininstr_instr (instr_sc5 (TABLE_SIZE x0)) = (admininstr_sc5 (admininstr_st5_TABLE_SIZE x0))"
		| "admininstr_instr (instr_sc5 (TABLE_GROW x0)) = (admininstr_sc5 (admininstr_st5_TABLE_GROW x0))"
		| "admininstr_instr (instr_sc5 (TABLE_FILL x0)) = (admininstr_sc5 (admininstr_st5_TABLE_FILL x0))"
		| "admininstr_instr (instr_sc5 (TABLE_COPY x0 x1)) = (admininstr_sc5 (admininstr_st5_TABLE_COPY x0 x1))"
		| "admininstr_instr (instr_sc5 (TABLE_INIT x0 x1)) = (admininstr_sc6 (admininstr_st6_TABLE_INIT x0 x1))"
		| "admininstr_instr (instr_sc5 (ELEM_DROP x0)) = (admininstr_sc6 (admininstr_st6_ELEM_DROP x0))"
		| "admininstr_instr (instr_sc5 (LOAD x0 x1 x2)) = (admininstr_sc6 (admininstr_st6_LOAD x0 x1 x2))"
		| "admininstr_instr (instr_sc6 (STORE x0 x1 x2)) = (admininstr_sc6 (admininstr_st6_STORE x0 x1 x2))"
		| "admininstr_instr (instr_sc6 (VLOAD x0 x1 x2)) = (admininstr_sc6 (admininstr_st6_VLOAD x0 x1 x2))"
		| "admininstr_instr (instr_sc6 (VLOAD_LANE x0 x1 x2 x3)) = (admininstr_sc6 (admininstr_st6_VLOAD_LANE x0 x1 x2 x3))"
		| "admininstr_instr (instr_sc6 (VSTORE x0 x1)) = (admininstr_sc6 (admininstr_st6_VSTORE x0 x1))"
		| "admininstr_instr (instr_sc6 (VSTORE_LANE x0 x1 x2 x3)) = (admininstr_sc6 (admininstr_st6_VSTORE_LANE x0 x1 x2 x3))"
		| "admininstr_instr (instr_sc6 MEMORY_SIZE) = (admininstr_sc6 admininstr_st6_MEMORY_SIZE)"
		| "admininstr_instr (instr_sc6 MEMORY_GROW) = (admininstr_sc7 admininstr_st7_MEMORY_GROW)"
		| "admininstr_instr (instr_sc6 MEMORY_FILL) = (admininstr_sc7 admininstr_st7_MEMORY_FILL)"
		| "admininstr_instr (instr_sc6 MEMORY_COPY) = (admininstr_sc7 admininstr_st7_MEMORY_COPY)"
		| "admininstr_instr (instr_sc7 (MEMORY_INIT x0)) = (admininstr_sc7 (admininstr_st7_MEMORY_INIT x0))"
		| "admininstr_instr (instr_sc7 (DATA_DROP x0)) = (admininstr_sc7 (admininstr_st7_DATA_DROP x0))"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) admininstr_ref :: "ref ⇒ admininstr" where
		  "admininstr_ref (ref_REF_NULL x0) = (admininstr_sc4 (admininstr_st4_REF_NULL x0))"
		| "admininstr_ref (REF_FUNC_ADDR x0) = (admininstr_sc7 (admininstr_st7_REF_FUNC_ADDR x0))"
		| "admininstr_ref (REF_HOST_ADDR x0) = (admininstr_sc7 (admininstr_st7_REF_HOST_ADDR x0))"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) admininstr_val :: "val ⇒ admininstr" where
		  "admininstr_val (val_CONST x0 x1) = (admininstr_sc1 (admininstr_st1_CONST x0 x1))"
		| "admininstr_val (val_VCONST x0 x1) = (admininstr_sc2 (admininstr_st2_VCONST x0 x1))"
		| "admininstr_val (val_REF_NULL x0) = (admininstr_sc4 (admininstr_st4_REF_NULL x0))"
		| "admininstr_val (val_REF_FUNC_ADDR x0) = (admininstr_sc7 (admininstr_st7_REF_FUNC_ADDR x0))"
		| "admininstr_val (val_REF_HOST_ADDR x0) = (admininstr_sc7 (admininstr_st7_REF_HOST_ADDR x0))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
inductive wf_admininstr :: "admininstr ⇒ bool" where
	  admininstr_case_0 :
		"wf_admininstr (admininstr_sc0 admininstr_st0_NOP)"
	| admininstr_case_1 :
		"wf_admininstr (admininstr_sc0 admininstr_st0_UNREACHABLE)"
	| admininstr_case_2 :
		"wf_admininstr (admininstr_sc0 admininstr_st0_DROP)"
	| admininstr_case_3 :
		"wf_admininstr (admininstr_sc0 (admininstr_st0_SELECT valtype_lst_opt))"
	| admininstr_case_4 :
		"(wf_blocktype v_blocktype) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_admininstr (admininstr_sc0 (admininstr_st0_BLOCK v_blocktype instr_lst))"
	| admininstr_case_5 :
		"(wf_blocktype v_blocktype) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_admininstr (admininstr_sc0 (admininstr_st0_LOOP v_blocktype instr_lst))"
	| admininstr_case_6 :
		"(wf_blocktype v_blocktype) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 list_all (λ (instr_lst_0 :: instr). (wf_instr instr_lst_0)) instr_lst_0 ⟹
		 wf_admininstr (admininstr_sc0 (admininstr_st0_IFELSE v_blocktype instr_lst instr_lst_0))"
	| admininstr_case_7 :
		"(wf_uN 32 v_labelidx) ⟹
		 wf_admininstr (admininstr_sc0 (admininstr_st0_BR v_labelidx))"
	| admininstr_case_8 :
		"(wf_uN 32 v_labelidx) ⟹
		 wf_admininstr (admininstr_sc0 (admininstr_st0_BR_IF v_labelidx))"
	| admininstr_case_9 :
		"list_all (λ (v_labelidx :: labelidx). (wf_uN 32 v_labelidx)) labelidx_lst ⟹
		 (wf_uN 32 v_labelidx) ⟹
		 wf_admininstr (admininstr_sc1 (admininstr_st1_BR_TABLE labelidx_lst v_labelidx))"
	| admininstr_case_10 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_admininstr (admininstr_sc1 (admininstr_st1_CALL v_funcidx))"
	| admininstr_case_11 :
		"(wf_uN 32 v_tableidx) ⟹
		 (wf_uN 32 v_typeidx) ⟹
		 wf_admininstr (admininstr_sc1 (admininstr_st1_CALL_INDIRECT v_tableidx v_typeidx))"
	| admininstr_case_12 :
		"wf_admininstr (admininstr_sc1 admininstr_st1_RETURN)"
	| admininstr_case_13 :
		"(wf_num_underscore v_numtype var_0) ⟹
		 wf_admininstr (admininstr_sc1 (admininstr_st1_CONST v_numtype var_0))"
	| admininstr_case_14 :
		"(wf_unop_underscore v_numtype var_0) ⟹
		 wf_admininstr (admininstr_sc1 (admininstr_st1_UNOP v_numtype var_0))"
	| admininstr_case_15 :
		"(wf_binop_underscore v_numtype var_0) ⟹
		 wf_admininstr (admininstr_sc1 (admininstr_st1_BINOP v_numtype var_0))"
	| admininstr_case_16 :
		"(wf_testop_underscore v_numtype var_0) ⟹
		 wf_admininstr (admininstr_sc1 (admininstr_st1_TESTOP v_numtype var_0))"
	| admininstr_case_17 :
		"(wf_relop_underscore v_numtype var_0) ⟹
		 wf_admininstr (admininstr_sc1 (admininstr_st1_RELOP v_numtype var_0))"
	| admininstr_case_18 :
		"(numtype_1 ≠ numtype_2) ⟹
		 wf_admininstr (admininstr_sc2 (admininstr_st2_CVTOP numtype_1 numtype_2 v_cvtop))"
	| admininstr_case_19 :
		"wf_admininstr (admininstr_sc2 (admininstr_st2_EXTEND v_numtype v_n))"
	| admininstr_case_20 :
		"((size (valtype_vectype v_vectype)) ≠ None) ⟹
		 (wf_uN (the ((size (valtype_vectype v_vectype)))) var_0) ⟹
		 wf_admininstr (admininstr_sc2 (admininstr_st2_VCONST v_vectype var_0))"
	| admininstr_case_21 :
		"wf_admininstr (admininstr_sc2 (admininstr_st2_VVUNOP v_vectype v_vvunop))"
	| admininstr_case_22 :
		"wf_admininstr (admininstr_sc2 (admininstr_st2_VVBINOP v_vectype v_vvbinop))"
	| admininstr_case_23 :
		"wf_admininstr (admininstr_sc2 (admininstr_st2_VVTERNOP v_vectype v_vvternop))"
	| admininstr_case_24 :
		"wf_admininstr (admininstr_sc2 (admininstr_st2_VVTESTOP v_vectype v_vvtestop))"
	| admininstr_case_25 :
		"(wf_shape v_shape) ⟹
		 (wf_vunop_underscore v_shape var_0) ⟹
		 wf_admininstr (admininstr_sc2 (admininstr_st2_VUNOP v_shape var_0))"
	| admininstr_case_26 :
		"(wf_shape v_shape) ⟹
		 (wf_vbinop_underscore v_shape var_0) ⟹
		 wf_admininstr (admininstr_sc2 (admininstr_st2_VBINOP v_shape var_0))"
	| admininstr_case_27 :
		"(wf_shape v_shape) ⟹
		 (wf_vtestop_underscore v_shape var_0) ⟹
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VTESTOP v_shape var_0))"
	| admininstr_case_28 :
		"(wf_shape v_shape) ⟹
		 (wf_vrelop_underscore v_shape var_0) ⟹
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VRELOP v_shape var_0))"
	| admininstr_case_29 :
		"(wf_ishape v_ishape) ⟹
		 (wf_vshiftop_underscore v_ishape var_0) ⟹
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VSHIFTOP v_ishape var_0))"
	| admininstr_case_30 :
		"(wf_ishape v_ishape) ⟹
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VBITMASK v_ishape))"
	| admininstr_case_31 :
		"(wf_ishape v_ishape) ⟹
		 (v_ishape = (ishape_X Jnn_I8 (mk_dim 16))) ⟹
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VSWIZZLE v_ishape))"
	| admininstr_case_32 :
		"(wf_ishape v_ishape) ⟹
		 list_all (λ (v_laneidx :: laneidx). (wf_uN 8 v_laneidx)) laneidx_lst ⟹
		 ((v_ishape = (ishape_X Jnn_I8 (mk_dim 16))) ∧ ((length laneidx_lst) = 16)) ⟹
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VSHUFFLE v_ishape laneidx_lst))"
	| admininstr_case_33 :
		"(wf_shape v_shape) ⟹
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VSPLAT v_shape))"
	| admininstr_case_34 :
		"(wf_shape v_shape) ⟹
		 (wf_uN 8 v_laneidx) ⟹
		 (((fun_lanetype v_shape) = (lanetype_numtype v_numtype)) ⟷ (sx_opt = None)) ⟹
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VEXTRACT_LANE v_shape sx_opt v_laneidx))"
	| admininstr_case_35 :
		"(wf_shape v_shape) ⟹
		 (wf_uN 8 v_laneidx) ⟹
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VREPLACE_LANE v_shape v_laneidx))"
	| admininstr_case_36 :
		"(wf_ishape ishape_1) ⟹
		 (wf_ishape ishape_2) ⟹
		 (wf_vextunop_underscore ishape_1 var_0) ⟹
		 ((lsize (fun_lanetype (shape_ishape ishape_1))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))) ⟹
		 wf_admininstr (admininstr_sc4 (admininstr_st4_VEXTUNOP ishape_1 ishape_2 var_0))"
	| admininstr_case_37 :
		"(wf_ishape ishape_1) ⟹
		 (wf_ishape ishape_2) ⟹
		 (wf_vextbinop_underscore ishape_1 var_0) ⟹
		 ((lsize (fun_lanetype (shape_ishape ishape_1))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))) ⟹
		 wf_admininstr (admininstr_sc4 (admininstr_st4_VEXTBINOP ishape_1 ishape_2 var_0))"
	| admininstr_case_38 :
		"(wf_ishape ishape_1) ⟹
		 (wf_ishape ishape_2) ⟹
		 (((lsize (fun_lanetype (shape_ishape ishape_2))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_1))))) ∧ ((2 * (lsize (fun_lanetype (shape_ishape ishape_1)))) ≤ 32)) ⟹
		 wf_admininstr (admininstr_sc4 (admininstr_st4_VNARROW ishape_1 ishape_2 v_sx))"
	| admininstr_case_39 :
		"(wf_shape v_shape) ⟹
		 (wf_shape shape_0) ⟹
		 wf_admininstr (admininstr_sc4 (admininstr_st4_VCVTOP v_shape shape_0 v_vcvtop))"
	| admininstr_case_40 :
		"wf_admininstr (admininstr_sc4 (admininstr_st4_REF_NULL v_reftype))"
	| admininstr_case_41 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_admininstr (admininstr_sc4 (admininstr_st4_REF_FUNC v_funcidx))"
	| admininstr_case_42 :
		"wf_admininstr (admininstr_sc4 admininstr_st4_REF_IS_NULL)"
	| admininstr_case_43 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_admininstr (admininstr_sc4 (admininstr_st4_LOCAL_GET v_localidx))"
	| admininstr_case_44 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_admininstr (admininstr_sc4 (admininstr_st4_LOCAL_SET v_localidx))"
	| admininstr_case_45 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_admininstr (admininstr_sc5 (admininstr_st5_LOCAL_TEE v_localidx))"
	| admininstr_case_46 :
		"(wf_uN 32 v_globalidx) ⟹
		 wf_admininstr (admininstr_sc5 (admininstr_st5_GLOBAL_GET v_globalidx))"
	| admininstr_case_47 :
		"(wf_uN 32 v_globalidx) ⟹
		 wf_admininstr (admininstr_sc5 (admininstr_st5_GLOBAL_SET v_globalidx))"
	| admininstr_case_48 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_admininstr (admininstr_sc5 (admininstr_st5_TABLE_GET v_tableidx))"
	| admininstr_case_49 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_admininstr (admininstr_sc5 (admininstr_st5_TABLE_SET v_tableidx))"
	| admininstr_case_50 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_admininstr (admininstr_sc5 (admininstr_st5_TABLE_SIZE v_tableidx))"
	| admininstr_case_51 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_admininstr (admininstr_sc5 (admininstr_st5_TABLE_GROW v_tableidx))"
	| admininstr_case_52 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_admininstr (admininstr_sc5 (admininstr_st5_TABLE_FILL v_tableidx))"
	| admininstr_case_53 :
		"(wf_uN 32 v_tableidx) ⟹
		 (wf_uN 32 tableidx_0) ⟹
		 wf_admininstr (admininstr_sc5 (admininstr_st5_TABLE_COPY v_tableidx tableidx_0))"
	| admininstr_case_54 :
		"(wf_uN 32 v_tableidx) ⟹
		 (wf_uN 32 v_elemidx) ⟹
		 wf_admininstr (admininstr_sc6 (admininstr_st6_TABLE_INIT v_tableidx v_elemidx))"
	| admininstr_case_55 :
		"(wf_uN 32 v_elemidx) ⟹
		 wf_admininstr (admininstr_sc6 (admininstr_st6_ELEM_DROP v_elemidx))"
	| admininstr_case_56 :
		"list_all (λ (var_0 :: loadop_underscore). (wf_loadop_underscore v_numtype var_0)) (option_to_list var_0) ⟹
		 (wf_memarg v_memarg) ⟹
		 wf_admininstr (admininstr_sc6 (admininstr_st6_LOAD v_numtype var_0 v_memarg))"
	| admininstr_case_57 :
		"list_all (λ (v_sz :: sz). (wf_sz v_sz)) (option_to_list sz_opt) ⟹
		 (wf_memarg v_memarg) ⟹
		 ((Inn_opt = None) ⟷ (numtype_opt = None)) ⟹
		 ((Inn_opt = None) ⟷ (sz_opt = None)) ⟹
		 list_all3 (λ (v_Inn :: Inn) (v_numtype :: numtype) (v_sz :: sz). ((v_numtype = (numtype_Inn v_Inn)) ∧ ((proj_sz_0 v_sz) < (sizenn (numtype_Inn v_Inn))))) (option_to_list Inn_opt) (option_to_list numtype_opt) (option_to_list sz_opt) ⟹
		 wf_admininstr (admininstr_sc6 (admininstr_st6_STORE v_numtype sz_opt v_memarg))"
	| admininstr_case_58 :
		"(wf_memarg v_memarg) ⟹
		 wf_admininstr (admininstr_sc6 (admininstr_st6_VLOAD v_vectype vloadop_opt v_memarg))"
	| admininstr_case_59 :
		"(wf_sz v_sz) ⟹
		 (wf_memarg v_memarg) ⟹
		 (wf_uN 8 v_laneidx) ⟹
		 wf_admininstr (admininstr_sc6 (admininstr_st6_VLOAD_LANE v_vectype v_sz v_memarg v_laneidx))"
	| admininstr_case_60 :
		"(wf_memarg v_memarg) ⟹
		 wf_admininstr (admininstr_sc6 (admininstr_st6_VSTORE v_vectype v_memarg))"
	| admininstr_case_61 :
		"(wf_sz v_sz) ⟹
		 (wf_memarg v_memarg) ⟹
		 (wf_uN 8 v_laneidx) ⟹
		 wf_admininstr (admininstr_sc6 (admininstr_st6_VSTORE_LANE v_vectype v_sz v_memarg v_laneidx))"
	| admininstr_case_62 :
		"wf_admininstr (admininstr_sc6 admininstr_st6_MEMORY_SIZE)"
	| admininstr_case_63 :
		"wf_admininstr (admininstr_sc7 admininstr_st7_MEMORY_GROW)"
	| admininstr_case_64 :
		"wf_admininstr (admininstr_sc7 admininstr_st7_MEMORY_FILL)"
	| admininstr_case_65 :
		"wf_admininstr (admininstr_sc7 admininstr_st7_MEMORY_COPY)"
	| admininstr_case_66 :
		"(wf_uN 32 v_dataidx) ⟹
		 wf_admininstr (admininstr_sc7 (admininstr_st7_MEMORY_INIT v_dataidx))"
	| admininstr_case_67 :
		"(wf_uN 32 v_dataidx) ⟹
		 wf_admininstr (admininstr_sc7 (admininstr_st7_DATA_DROP v_dataidx))"
	| admininstr_case_68 :
		"wf_admininstr (admininstr_sc7 (admininstr_st7_REF_FUNC_ADDR v_funcaddr))"
	| admininstr_case_69 :
		"wf_admininstr (admininstr_sc7 (admininstr_st7_REF_HOST_ADDR v_hostaddr))"
	| admininstr_case_70 :
		"wf_admininstr (admininstr_sc7 (CALL_ADDR v_funcaddr))"
	| admininstr_case_71 :
		"list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 list_all (λ (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst ⟹
		 wf_admininstr (admininstr_sc8 (LABEL_underscore v_n instr_lst admininstr_lst))"
	| admininstr_case_72 :
		"(wf_frame v_frame) ⟹
		 list_all (λ (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst ⟹
		 wf_admininstr (admininstr_sc8 (FRAME_underscore v_n v_frame admininstr_lst))"
	| admininstr_case_73 :
		"wf_admininstr (admininstr_sc7 admininstr_st7_TRAP)"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:117.1-117.62 *)
datatype config =
	  mk_config "state" "(admininstr list)"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:117.8-117.14 *)
inductive wf_config :: "config ⇒ bool" where
	  config_case_0 :
		"(wf_state v_state) ⟹
		 list_all (λ (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst ⟹
		 wf_config (mk_config v_state admininstr_lst)"

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:7.1-7.43 *)
function (sequential) default_underscore :: "valtype ⇒ (val option)" where
		  "default_underscore valtype_I32 = (Some (val_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))))"
		| "default_underscore valtype_I64 = (Some (val_CONST I64 (mk_num__0 Inn_I64 (mk_uN 0))))"
		| "default_underscore valtype_F32 = (Some (val_CONST F32 (mk_num__1 Fnn_F32 (fzero (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))))))))))))))))))))))))))"
		| "default_underscore valtype_F64 = (Some (val_CONST F64 (mk_num__1 Fnn_F64 (fzero (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))"
		| "default_underscore valtype_V128 = (Some (val_VCONST V128 (mk_uN 0)))"
		| "default_underscore valtype_FUNCREF = (Some (val_REF_NULL FUNCREF))"
		| "default_underscore valtype_EXTERNREF = (Some (val_REF_NULL EXTERNREF))"
		| "default_underscore x0 = None"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:20.1-20.63 *)
inductive fun_funcsxa :: "(externaddr list) ⇒ (funcaddr list) ⇒ bool" where
	  fun_funcsxa_case_0 :
		"fun_funcsxa [] []"
	| fun_funcsxa_case_1 :
		"(fun_funcsxa xv_lst var_0) ⟹
		 fun_funcsxa ([(externaddr_FUNC fa)] @ xv_lst) ([fa] @ var_0)"
	| fun_funcsxa_case_2 :
		"(fun_funcsxa xv_lst var_0) ⟹
		 fun_funcsxa ([v_externaddr] @ xv_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:21.1-21.65 *)
inductive fun_globalsxa :: "(externaddr list) ⇒ (globaladdr list) ⇒ bool" where
	  fun_globalsxa_case_0 :
		"fun_globalsxa [] []"
	| fun_globalsxa_case_1 :
		"(fun_globalsxa xv_lst var_0) ⟹
		 fun_globalsxa ([(externaddr_GLOBAL ga)] @ xv_lst) ([ga] @ var_0)"
	| fun_globalsxa_case_2 :
		"(fun_globalsxa xv_lst var_0) ⟹
		 fun_globalsxa ([v_externaddr] @ xv_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:22.1-22.64 *)
inductive fun_tablesxa :: "(externaddr list) ⇒ (tableaddr list) ⇒ bool" where
	  fun_tablesxa_case_0 :
		"fun_tablesxa [] []"
	| fun_tablesxa_case_1 :
		"(fun_tablesxa xv_lst var_0) ⟹
		 fun_tablesxa ([(externaddr_TABLE ta)] @ xv_lst) ([ta] @ var_0)"
	| fun_tablesxa_case_2 :
		"(fun_tablesxa xv_lst var_0) ⟹
		 fun_tablesxa ([v_externaddr] @ xv_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:23.1-23.62 *)
inductive fun_memsxa :: "(externaddr list) ⇒ (memaddr list) ⇒ bool" where
	  fun_memsxa_case_0 :
		"fun_memsxa [] []"
	| fun_memsxa_case_1 :
		"(fun_memsxa xv_lst var_0) ⟹
		 fun_memsxa ([(externaddr_MEM ma)] @ xv_lst) ([ma] @ var_0)"
	| fun_memsxa_case_2 :
		"(fun_memsxa xv_lst var_0) ⟹
		 fun_memsxa ([v_externaddr] @ xv_lst) var_0"

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:48.1-48.57 *)
function (sequential) fun_store :: "state ⇒ store" where
		  "fun_store (mk_state s f) = s"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:49.1-49.57 *)
function (sequential) fun_frame :: "state ⇒ frame" where
		  "fun_frame (mk_state s f) = f"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:55.1-55.64 *)
function (sequential) fun_funcaddr :: "state ⇒ (funcaddr list)" where
		  "fun_funcaddr (mk_state s f) = (FUNCS (frame_MODULE f))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:58.1-58.57 *)
function (sequential) fun_funcinst :: "state ⇒ (funcinst list)" where
		  "fun_funcinst (mk_state s f) = (store_FUNCS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:59.1-59.59 *)
function (sequential) fun_globalinst :: "state ⇒ (globalinst list)" where
		  "fun_globalinst (mk_state s f) = (store_GLOBALS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:60.1-60.58 *)
function (sequential) fun_tableinst :: "state ⇒ (tableinst list)" where
		  "fun_tableinst (mk_state s f) = (store_TABLES s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:61.1-61.56 *)
function (sequential) fun_meminst :: "state ⇒ (meminst list)" where
		  "fun_meminst (mk_state s f) = (store_MEMS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:62.1-62.57 *)
function (sequential) fun_eleminst :: "state ⇒ (eleminst list)" where
		  "fun_eleminst (mk_state s f) = (store_ELEMS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:63.1-63.57 *)
function (sequential) fun_datainst :: "state ⇒ (datainst list)" where
		  "fun_datainst (mk_state s f) = (store_DATAS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:64.1-64.58 *)
function (sequential) fun_moduleinst :: "state ⇒ moduleinst" where
		  "fun_moduleinst (mk_state s f) = (frame_MODULE f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:74.1-74.66 *)
function (sequential) fun_type :: "state ⇒ typeidx ⇒ functype" where
		  "fun_type (mk_state s f) x = ((TYPES (frame_MODULE f)) ! (proj_uN_0 x))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:75.1-75.66 *)
function (sequential) fun_func :: "state ⇒ funcidx ⇒ funcinst" where
		  "fun_func (mk_state s f) x = ((store_FUNCS s) ! ((FUNCS (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:76.1-76.68 *)
function (sequential) fun_global :: "state ⇒ globalidx ⇒ globalinst" where
		  "fun_global (mk_state s f) x = ((store_GLOBALS s) ! ((GLOBALS (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:77.1-77.67 *)
function (sequential) fun_table :: "state ⇒ tableidx ⇒ tableinst" where
		  "fun_table (mk_state s f) x = ((store_TABLES s) ! ((TABLES (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.1-78.65 *)
function (sequential) fun_mem :: "state ⇒ memidx ⇒ meminst" where
		  "fun_mem (mk_state s f) x = ((store_MEMS s) ! ((MEMS (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:79.1-79.66 *)
function (sequential) fun_elem :: "state ⇒ tableidx ⇒ eleminst" where
		  "fun_elem (mk_state s f) x = ((store_ELEMS s) ! ((ELEMS (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:80.1-80.66 *)
function (sequential) fun_data :: "state ⇒ dataidx ⇒ datainst" where
		  "fun_data (mk_state s f) x = ((store_DATAS s) ! ((DATAS (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:81.1-81.67 *)
function (sequential) fun_local :: "state ⇒ localidx ⇒ val" where
		  "fun_local (mk_state s f) x = ((LOCALS f) ! (proj_uN_0 x))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:95.1-95.89 *)
function (sequential) with_local :: "state ⇒ localidx ⇒ val ⇒ state" where
		  "with_local (mk_state s f) x v = (mk_state s (f ⦇ LOCALS := (list_update_func (LOCALS f) (proj_uN_0 x) (λ (underscore_underscore :: val). v))  ⦈))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:96.1-96.96 *)
function (sequential) with_global :: "state ⇒ globalidx ⇒ val ⇒ state" where
		  "with_global (mk_state s f) x v = (mk_state (s ⦇ store_GLOBALS := (list_update_func (store_GLOBALS s) ((GLOBALS (frame_MODULE f)) ! (proj_uN_0 x)) (λ (var_1 :: globalinst). (var_1 ⦇ VALUE := v  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:97.1-97.97 *)
function (sequential) with_table :: "state ⇒ tableidx ⇒ nat ⇒ ref ⇒ state" where
		  "with_table (mk_state s f) x i r = (mk_state (s ⦇ store_TABLES := (list_update_func (store_TABLES s) ((TABLES (frame_MODULE f)) ! (proj_uN_0 x)) (λ (var_1 :: tableinst). (var_1 ⦇ REFS := (list_update_func (REFS var_1) i (λ (underscore_underscore :: ref). r))  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:98.1-98.89 *)
function (sequential) with_tableinst :: "state ⇒ tableidx ⇒ tableinst ⇒ state" where
		  "with_tableinst (mk_state s f) x ti = (mk_state (s ⦇ store_TABLES := (list_update_func (store_TABLES s) ((TABLES (frame_MODULE f)) ! (proj_uN_0 x)) (λ (underscore_underscore :: tableinst). ti))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:99.1-99.100 *)
function (sequential) with_mem :: "state ⇒ memidx ⇒ nat ⇒ nat ⇒ (byte list) ⇒ state" where
		  "with_mem (mk_state s f) x i j b_lst = (mk_state (s ⦇ store_MEMS := (list_update_func (store_MEMS s) ((MEMS (frame_MODULE f)) ! (proj_uN_0 x)) (λ (var_1 :: meminst). (var_1 ⦇ BYTES := (list_slice_update (BYTES var_1) i j b_lst)  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:100.1-100.87 *)
function (sequential) with_meminst :: "state ⇒ memidx ⇒ meminst ⇒ state" where
		  "with_meminst (mk_state s f) x mi = (mk_state (s ⦇ store_MEMS := (list_update_func (store_MEMS s) ((MEMS (frame_MODULE f)) ! (proj_uN_0 x)) (λ (underscore_underscore :: meminst). mi))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:101.1-101.93 *)
function (sequential) with_elem :: "state ⇒ elemidx ⇒ (ref list) ⇒ state" where
		  "with_elem (mk_state s f) x r_lst = (mk_state (s ⦇ store_ELEMS := (list_update_func (store_ELEMS s) ((ELEMS (frame_MODULE f)) ! (proj_uN_0 x)) (λ (var_1 :: eleminst). (var_1 ⦇ eleminst_REFS := r_lst  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:102.1-102.94 *)
function (sequential) with_data :: "state ⇒ dataidx ⇒ (byte list) ⇒ state" where
		  "with_data (mk_state s f) x b_lst = (mk_state (s ⦇ store_DATAS := (list_update_func (store_DATAS s) ((DATAS (frame_MODULE f)) ! (proj_uN_0 x)) (λ (var_1 :: datainst). (var_1 ⦇ datainst_BYTES := b_lst  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 *)
inductive fun_growtable :: "tableinst ⇒ nat ⇒ ref ⇒ (tableinst option) ⇒ bool" where
	  fun_growtable_case_0 :
		"(wf_tableinst ⦇ tableinst_TYPE = (mk_tabletype (mk_limits i j_opt) rt), REFS = r'_lst ⦈) ⟹
		 (wf_tableinst ⦇ tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN i') j_opt) rt), REFS = (r'_lst @ (repeat v_n r)) ⦈) ⟹
		 (ti = ⦇ tableinst_TYPE = (mk_tabletype (mk_limits i j_opt) rt), REFS = r'_lst ⦈) ⟹
		 (i' = ((length r'_lst) + v_n)) ⟹
		 list_all (λ (j :: u32). (i' ≤ (proj_uN_0 j))) (option_to_list j_opt) ⟹
		 (ti' = ⦇ tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN i') j_opt) rt), REFS = (r'_lst @ (repeat v_n r)) ⦈) ⟹
		 fun_growtable ti v_n r (Some ti')"
	| fun_growtable_case_1 :
		"True ⟹
		 fun_growtable x0 x1 x2 None"

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 *)
inductive fun_growmemory :: "meminst ⇒ nat ⇒ (meminst option) ⇒ bool" where
	  fun_growmemory_case_0 :
		"(wf_meminst ⦇ meminst_TYPE = (PAGE (mk_limits i j_opt)), BYTES = b_lst ⦈) ⟹
		 (wf_meminst ⦇ meminst_TYPE = (PAGE (mk_limits (mk_uN (i' :: nat)) j_opt)), BYTES = (b_lst @ (repeat (v_n * (64 * (Ki ))) (mk_byte 0))) ⦈) ⟹
		 (mi = ⦇ meminst_TYPE = (PAGE (mk_limits i j_opt)), BYTES = b_lst ⦈) ⟹
		 (i' = ((((length b_lst) :: nat) div ((64 * (Ki )) :: nat)) + (v_n :: nat))) ⟹
		 list_all (λ (j :: u32). (i' ≤ ((proj_uN_0 j) :: nat))) (option_to_list j_opt) ⟹
		 (mi' = ⦇ meminst_TYPE = (PAGE (mk_limits (mk_uN (i' :: nat)) j_opt)), BYTES = (b_lst @ (repeat (v_n * (64 * (Ki ))) (mk_byte 0))) ⦈) ⟹
		 fun_growmemory mi v_n (Some mi')"
	| fun_growmemory_case_1 :
		"True ⟹
		 fun_growmemory x0 x1 None"

(* Record Creation Definition at: ../specification/wasm-2.0/6-typing.spectec:5.1-9.62 *)
record res_context =
	context_TYPES :: "(functype list)"
	context_FUNCS :: "(functype list)"
	context_GLOBALS :: "(globaltype list)"
	context_TABLES :: "(tabletype list)"
	context_MEMS :: "(memtype list)"
	context_ELEMS :: "(elemtype list)"
	context_DATAS :: "(res_datatype list)"
	context_LOCALS :: "(valtype list)"
	LABELS :: "(resulttype list)"
	context_RETURN :: "(resulttype option)"

definition append_res_context :: "res_context ⇒ res_context ⇒ res_context" where
	"append_res_context arg1 arg2 = ⦇
		context_TYPES = context_TYPES arg1 @ context_TYPES arg2,
		context_FUNCS = context_FUNCS arg1 @ context_FUNCS arg2,
		context_GLOBALS = context_GLOBALS arg1 @ context_GLOBALS arg2,
		context_TABLES = context_TABLES arg1 @ context_TABLES arg2,
		context_MEMS = context_MEMS arg1 @ context_MEMS arg2,
		context_ELEMS = context_ELEMS arg1 @ context_ELEMS arg2,
		context_DATAS = context_DATAS arg1 @ context_DATAS arg2,
		context_LOCALS = context_LOCALS arg1 @ context_LOCALS arg2,
		LABELS = LABELS arg1 @ LABELS arg2,
		context_RETURN = context_RETURN arg1 @@@ context_RETURN arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:5.8-5.15 *)
inductive wf_context :: "res_context ⇒ bool" where
	  context_case_underscore :
		"list_all (λ (var_3 :: tabletype). (wf_tabletype var_3)) var_3 ⟹
		 list_all (λ (var_4 :: memtype). (wf_memtype var_4)) var_4 ⟹
		 wf_context ⦇ context_TYPES = var_0, context_FUNCS = var_1, context_GLOBALS = var_2, context_TABLES = var_3, context_MEMS = var_4, context_ELEMS = var_5, context_DATAS = var_6, context_LOCALS = var_7, LABELS = var_8, context_RETURN = var_9 ⦈"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:19.1-19.66 *)
inductive Limits_ok :: "limits ⇒ nat ⇒ bool" where
	  mk_Limits_ok :
		"(v_n ≤ k) ⟹
		 list_all (λ (v_m :: nat). ((v_n ≤ v_m) ∧ (v_m ≤ k))) (option_to_list m_opt) ⟹
		 Limits_ok (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)) k"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:20.1-20.64 *)
inductive Functype_ok :: "functype ⇒ bool" where
	  mk_Functype_ok :
		"Functype_ok (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:21.1-21.66 *)
inductive Globaltype_ok :: "globaltype ⇒ bool" where
	  mk_Globaltype_ok :
		"Globaltype_ok (mk_globaltype (Some MUT_MUT) t)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:22.1-22.65 *)
inductive Tabletype_ok :: "tabletype ⇒ bool" where
	  mk_Tabletype_ok :
		"(Limits_ok v_limits ((((2 ^ 32) :: nat) - (1 :: nat)) :: nat)) ⟹
		 Tabletype_ok (mk_tabletype v_limits v_reftype)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:23.1-23.63 *)
inductive Memtype_ok :: "memtype ⇒ bool" where
	  mk_Memtype_ok :
		"(Limits_ok v_limits (2 ^ 16)) ⟹
		 Memtype_ok (PAGE v_limits)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:24.1-24.66 *)
inductive Externtype_ok :: "externtype ⇒ bool" where
	  Externtype_ok__func :
		"(Functype_ok v_functype) ⟹
		 Externtype_ok (FUNC v_functype)"
	| Externtype_ok__global :
		"(Globaltype_ok v_globaltype) ⟹
		 Externtype_ok (GLOBAL v_globaltype)"
	| Externtype_ok__table :
		"(Tabletype_ok v_tabletype) ⟹
		 Externtype_ok (TABLE v_tabletype)"
	| Externtype_ok__mem :
		"(Memtype_ok v_memtype) ⟹
		 Externtype_ok (MEM v_memtype)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:71.1-71.69 *)
inductive Valtype_sub :: "valtype ⇒ valtype ⇒ bool" where
	  refl :
		"Valtype_sub t t"
	| bot :
		"Valtype_sub BOT t"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:72.1-72.76 *)
inductive Resulttype_sub :: "resulttype ⇒ resulttype ⇒ bool" where
	  mk_Resulttype_sub :
		"((length t_1_lst) = (length t_2_lst)) ⟹
		 list_all2 (λ (t_1 :: valtype) (t_2 :: valtype). (Valtype_sub t_1 t_2)) t_1_lst t_2_lst ⟹
		 Resulttype_sub (mk_list t_1_lst) (mk_list t_2_lst)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:87.1-87.75 *)
inductive Limits_sub :: "limits ⇒ limits ⇒ bool" where
	  mk_Limits_sub :
		"(n_11 ≥ n_21) ⟹
		 (n_12 ≤ n_22) ⟹
		 Limits_sub (mk_limits (mk_uN n_11) (Some (mk_uN n_12))) (mk_limits (mk_uN n_21) (Some (mk_uN n_22)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:88.1-88.73 *)
inductive Functype_sub :: "functype ⇒ functype ⇒ bool" where
	  mk_Functype_sub :
		"Functype_sub ft ft"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:89.1-89.75 *)
inductive Globaltype_sub :: "globaltype ⇒ globaltype ⇒ bool" where
	  mk_Globaltype_sub :
		"Globaltype_sub gt gt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:90.1-90.74 *)
inductive Tabletype_sub :: "tabletype ⇒ tabletype ⇒ bool" where
	  mk_Tabletype_sub :
		"(Limits_sub lim_1 lim_2) ⟹
		 Tabletype_sub (mk_tabletype lim_1 rt) (mk_tabletype lim_2 rt)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:91.1-91.72 *)
inductive Memtype_sub :: "memtype ⇒ memtype ⇒ bool" where
	  mk_Memtype_sub :
		"(Limits_sub lim_1 lim_2) ⟹
		 Memtype_sub (PAGE lim_1) (PAGE lim_2)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:92.1-92.75 *)
inductive Externtype_sub :: "externtype ⇒ externtype ⇒ bool" where
	  Externtype_sub__func :
		"(Functype_sub ft_1 ft_2) ⟹
		 Externtype_sub (FUNC ft_1) (FUNC ft_2)"
	| Externtype_sub__global :
		"(Globaltype_sub gt_1 gt_2) ⟹
		 Externtype_sub (GLOBAL gt_1) (GLOBAL gt_2)"
	| Externtype_sub__table :
		"(Tabletype_sub tt_1 tt_2) ⟹
		 Externtype_sub (TABLE tt_1) (TABLE tt_2)"
	| Externtype_sub__mem :
		"(Memtype_sub mt_1 mt_2) ⟹
		 Externtype_sub (MEM mt_1) (MEM mt_2)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:198.1-198.76 *)
inductive Blocktype_ok :: "res_context ⇒ blocktype ⇒ functype ⇒ bool" where
	  Blocktype_ok__valtype :
		"Blocktype_ok C (underscore_RESULT valtype_opt) (mk_functype (mk_list []) (mk_list (option_to_list valtype_opt)))"
	| Blocktype_ok__typeidx :
		"((proj_uN_0 v_typeidx) < (length (context_TYPES C))) ⟹
		 (((context_TYPES C) ! (proj_uN_0 v_typeidx)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Blocktype_ok C (underscore_IDX v_typeidx) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"

(* Mutual Recursion at: ../specification/wasm-2.0/6-typing.spectec:137.1-138.65 *)
inductive Instr_ok :: "res_context ⇒ instr ⇒ functype ⇒ bool"
and Instrs_ok :: "res_context ⇒ (instr list) ⇒ functype ⇒ bool" where
	  nop :
		"Instr_ok C (instr_sc0 NOP) (mk_functype (mk_list []) (mk_list []))"
	| unreachable :
		"Instr_ok C (instr_sc0 UNREACHABLE) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
	| drop :
		"Instr_ok C (instr_sc0 DROP) (mk_functype (mk_list [t]) (mk_list []))"
	| select_expl :
		"Instr_ok C (instr_sc0 (SELECT (Some [t]))) (mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t]))"
	| select_impl :
		"(Valtype_sub t t') ⟹
		 ((t' = (valtype_numtype v_numtype)) ∨ (t' = (valtype_vectype v_vectype))) ⟹
		 Instr_ok C (instr_sc0 (SELECT None)) (mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t]))"
	| block :
		"(wf_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None ⦈) ⟹
		 (Blocktype_ok C bt (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (Instrs_ok (append_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None ⦈ C) instr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc7 (BLOCK bt instr_lst)) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
	| loop :
		"(wf_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_1_lst)], context_RETURN = None ⦈) ⟹
		 (Blocktype_ok C bt (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (Instrs_ok (append_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_1_lst)], context_RETURN = None ⦈ C) instr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc7 (LOOP bt instr_lst)) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
	| res_if :
		"(wf_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None ⦈) ⟹
		 (Blocktype_ok C bt (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (Instrs_ok (append_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None ⦈ C) instr_1_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (Instrs_ok (append_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None ⦈ C) instr_2_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc7 (IFELSE bt instr_1_lst instr_2_lst)) (mk_functype (mk_list (t_1_lst @ [valtype_I32])) (mk_list t_2_lst))"
	| br :
		"((proj_uN_0 l) < (length (LABELS C))) ⟹
		 ((proj_list_0  ((LABELS C) ! (proj_uN_0 l))) = t_lst) ⟹
		 Instr_ok C (instr_sc0 (BR l)) (mk_functype (mk_list (t_1_lst @ t_lst)) (mk_list t_2_lst))"
	| br_if :
		"((proj_uN_0 l) < (length (LABELS C))) ⟹
		 ((proj_list_0  ((LABELS C) ! (proj_uN_0 l))) = t_lst) ⟹
		 Instr_ok C (instr_sc0 (BR_IF l)) (mk_functype (mk_list (t_lst @ [valtype_I32])) (mk_list t_lst))"
	| br_table :
		"list_all (λ (l :: labelidx). ((proj_uN_0 l) < (length (LABELS C)))) l_lst ⟹
		 list_all (λ (l :: labelidx). (Resulttype_sub (mk_list t_lst) ((LABELS C) ! (proj_uN_0 l)))) l_lst ⟹
		 ((proj_uN_0 l') < (length (LABELS C))) ⟹
		 (Resulttype_sub (mk_list t_lst) ((LABELS C) ! (proj_uN_0 l'))) ⟹
		 Instr_ok C (instr_sc0 (BR_TABLE l_lst l')) (mk_functype (mk_list (t_1_lst @ (t_lst @ [valtype_I32]))) (mk_list t_2_lst))"
	| call :
		"((proj_uN_0 x) < (length (context_FUNCS C))) ⟹
		 (((context_FUNCS C) ! (proj_uN_0 x)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc0 (CALL x)) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
	| call_indirect :
		"(wf_tabletype (mk_tabletype lim FUNCREF)) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim FUNCREF)) ⟹
		 ((proj_uN_0 y) < (length (context_TYPES C))) ⟹
		 (((context_TYPES C) ! (proj_uN_0 y)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Instr_ok C (instr_sc0 (CALL_INDIRECT x y)) (mk_functype (mk_list (t_1_lst @ [valtype_I32])) (mk_list t_2_lst))"
	| return :
		"((context_RETURN C) = (Some (mk_list t_lst))) ⟹
		 Instr_ok C (instr_sc1 RETURN) (mk_functype (mk_list (t_1_lst @ t_lst)) (mk_list t_2_lst))"
	| const :
		"Instr_ok C (instr_sc1 (res_CONST nt c_nt)) (mk_functype (mk_list []) (mk_list [(valtype_numtype nt)]))"
	| unop :
		"Instr_ok C (instr_sc1 (UNOP nt unop_nt)) (mk_functype (mk_list [(valtype_numtype nt)]) (mk_list [(valtype_numtype nt)]))"
	| binop :
		"Instr_ok C (instr_sc1 (BINOP nt binop_nt)) (mk_functype (mk_list [(valtype_numtype nt), (valtype_numtype nt)]) (mk_list [(valtype_numtype nt)]))"
	| testop :
		"Instr_ok C (instr_sc1 (TESTOP nt testop_nt)) (mk_functype (mk_list [(valtype_numtype nt)]) (mk_list [valtype_I32]))"
	| relop :
		"Instr_ok C (instr_sc1 (RELOP nt relop_nt)) (mk_functype (mk_list [(valtype_numtype nt), (valtype_numtype nt)]) (mk_list [valtype_I32]))"
	| cvtop_reinterpret :
		"((size (valtype_numtype nt_1)) ≠ None) ⟹
		 ((size (valtype_numtype nt_2)) ≠ None) ⟹
		 ((the ((size (valtype_numtype nt_1)))) = (the ((size (valtype_numtype nt_2))))) ⟹
		 Instr_ok C (instr_sc1 (CVTOP nt_1 nt_2 REINTERPRET)) (mk_functype (mk_list [(valtype_numtype nt_2)]) (mk_list [(valtype_numtype nt_1)]))"
	| cvtop_convert :
		"Instr_ok C (instr_sc1 (CVTOP nt_1 nt_2 v_cvtop)) (mk_functype (mk_list [(valtype_numtype nt_2)]) (mk_list [(valtype_numtype nt_1)]))"
	| ref_null :
		"Instr_ok C (instr_sc4 (REF_NULL rt)) (mk_functype (mk_list []) (mk_list [(valtype_reftype rt)]))"
	| ref_func :
		"((proj_uN_0 x) < (length (context_FUNCS C))) ⟹
		 (((context_FUNCS C) ! (proj_uN_0 x)) = ft) ⟹
		 Instr_ok C (instr_sc4 (REF_FUNC x)) (mk_functype (mk_list []) (mk_list [valtype_FUNCREF]))"
	| ref_is_null :
		"Instr_ok C (instr_sc4 REF_IS_NULL) (mk_functype (mk_list [(valtype_reftype rt)]) (mk_list [valtype_I32]))"
	| vconst :
		"Instr_ok C (instr_sc1 (VCONST V128 c)) (mk_functype (mk_list []) (mk_list [valtype_V128]))"
	| Instr_ok__vvunop :
		"Instr_ok C (instr_sc2 (VVUNOP V128 v_vvunop)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]))"
	| Instr_ok__vvbinop :
		"Instr_ok C (instr_sc2 (VVBINOP V128 v_vvbinop)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| Instr_ok__vvternop :
		"Instr_ok C (instr_sc2 (VVTERNOP V128 v_vvternop)) (mk_functype (mk_list [valtype_V128, valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| Instr_ok__vvtestop :
		"Instr_ok C (instr_sc2 (VVTESTOP V128 v_vvtestop)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32]))"
	| vunop :
		"Instr_ok C (instr_sc2 (VUNOP sh vunop_sh)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]))"
	| vbinop :
		"Instr_ok C (instr_sc2 (VBINOP sh vbinop_sh)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| vtestop :
		"Instr_ok C (instr_sc2 (VTESTOP sh vtestop_sh)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32]))"
	| vrelop :
		"Instr_ok C (instr_sc2 (VRELOP sh vrelop_sh)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| vshiftop :
		"Instr_ok C (instr_sc2 (VSHIFTOP sh vshiftop_sh)) (mk_functype (mk_list [valtype_V128, valtype_I32]) (mk_list [valtype_V128]))"
	| vbitmask :
		"Instr_ok C (instr_sc3 (VBITMASK sh)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32]))"
	| vswizzle :
		"Instr_ok C (instr_sc3 (VSWIZZLE sh)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| vshuffle :
		"(wf_dim (fun_dim (shape_ishape sh))) ⟹
		 list_all (λ (i :: laneidx). ((proj_uN_0 i) < (2 * (proj_dim_0 (fun_dim (shape_ishape sh)))))) i_lst ⟹
		 Instr_ok C (instr_sc3 (VSHUFFLE sh i_lst)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| vsplat :
		"Instr_ok C (instr_sc3 (VSPLAT sh)) (mk_functype (mk_list [(valtype_numtype (shunpack sh))]) (mk_list [valtype_V128]))"
	| vextract_lane :
		"(wf_dim (fun_dim sh)) ⟹
		 ((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) ⟹
		 Instr_ok C (instr_sc3 (VEXTRACT_LANE sh sx_opt i)) (mk_functype (mk_list [valtype_V128]) (mk_list [(valtype_numtype (shunpack sh))]))"
	| vreplace_lane :
		"(wf_dim (fun_dim sh)) ⟹
		 ((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) ⟹
		 Instr_ok C (instr_sc3 (VREPLACE_LANE sh i)) (mk_functype (mk_list [valtype_V128, (valtype_numtype (shunpack sh))]) (mk_list [valtype_V128]))"
	| vextunop :
		"Instr_ok C (instr_sc3 (VEXTUNOP sh_1 sh_2 vextunop)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]))"
	| vextbinop :
		"Instr_ok C (instr_sc3 (VEXTBINOP sh_1 sh_2 vextbinop)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| vnarrow :
		"Instr_ok C (instr_sc3 (VNARROW sh_1 sh_2 v_sx)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| Instr_ok__vcvtop :
		"Instr_ok C (instr_sc4 (VCVTOP sh_1 sh_2 v_vcvtop)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]))"
	| local_get :
		"((proj_uN_0 x) < (length (context_LOCALS C))) ⟹
		 (((context_LOCALS C) ! (proj_uN_0 x)) = t) ⟹
		 Instr_ok C (instr_sc4 (LOCAL_GET x)) (mk_functype (mk_list []) (mk_list [t]))"
	| local_set :
		"((proj_uN_0 x) < (length (context_LOCALS C))) ⟹
		 (((context_LOCALS C) ! (proj_uN_0 x)) = t) ⟹
		 Instr_ok C (instr_sc4 (LOCAL_SET x)) (mk_functype (mk_list [t]) (mk_list []))"
	| local_tee :
		"((proj_uN_0 x) < (length (context_LOCALS C))) ⟹
		 (((context_LOCALS C) ! (proj_uN_0 x)) = t) ⟹
		 Instr_ok C (instr_sc4 (LOCAL_TEE x)) (mk_functype (mk_list [t]) (mk_list [t]))"
	| global_get :
		"((proj_uN_0 x) < (length (context_GLOBALS C))) ⟹
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype v_mut t)) ⟹
		 Instr_ok C (instr_sc4 (GLOBAL_GET x)) (mk_functype (mk_list []) (mk_list [t]))"
	| global_set :
		"((proj_uN_0 x) < (length (context_GLOBALS C))) ⟹
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype (Some MUT_MUT) t)) ⟹
		 Instr_ok C (instr_sc4 (GLOBAL_SET x)) (mk_functype (mk_list [t]) (mk_list []))"
	| table_get :
		"(wf_tabletype (mk_tabletype lim rt)) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) ⟹
		 Instr_ok C (instr_sc5 (TABLE_GET x)) (mk_functype (mk_list [valtype_I32]) (mk_list [(valtype_reftype rt)]))"
	| table_set :
		"(wf_tabletype (mk_tabletype lim rt)) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) ⟹
		 Instr_ok C (instr_sc5 (TABLE_SET x)) (mk_functype (mk_list [valtype_I32, (valtype_reftype rt)]) (mk_list []))"
	| table_size :
		"(wf_tabletype (mk_tabletype lim rt)) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) ⟹
		 Instr_ok C (instr_sc5 (TABLE_SIZE x)) (mk_functype (mk_list []) (mk_list [valtype_I32]))"
	| table_grow :
		"(wf_tabletype (mk_tabletype lim rt)) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) ⟹
		 Instr_ok C (instr_sc5 (TABLE_GROW x)) (mk_functype (mk_list [(valtype_reftype rt), valtype_I32]) (mk_list [valtype_I32]))"
	| table_fill :
		"(wf_tabletype (mk_tabletype lim rt)) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) ⟹
		 Instr_ok C (instr_sc5 (TABLE_FILL x)) (mk_functype (mk_list [valtype_I32, (valtype_reftype rt), valtype_I32]) (mk_list []))"
	| table_copy :
		"(wf_tabletype (mk_tabletype lim_1 rt)) ⟹
		 (wf_tabletype (mk_tabletype lim_2 rt)) ⟹
		 ((proj_uN_0 x_1) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x_1)) = (mk_tabletype lim_1 rt)) ⟹
		 ((proj_uN_0 x_2) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x_2)) = (mk_tabletype lim_2 rt)) ⟹
		 Instr_ok C (instr_sc5 (TABLE_COPY x_1 x_2)) (mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list []))"
	| table_init :
		"(wf_tabletype (mk_tabletype lim rt)) ⟹
		 ((proj_uN_0 x_1) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x_1)) = (mk_tabletype lim rt)) ⟹
		 ((proj_uN_0 x_2) < (length (context_ELEMS C))) ⟹
		 (((context_ELEMS C) ! (proj_uN_0 x_2)) = rt) ⟹
		 Instr_ok C (instr_sc5 (TABLE_INIT x_1 x_2)) (mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list []))"
	| elem_drop :
		"((proj_uN_0 x) < (length (context_ELEMS C))) ⟹
		 (((context_ELEMS C) ! (proj_uN_0 x)) = rt) ⟹
		 Instr_ok C (instr_sc5 (ELEM_DROP x)) (mk_functype (mk_list []) (mk_list []))"
	| memory_size :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 Instr_ok C (instr_sc6 MEMORY_SIZE) (mk_functype (mk_list []) (mk_list [valtype_I32]))"
	| memory_grow :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 Instr_ok C (instr_sc6 MEMORY_GROW) (mk_functype (mk_list [valtype_I32]) (mk_list [valtype_I32]))"
	| memory_fill :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 Instr_ok C (instr_sc6 MEMORY_FILL) (mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list []))"
	| memory_copy :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 Instr_ok C (instr_sc6 MEMORY_COPY) (mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list []))"
	| memory_init :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 ((proj_uN_0 x) < (length (context_DATAS C))) ⟹
		 (((context_DATAS C) ! (proj_uN_0 x)) = OK) ⟹
		 Instr_ok C (instr_sc7 (MEMORY_INIT x)) (mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list []))"
	| data_drop :
		"((proj_uN_0 x) < (length (context_DATAS C))) ⟹
		 (((context_DATAS C) ! (proj_uN_0 x)) = OK) ⟹
		 Instr_ok C (instr_sc7 (DATA_DROP x)) (mk_functype (mk_list []) (mk_list []))"
	| load_val :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 ((size (valtype_numtype nt)) ≠ None) ⟹
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) ≤ (((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat))) ⟹
		 Instr_ok C (instr_sc5 (LOAD nt None v_memarg)) (mk_functype (mk_list [valtype_I32]) (mk_list [(valtype_numtype nt)]))"
	| load_pack :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) ≤ ((v_M :: nat) div (8 :: nat))) ⟹
		 Instr_ok C (instr_sc5 (LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_M) v_sx))) v_memarg)) (mk_functype (mk_list [valtype_I32]) (mk_list [(valtype_Inn v_Inn)]))"
	| store_val :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 ((size (valtype_numtype nt)) ≠ None) ⟹
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) ≤ (((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat))) ⟹
		 Instr_ok C (instr_sc6 (STORE nt None v_memarg)) (mk_functype (mk_list [valtype_I32, (valtype_numtype nt)]) (mk_list []))"
	| store_pack :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) ≤ ((v_M :: nat) div (8 :: nat))) ⟹
		 Instr_ok C (instr_sc6 (STORE (numtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg)) (mk_functype (mk_list [valtype_I32, (valtype_Inn v_Inn)]) (mk_list []))"
	| vload :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) ≤ (((v_M :: nat) div (8 :: nat)) * (v_N :: nat))) ⟹
		 Instr_ok C (instr_sc6 (VLOAD V128 (Some (SHAPEX_underscore v_M v_N v_sx)) v_memarg)) (mk_functype (mk_list [valtype_I32]) (mk_list [valtype_V128]))"
	| vload_splat :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) ≤ ((v_n :: nat) div (8 :: nat))) ⟹
		 Instr_ok C (instr_sc6 (VLOAD V128 (Some (SPLAT v_n)) v_memarg)) (mk_functype (mk_list [valtype_I32]) (mk_list [valtype_V128]))"
	| vload_zero :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) ≤ ((v_n :: nat) div (8 :: nat))) ⟹
		 Instr_ok C (instr_sc6 (VLOAD V128 (Some (vloadop_ZERO v_n)) v_memarg)) (mk_functype (mk_list [valtype_I32]) (mk_list [valtype_V128]))"
	| vload_lane :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) ≤ ((v_n :: nat) div (8 :: nat))) ⟹
		 (((proj_uN_0 v_laneidx) :: nat) < ((128 :: nat) div (v_n :: nat))) ⟹
		 Instr_ok C (instr_sc6 (VLOAD_LANE V128 (mk_sz v_n) v_memarg v_laneidx)) (mk_functype (mk_list [valtype_I32, valtype_V128]) (mk_list [valtype_V128]))"
	| vstore :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 ((size valtype_V128) ≠ None) ⟹
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) ≤ (((the ((size valtype_V128))) :: nat) div (8 :: nat))) ⟹
		 Instr_ok C (instr_sc6 (VSTORE V128 v_memarg)) (mk_functype (mk_list [valtype_I32, valtype_V128]) (mk_list []))"
	| vstore_lane :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) ≤ ((v_n :: nat) div (8 :: nat))) ⟹
		 (((proj_uN_0 v_laneidx) :: nat) < ((128 :: nat) div (v_n :: nat))) ⟹
		 Instr_ok C (instr_sc6 (VSTORE_LANE V128 (mk_sz v_n) v_memarg v_laneidx)) (mk_functype (mk_list [valtype_I32, valtype_V128]) (mk_list []))"
	| empty :
		"Instrs_ok C [] (mk_functype (mk_list []) (mk_list []))"
	| Instrs_ok__instr :
		"(Instr_ok C v_instr (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Instrs_ok C [v_instr] (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
	| seq :
		"(Instrs_ok C instr_1_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (Instrs_ok C instr_2_lst (mk_functype (mk_list t_2_lst) (mk_list t_3_lst))) ⟹
		 Instrs_ok C (instr_1_lst @ instr_2_lst) (mk_functype (mk_list t_1_lst) (mk_list t_3_lst))"
	| sub :
		"(Instrs_ok C instr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (Resulttype_sub (mk_list t'_1_lst) (mk_list t_1_lst)) ⟹
		 (Resulttype_sub (mk_list t_2_lst) (mk_list t'_2_lst)) ⟹
		 Instrs_ok C instr_lst (mk_functype (mk_list t'_1_lst) (mk_list t'_2_lst))"
	| Instrs_ok__frame :
		"(Instrs_ok C instr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 Instrs_ok C instr_lst (mk_functype (mk_list (t_lst @ t_1_lst)) (mk_list (t_lst @ t_2_lst)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:139.1-139.69 *)
inductive Expr_ok :: "res_context ⇒ expr ⇒ resulttype ⇒ bool" where
	  mk_Expr_ok :
		"(Instrs_ok C instr_lst (mk_functype (mk_list []) (mk_list t_lst))) ⟹
		 Expr_ok C instr_lst (mk_list t_lst)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:529.1-529.78 *)
inductive Instr_const :: "res_context ⇒ instr ⇒ bool" where
	  Instr_const__const :
		"Instr_const C (instr_sc1 (res_CONST nt c))"
	| Instr_const__vconst :
		"Instr_const C (instr_sc1 (VCONST vt vc))"
	| Instr_const__ref_null :
		"Instr_const C (instr_sc4 (REF_NULL rt))"
	| Instr_const__ref_func :
		"Instr_const C (instr_sc4 (REF_FUNC x))"
	| Instr_const__global_get :
		"((proj_uN_0 x) < (length (context_GLOBALS C))) ⟹
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype None t)) ⟹
		 Instr_const C (instr_sc4 (GLOBAL_GET x))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:530.1-530.77 *)
inductive Expr_const :: "res_context ⇒ expr ⇒ bool" where
	  mk_Expr_const :
		"list_all (λ (v_instr :: instr). (Instr_const C v_instr)) instr_lst ⟹
		 Expr_const C instr_lst"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:531.1-531.78 *)
inductive Expr_ok_const :: "res_context ⇒ expr ⇒ valtype ⇒ bool" where
	  mk_Expr_ok_const :
		"(Expr_ok C v_expr (mk_list [t])) ⟹
		 (Expr_const C v_expr) ⟹
		 Expr_ok_const C v_expr t"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:564.1-564.73 *)
inductive Type_ok :: "type ⇒ functype ⇒ bool" where
	  mk_Type_ok :
		"(Functype_ok ft) ⟹
		 Type_ok (res_TYPE ft) ft"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:565.1-565.73 *)
inductive Func_ok :: "res_context ⇒ func ⇒ functype ⇒ bool" where
	  mk_Func_ok :
		"(wf_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = (t_1_lst @ t_lst), LABELS = [(mk_list t_2_lst)], context_RETURN = (Some (mk_list t_2_lst)) ⦈) ⟹
		 ((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (((context_TYPES C) ! (proj_uN_0 x)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 list_all (λ (t :: valtype). (t ≠ BOT)) t_lst ⟹
		 (Expr_ok (append_context C ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = (t_1_lst @ t_lst), LABELS = [(mk_list t_2_lst)], context_RETURN = (Some (mk_list t_2_lst)) ⦈) v_expr (mk_list t_2_lst)) ⟹
		 Func_ok C (func_FUNC x (map (λ (t :: valtype). (LOCAL t)) t_lst) v_expr) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:566.1-566.75 *)
inductive Global_ok :: "res_context ⇒ global ⇒ globaltype ⇒ bool" where
	  mk_Global_ok :
		"(Globaltype_ok gt) ⟹
		 (gt = (mk_globaltype v_mut t)) ⟹
		 (Expr_ok_const C v_expr t) ⟹
		 Global_ok C (global_GLOBAL gt v_expr) gt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:567.1-567.74 *)
inductive Table_ok :: "res_context ⇒ table ⇒ tabletype ⇒ bool" where
	  mk_Table_ok :
		"(Tabletype_ok tt) ⟹
		 Table_ok C (table_TABLE tt) tt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:568.1-568.72 *)
inductive Mem_ok :: "res_context ⇒ mem ⇒ memtype ⇒ bool" where
	  mk_Mem_ok :
		"(Memtype_ok mt) ⟹
		 Mem_ok C (MEMORY mt) mt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:571.1-571.77 *)
inductive Elemmode_ok :: "res_context ⇒ elemmode ⇒ reftype ⇒ bool" where
	  active :
		"(wf_tabletype (mk_tabletype lim rt)) ⟹
		 ((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) ⟹
		 (Expr_ok_const C v_expr valtype_I32) ⟹
		 Elemmode_ok C (ACTIVE x v_expr) rt"
	| res_passive :
		"Elemmode_ok C PASSIVE rt"
	| res_declare :
		"Elemmode_ok C DECLARE rt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:569.1-569.73 *)
inductive Elem_ok :: "res_context ⇒ elem ⇒ reftype ⇒ bool" where
	  mk_Elem_ok :
		"list_all (λ (v_expr :: expr). (Expr_ok_const C v_expr (valtype_reftype rt))) expr_lst ⟹
		 (Elemmode_ok C v_elemmode rt) ⟹
		 Elem_ok C (ELEM rt expr_lst v_elemmode) rt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:572.1-572.77 *)
inductive Datamode_ok :: "res_context ⇒ datamode ⇒ bool" where
	  Datamode_ok__active :
		"(wf_memtype mt) ⟹
		 (0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 (Expr_ok_const C v_expr valtype_I32) ⟹
		 Datamode_ok C (datamode_ACTIVE (mk_uN 0) v_expr)"
	| Datamode_ok__passive :
		"Datamode_ok C datamode_PASSIVE"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:570.1-570.73 *)
inductive Data_ok :: "res_context ⇒ data ⇒ bool" where
	  mk_Data_ok :
		"(Datamode_ok C v_datamode) ⟹
		 Data_ok C (DATA b_lst v_datamode)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:573.1-573.74 *)
inductive Start_ok :: "res_context ⇒ start ⇒ bool" where
	  mk_Start_ok :
		"((proj_uN_0 x) < (length (context_FUNCS C))) ⟹
		 (((context_FUNCS C) ! (proj_uN_0 x)) = (mk_functype (mk_list []) (mk_list []))) ⟹
		 Start_ok C (START x)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:637.1-637.80 *)
inductive Import_ok :: "res_context ⇒ import ⇒ externtype ⇒ bool" where
	  mk_Import_ok :
		"(Externtype_ok xt) ⟹
		 Import_ok C (IMPORT name_1 name_2 xt) xt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:639.1-639.83 *)
inductive Externidx_ok :: "res_context ⇒ externidx ⇒ externtype ⇒ bool" where
	  Externidx_ok__func :
		"((proj_uN_0 x) < (length (context_FUNCS C))) ⟹
		 (((context_FUNCS C) ! (proj_uN_0 x)) = ft) ⟹
		 Externidx_ok C (externidx_FUNC x) (FUNC ft)"
	| Externidx_ok__global :
		"((proj_uN_0 x) < (length (context_GLOBALS C))) ⟹
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = gt) ⟹
		 Externidx_ok C (externidx_GLOBAL x) (GLOBAL gt)"
	| Externidx_ok__table :
		"((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = tt) ⟹
		 Externidx_ok C (externidx_TABLE x) (TABLE tt)"
	| Externidx_ok__mem :
		"((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = mt) ⟹
		 Externidx_ok C (externidx_MEM x) (MEM mt)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:638.1-638.80 *)
inductive Export_ok :: "res_context ⇒ export ⇒ externtype ⇒ bool" where
	  mk_Export_ok :
		"(Externidx_ok C v_externidx xt) ⟹
		 Export_ok C (EXPORT v_name v_externidx) xt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:669.1-669.62 *)
inductive Module_ok :: "module ⇒ bool" where
	  mk_Module_ok :
		"(fun_globalsxt ixt_lst var_3) ⟹
		 (fun_funcsxt ixt_lst var_2) ⟹
		 (fun_memsxt ixt_lst var_1) ⟹
		 (fun_tablesxt ixt_lst var_0) ⟹
		 list_all (λ (ixt :: externtype). (wf_externtype ixt)) ixt_lst ⟹
		 (wf_context C') ⟹
		 (wf_context C) ⟹
		 list_all (λ (xt :: externtype). (wf_externtype xt)) xt_lst ⟹
		 list_all (λ (iter :: tabletype). (wf_tabletype iter)) var_0 ⟹
		 list_all (λ (iter :: memtype). (wf_memtype iter)) var_1 ⟹
		 (wf_context ⦇ context_TYPES = ft'_lst, context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [], context_RETURN = None ⦈) ⟹
		 (wf_context ⦇ context_TYPES = ft'_lst, context_FUNCS = (ift_lst @ ft_lst), context_GLOBALS = (igt_lst @ gt_lst), context_TABLES = (itt_lst @ tt_lst), context_MEMS = (imt_lst @ mt_lst), context_ELEMS = rt_lst, context_DATAS = (repeat v_n OK), context_LOCALS = [], LABELS = [], context_RETURN = None ⦈) ⟹
		 (wf_context ⦇ context_TYPES = ft'_lst, context_FUNCS = (ift_lst @ ft_lst), context_GLOBALS = igt_lst, context_TABLES = (itt_lst @ tt_lst), context_MEMS = (imt_lst @ mt_lst), context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [], context_RETURN = None ⦈) ⟹
		 ((length ft'_lst) = (length type_lst)) ⟹
		 list_all2 (λ (ft' :: functype) (v_type :: type). (Type_ok v_type ft')) ft'_lst type_lst ⟹
		 ((length import_lst) = (length ixt_lst)) ⟹
		 list_all2 (λ (v_import :: import) (ixt :: externtype). (Import_ok ⦇ context_TYPES = ft'_lst, context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [], context_RETURN = None ⦈ v_import ixt)) import_lst ixt_lst ⟹
		 ((length global_lst) = (length gt_lst)) ⟹
		 list_all2 (λ (v_global :: global) (gt :: globaltype). (Global_ok C' v_global gt)) global_lst gt_lst ⟹
		 ((length table_lst) = (length tt_lst)) ⟹
		 list_all2 (λ (v_table :: table) (tt :: tabletype). (Table_ok C' v_table tt)) table_lst tt_lst ⟹
		 ((length mem_lst) = (length mt_lst)) ⟹
		 list_all2 (λ (v_mem :: mem) (mt :: memtype). (Mem_ok C' v_mem mt)) mem_lst mt_lst ⟹
		 ((length elem_lst) = (length rt_lst)) ⟹
		 list_all2 (λ (v_elem :: elem) (rt :: reftype). (Elem_ok C' v_elem rt)) elem_lst rt_lst ⟹
		 list_all (λ (v_data :: data). (Data_ok C' v_data)) data_lst ⟹
		 ((length ft_lst) = (length func_lst)) ⟹
		 list_all2 (λ (ft :: functype) (v_func :: func). (Func_ok C v_func ft)) ft_lst func_lst ⟹
		 list_all (λ (v_start :: start). (Start_ok C v_start)) (option_to_list start_opt) ⟹
		 ((length export_lst) = (length xt_lst)) ⟹
		 list_all2 (λ (v_export :: export) (xt :: externtype). (Export_ok C v_export xt)) export_lst xt_lst ⟹
		 ((length mt_lst) ≤ 1) ⟹
		 (C = ⦇ context_TYPES = ft'_lst, context_FUNCS = (ift_lst @ ft_lst), context_GLOBALS = (igt_lst @ gt_lst), context_TABLES = (itt_lst @ tt_lst), context_MEMS = (imt_lst @ mt_lst), context_ELEMS = rt_lst, context_DATAS = (repeat v_n OK), context_LOCALS = [], LABELS = [], context_RETURN = None ⦈) ⟹
		 (C' = ⦇ context_TYPES = ft'_lst, context_FUNCS = (ift_lst @ ft_lst), context_GLOBALS = igt_lst, context_TABLES = (itt_lst @ tt_lst), context_MEMS = (imt_lst @ mt_lst), context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [], context_RETURN = None ⦈) ⟹
		 (ift_lst = var_2) ⟹
		 (igt_lst = var_3) ⟹
		 (itt_lst = var_0) ⟹
		 (imt_lst = var_1) ⟹
		 (v_n = (length data_lst)) ⟹
		 Module_ok (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:276.1-278.15 *)
inductive Step_pure_before_vtestop_false :: "(admininstr list) ⇒ bool" where
	  vtestop_true_0 :
		"list_all (λ (ci_1 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ci_1)) ci_1_lst ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) iter)) (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c) ⟹
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ⟹
		 (ci_1_lst = (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c)) ⟹
		 list_all (λ (ci_1 :: lane_underscore). ((proj_lane__2 ci_1) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1 :: lane_underscore). ((proj_uN_0 (the ((proj_lane__2 ci_1)))) ≠ 0)) ci_1_lst ⟹
		 Step_pure_before_vtestop_false [(admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc3 (admininstr_st3_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE)))]"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.77 *)
inductive Step_pure :: "(admininstr list) ⇒ (admininstr list) ⇒ bool" where
	  Step_pure__unreachable :
		"Step_pure [(admininstr_sc0 admininstr_st0_UNREACHABLE)] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| Step_pure__nop :
		"Step_pure [(admininstr_sc0 admininstr_st0_NOP)] []"
	| Step_pure__drop :
		"Step_pure [(admininstr_val v_val), (admininstr_sc0 admininstr_st0_DROP)] []"
	| select_true :
		"((proj_num__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 c)))) ≠ 0) ⟹
		 Step_pure [(admininstr_val val_1), (admininstr_val val_2), (admininstr_sc1 (admininstr_st1_CONST I32 c)), (admininstr_sc0 (admininstr_st0_SELECT t_lst_opt))] [(admininstr_val val_1)]"
	| select_false :
		"((proj_num__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 c)))) = 0) ⟹
		 Step_pure [(admininstr_val val_1), (admininstr_val val_2), (admininstr_sc1 (admininstr_st1_CONST I32 c)), (admininstr_sc0 (admininstr_st0_SELECT t_lst_opt))] [(admininstr_val val_2)]"
	| if_true :
		"((proj_num__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 c)))) ≠ 0) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST I32 c)), (admininstr_sc0 (admininstr_st0_IFELSE bt instr_1_lst instr_2_lst))] [(admininstr_sc0 (admininstr_st0_BLOCK bt instr_1_lst))]"
	| if_false :
		"((proj_num__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 c)))) = 0) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST I32 c)), (admininstr_sc0 (admininstr_st0_IFELSE bt instr_1_lst instr_2_lst))] [(admininstr_sc0 (admininstr_st0_BLOCK bt instr_2_lst))]"
	| label_vals :
		"Step_pure [(admininstr_sc8 (LABEL_underscore v_n instr_lst (map (λ (v_val :: val). (admininstr_val v_val)) val_lst)))] (map (λ (v_val :: val). (admininstr_val v_val)) val_lst)"
	| br_zero :
		"(v_n = (length val_lst)) ⟹
		 Step_pure [(admininstr_sc8 (LABEL_underscore v_n instr'_lst ((((map (λ (val' :: val). (admininstr_val val')) val'_lst) @ (map (λ (v_val :: val). (admininstr_val v_val)) val_lst)) @ [(admininstr_sc0 (admininstr_st0_BR (mk_uN 0)))]) @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))))] ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ (map (λ (instr' :: instr). (admininstr_instr instr')) instr'_lst))"
	| br_succ :
		"Step_pure [(admininstr_sc8 (LABEL_underscore v_n instr'_lst (((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc0 (admininstr_st0_BR (mk_uN ((proj_uN_0 l) + 1))))]) @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))))] ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc0 (admininstr_st0_BR l))])"
	| br_if_true :
		"((proj_num__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 c)))) ≠ 0) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST I32 c)), (admininstr_sc0 (admininstr_st0_BR_IF l))] [(admininstr_sc0 (admininstr_st0_BR l))]"
	| br_if_false :
		"((proj_num__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 c)))) = 0) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST I32 c)), (admininstr_sc0 (admininstr_st0_BR_IF l))] []"
	| br_table_lt :
		"((proj_uN_0 (the ((proj_num__0 i)))) < (length l_lst)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_BR_TABLE l_lst l'))] [(admininstr_sc0 (admininstr_st0_BR (l_lst ! (proj_uN_0 (the ((proj_num__0 i)))))))]"
	| br_table_ge :
		"((proj_num__0 i) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i)))) ≥ (length l_lst)) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_BR_TABLE l_lst l'))] [(admininstr_sc0 (admininstr_st0_BR l'))]"
	| frame_vals :
		"(v_n = (length val_lst)) ⟹
		 Step_pure [(admininstr_sc8 (FRAME_underscore v_n f (map (λ (v_val :: val). (admininstr_val v_val)) val_lst)))] (map (λ (v_val :: val). (admininstr_val v_val)) val_lst)"
	| return_frame :
		"(v_n = (length val_lst)) ⟹
		 Step_pure [(admininstr_sc8 (FRAME_underscore v_n f ((((map (λ (val' :: val). (admininstr_val val')) val'_lst) @ (map (λ (v_val :: val). (admininstr_val v_val)) val_lst)) @ [(admininstr_sc1 admininstr_st1_RETURN)]) @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))))] (map (λ (v_val :: val). (admininstr_val v_val)) val_lst)"
	| return_label :
		"Step_pure [(admininstr_sc8 (LABEL_underscore v_n instr'_lst (((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc1 admininstr_st1_RETURN)]) @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))))] ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc1 admininstr_st1_RETURN)])"
	| trap_vals :
		"((val_lst ≠ []) ∨ (instr_lst ≠ [])) ⟹
		 Step_pure ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ ([(admininstr_sc7 admininstr_st7_TRAP)] @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| trap_label :
		"Step_pure [(admininstr_sc8 (LABEL_underscore v_n instr'_lst [(admininstr_sc7 admininstr_st7_TRAP)]))] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| trap_frame :
		"Step_pure [(admininstr_sc8 (FRAME_underscore v_n f [(admininstr_sc7 admininstr_st7_TRAP)]))] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| unop_val :
		"list_all (λ (iter :: num_underscore). (wf_num_underscore nt iter)) (fun_unop_underscore nt unop c_1) ⟹
		 ((length (fun_unop_underscore nt unop c_1)) > 0) ⟹
		 (c ∈ set (fun_unop_underscore nt unop c_1)) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt c_1)), (admininstr_sc1 (admininstr_st1_UNOP nt unop))] [(admininstr_sc1 (admininstr_st1_CONST nt c))]"
	| unop_trap :
		"list_all (λ (iter :: num_underscore). (wf_num_underscore nt iter)) (fun_unop_underscore nt unop c_1) ⟹
		 ((fun_unop_underscore nt unop c_1) = []) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt c_1)), (admininstr_sc1 (admininstr_st1_UNOP nt unop))] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| binop_val :
		"(fun_binop_underscore nt binop c_1 c_2 var_0) ⟹
		 list_all (λ (iter :: num_underscore). (wf_num_underscore nt iter)) var_0 ⟹
		 ((length var_0) > 0) ⟹
		 (c ∈ set var_0) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt c_1)), (admininstr_sc1 (admininstr_st1_CONST nt c_2)), (admininstr_sc1 (admininstr_st1_BINOP nt binop))] [(admininstr_sc1 (admininstr_st1_CONST nt c))]"
	| binop_trap :
		"(fun_binop_underscore nt binop c_1 c_2 var_0) ⟹
		 list_all (λ (iter :: num_underscore). (wf_num_underscore nt iter)) var_0 ⟹
		 (var_0 = []) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt c_1)), (admininstr_sc1 (admininstr_st1_CONST nt c_2)), (admininstr_sc1 (admininstr_st1_BINOP nt binop))] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| Step_pure__testop :
		"(wf_num_underscore I32 (fun_testop_underscore nt testop c_1)) ⟹
		 (c = (fun_testop_underscore nt testop c_1)) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt c_1)), (admininstr_sc1 (admininstr_st1_TESTOP nt testop))] [(admininstr_sc1 (admininstr_st1_CONST I32 c))]"
	| Step_pure__relop :
		"(fun_relop_underscore nt relop c_1 c_2 var_0) ⟹
		 (wf_num_underscore I32 var_0) ⟹
		 (c = var_0) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt c_1)), (admininstr_sc1 (admininstr_st1_CONST nt c_2)), (admininstr_sc1 (admininstr_st1_RELOP nt relop))] [(admininstr_sc1 (admininstr_st1_CONST I32 c))]"
	| cvtop_val :
		"(fun_cvtop__underscore nt_1 nt_2 v_cvtop c_1 var_0) ⟹
		 list_all (λ (iter :: num_underscore). (wf_num_underscore nt_2 iter)) var_0 ⟹
		 ((length var_0) > 0) ⟹
		 (c ∈ set var_0) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt_1 c_1)), (admininstr_sc2 (admininstr_st2_CVTOP nt_2 nt_1 v_cvtop))] [(admininstr_sc1 (admininstr_st1_CONST nt_2 c))]"
	| cvtop_trap :
		"(fun_cvtop__underscore nt_1 nt_2 v_cvtop c_1 var_0) ⟹
		 list_all (λ (iter :: num_underscore). (wf_num_underscore nt_2 iter)) var_0 ⟹
		 (var_0 = []) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt_1 c_1)), (admininstr_sc2 (admininstr_st2_CVTOP nt_2 nt_1 v_cvtop))] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| ref_is_null_true :
		"(v_ref = (ref_REF_NULL rt)) ⟹
		 Step_pure [(admininstr_ref v_ref), (admininstr_sc4 admininstr_st4_REF_IS_NULL)] [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN 1))))]"
	| ref_is_null_false :
		"(v_ref ≠ (ref_REF_NULL rt)) ⟹
		 Step_pure [(admininstr_ref v_ref), (admininstr_sc4 admininstr_st4_REF_IS_NULL)] [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))))]"
	| Step_pure__vvunop :
		"(wf_uN 128 (vvunop_underscore V128 v_vvunop c_1)) ⟹
		 (c = (vvunop_underscore V128 v_vvunop c_1)) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VVUNOP V128 v_vvunop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vvbinop :
		"(wf_uN 128 (vvbinop_underscore V128 v_vvbinop c_1 c_2)) ⟹
		 (c = (vvbinop_underscore V128 v_vvbinop c_1 c_2)) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc2 (admininstr_st2_VVBINOP V128 v_vvbinop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vvternop :
		"(wf_uN 128 (vvternop_underscore V128 v_vvternop c_1 c_2 c_3)) ⟹
		 (c = (vvternop_underscore V128 v_vvternop c_1 c_2 c_3)) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_3)), (admininstr_sc2 (admininstr_st2_VVTERNOP V128 v_vvternop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vvtestop :
		"((size valtype_V128) ≠ None) ⟹
		 (wf_uN 32 (ine_underscore (the ((size valtype_V128))) c_1 (mk_uN 0))) ⟹
		 (wf_uN 128 (mk_uN 0)) ⟹
		 ((proj_num__0 c) ≠ None) ⟹
		 ((the ((proj_num__0 c))) = (ine_underscore (the ((size valtype_V128))) c_1 (mk_uN 0))) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VVTESTOP V128 ANY_TRUE))] [(admininstr_sc1 (admininstr_st1_CONST I32 c))]"
	| Step_pure__vunop :
		"(fun_vunop_underscore sh vunop c_1 var_0) ⟹
		 list_all (λ (iter :: vec_underscore). (wf_uN 128 iter)) var_0 ⟹
		 ((length var_0) > 0) ⟹
		 (c ∈ set var_0) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VUNOP sh vunop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vunop_trap :
		"(fun_vunop_underscore sh vunop c_1 var_0) ⟹
		 list_all (λ (iter :: vec_underscore). (wf_uN 128 iter)) var_0 ⟹
		 (var_0 = []) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VUNOP sh vunop))] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| vbinop_val :
		"(fun_vbinop_underscore sh vbinop c_1 c_2 var_0) ⟹
		 list_all (λ (iter :: vec_underscore). (wf_uN 128 iter)) var_0 ⟹
		 ((length var_0) > 0) ⟹
		 (c ∈ set var_0) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc2 (admininstr_st2_VBINOP sh vbinop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vbinop_trap :
		"(fun_vbinop_underscore sh vbinop c_1 c_2 var_0) ⟹
		 list_all (λ (iter :: vec_underscore). (wf_uN 128 iter)) var_0 ⟹
		 (var_0 = []) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc2 (admininstr_st2_VBINOP sh vbinop))] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| vtestop_true :
		"list_all (λ (ci_1 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ci_1)) ci_1_lst ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) iter)) (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c) ⟹
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ⟹
		 (ci_1_lst = (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c)) ⟹
		 list_all (λ (ci_1 :: lane_underscore). ((proj_lane__2 ci_1) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1 :: lane_underscore). ((proj_uN_0 (the ((proj_lane__2 ci_1)))) ≠ 0)) ci_1_lst ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc3 (admininstr_st3_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE)))] [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN 1))))]"
	| vtestop_false :
		"(~(Step_pure_before_vtestop_false [(admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc3 (admininstr_st3_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE)))])) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc3 (admininstr_st3_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE)))] [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))))]"
	| Step_pure__vrelop :
		"(fun_vrelop_underscore sh vrelop c_1 c_2 var_0) ⟹
		 (wf_uN 128 var_0) ⟹
		 (var_0 = c) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc3 (admininstr_st3_VRELOP sh vrelop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vshiftop :
		"((length var_0_lst) = (length c'_lst)) ⟹
		 list_all2 (λ (var_0 :: lane_underscore) (c' :: lane_underscore). (fun_vshiftop_underscore (ishape_X v_Jnn (mk_dim v_N)) vshiftop c' (mk_uN v_n) var_0)) var_0_lst c'_lst ⟹
		 list_all (λ (c' :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) c')) c'_lst ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) iter)) (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c_1) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) var_0_lst)) ⟹
		 list_all (λ (var_0 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) var_0)) var_0_lst ⟹
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ⟹
		 (wf_ishape (ishape_X v_Jnn (mk_dim v_N))) ⟹
		 (wf_uN 32 (mk_uN v_n)) ⟹
		 (c'_lst = (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c_1)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) var_0_lst)) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc3 (admininstr_st3_VSHIFTOP (ishape_X v_Jnn (mk_dim v_N)) vshiftop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vbitmask :
		"((length var_0_lst) = (length ci_1_lst)) ⟹
		 list_all (λ (ci_1 :: lane_underscore). ((proj_lane__2 ci_1) ≠ None)) ci_1_lst ⟹
		 list_all2 (λ (var_0 :: uN) (ci_1 :: lane_underscore). (fun_ilt_underscore (lsize (lanetype_Jnn v_Jnn)) S (the ((proj_lane__2 ci_1))) (mk_uN 0) var_0)) var_0_lst ci_1_lst ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) iter)) (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c) ⟹
		 list_all (λ (iter :: bit). (wf_bit iter)) (ibits_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) ci) ⟹
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ⟹
		 list_all (λ (var_0 :: uN). (wf_bit (mk_bit (proj_uN_0 var_0)))) var_0_lst ⟹
		 (wf_bit (mk_bit 0)) ⟹
		 (ci_1_lst = (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c)) ⟹
		 ((ibits_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) ci) = ((map (λ (var_0 :: uN). (mk_bit (proj_uN_0 var_0))) var_0_lst) @ (repeat (((32 :: nat) - (v_N :: nat)) :: nat) (mk_bit 0)))) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc3 (admininstr_st3_VBITMASK (ishape_X v_Jnn (mk_dim v_N))))] [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (irev_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) ci))))]"
	| Step_pure__vswizzle :
		"list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_M))) iter)) (lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_M)) c_2) ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_M))) iter)) (lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_M)) c_1) ⟹
		 ((proj_uN_0 (the ((proj_lane__1 (ci_lst ! k))))) < (length c'_lst)) ⟹
		 ((proj_lane__1 (ci_lst ! k)) ≠ None) ⟹
		 (k < (length ci_lst)) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_M)) (mkseq (λ k. (mk_lane__1 v_Pnn (c'_lst ! (proj_uN_0 (the ((proj_lane__1 (ci_lst ! k)))))))) v_M))) ⟹
		 (wf_shape (X (lanetype_packtype v_Pnn) (mk_dim v_M))) ⟹
		 (wf_uN (psize v_Pnn) (mk_uN 0)) ⟹
		 ((proj_uN_0 (the ((proj_lane__1 (ci_lst ! k))))) < (length c'_lst)) ⟹
		 ((proj_lane__1 (ci_lst ! k)) ≠ None) ⟹
		 (k < (length ci_lst)) ⟹
		 (wf_lane_underscore (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_M))) (mk_lane__1 v_Pnn (c'_lst ! (proj_uN_0 (the ((proj_lane__1 (ci_lst ! k)))))))) ⟹
		 (ci_lst = (lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_M)) c_2)) ⟹
		 list_all (λ (iter_0 :: lane_underscore). ((proj_lane__1 iter_0) ≠ None)) (lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_M)) c_1) ⟹
		 (c'_lst = ((map (λ (iter_0 :: lane_underscore). (the ((proj_lane__1 iter_0)))) (lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_M)) c_1)) @ (repeat (((256 :: nat) - (v_M :: nat)) :: nat) (mk_uN 0)))) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_M)) (mkseq (λ k. (mk_lane__1 v_Pnn (c'_lst ! (proj_uN_0 (the ((proj_lane__1 (ci_lst ! k)))))))) v_M))) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc3 (admininstr_st3_VSWIZZLE (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_M))))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vshuffle :
		"list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_N))) iter)) (lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_N)) c_1) ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_N))) iter)) (lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_N)) c_2) ⟹
		 ((proj_uN_0 (i_lst ! k)) < (length c'_lst)) ⟹
		 (k < (length i_lst)) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_N)) (mkseq (λ k. (mk_lane__1 v_Pnn (c'_lst ! (proj_uN_0 (i_lst ! k))))) v_N))) ⟹
		 list_all (λ (c' :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_N))) (mk_lane__1 v_Pnn c'))) c'_lst ⟹
		 (wf_shape (X (lanetype_packtype v_Pnn) (mk_dim v_N))) ⟹
		 ((proj_uN_0 (i_lst ! k)) < (length c'_lst)) ⟹
		 (k < (length i_lst)) ⟹
		 (wf_lane_underscore (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_N))) (mk_lane__1 v_Pnn (c'_lst ! (proj_uN_0 (i_lst ! k))))) ⟹
		 ((map (λ (c' :: iN). (mk_lane__1 v_Pnn c')) c'_lst) = ((lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_N)) c_1) @ (lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_N)) c_2))) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_N)) (mkseq (λ k. (mk_lane__1 v_Pnn (c'_lst ! (proj_uN_0 (i_lst ! k))))) v_N))) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc3 (admininstr_st3_VSHUFFLE (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_N)) i_lst))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vsplat :
		"(wf_uN 128 (inv_lanes_underscore (X v_Lnn (mk_dim v_N)) (repeat v_N (packnum_underscore v_Lnn c_1)))) ⟹
		 (wf_lane_underscore (fun_lanetype (X v_Lnn (mk_dim v_N))) (packnum_underscore v_Lnn c_1)) ⟹
		 (wf_shape (X v_Lnn (mk_dim v_N))) ⟹
		 (c = (inv_lanes_underscore (X v_Lnn (mk_dim v_N)) (repeat v_N (packnum_underscore v_Lnn c_1)))) ⟹
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST (unpack v_Lnn) c_1)), (admininstr_sc3 (admininstr_st3_VSPLAT (X v_Lnn (mk_dim v_N))))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vextract_lane_num :
		"list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_numtype nt) (mk_dim v_N))) iter)) (lanes_underscore (X (lanetype_numtype nt) (mk_dim v_N)) c_1) ⟹
		 (wf_lane_underscore (fun_lanetype (X (lanetype_numtype nt) (mk_dim v_N))) (mk_lane__0 nt c_2)) ⟹
		 (wf_shape (X (lanetype_numtype nt) (mk_dim v_N))) ⟹
		 ((proj_uN_0 i) < (length (lanes_underscore (X (lanetype_numtype nt) (mk_dim v_N)) c_1))) ⟹
		 ((mk_lane__0 nt c_2) = ((lanes_underscore (X (lanetype_numtype nt) (mk_dim v_N)) c_1) ! (proj_uN_0 i))) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc3 (admininstr_st3_VEXTRACT_LANE (X (lanetype_numtype nt) (mk_dim v_N)) None i))] [(admininstr_sc1 (admininstr_st1_CONST nt c_2))]"
	| vextract_lane_pack :
		"((proj_lane__1 ((lanes_underscore (X (lanetype_packtype pt) (mk_dim v_N)) c_1) ! (proj_uN_0 i))) ≠ None) ⟹
		 ((proj_uN_0 i) < (length (lanes_underscore (X (lanetype_packtype pt) (mk_dim v_N)) c_1))) ⟹
		 (wf_uN 32 (extend__underscore (psize pt) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) v_sx (the ((proj_lane__1 ((lanes_underscore (X (lanetype_packtype pt) (mk_dim v_N)) c_1) ! (proj_uN_0 i))))))) ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_packtype pt) (mk_dim v_N))) iter)) (lanes_underscore (X (lanetype_packtype pt) (mk_dim v_N)) c_1) ⟹
		 (wf_shape (X (lanetype_packtype pt) (mk_dim v_N))) ⟹
		 ((proj_num__0 c_2) ≠ None) ⟹
		 ((the ((proj_num__0 c_2))) = (extend__underscore (psize pt) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) v_sx (the ((proj_lane__1 ((lanes_underscore (X (lanetype_packtype pt) (mk_dim v_N)) c_1) ! (proj_uN_0 i))))))) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc3 (admininstr_st3_VEXTRACT_LANE (X (lanetype_packtype pt) (mk_dim v_N)) (Some v_sx) i))] [(admininstr_sc1 (admininstr_st1_CONST I32 c_2))]"
	| Step_pure__vreplace_lane :
		"(wf_uN 128 (inv_lanes_underscore (X v_Lnn (mk_dim v_N)) (list_update_func (lanes_underscore (X v_Lnn (mk_dim v_N)) c_1) (proj_uN_0 i) (λ (underscore_underscore :: lane_underscore). (packnum_underscore v_Lnn c_2))))) ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X v_Lnn (mk_dim v_N))) iter)) (lanes_underscore (X v_Lnn (mk_dim v_N)) c_1) ⟹
		 (wf_lane_underscore (fun_lanetype (X v_Lnn (mk_dim v_N))) (packnum_underscore v_Lnn c_2)) ⟹
		 (wf_shape (X v_Lnn (mk_dim v_N))) ⟹
		 (c = (inv_lanes_underscore (X v_Lnn (mk_dim v_N)) (list_update_func (lanes_underscore (X v_Lnn (mk_dim v_N)) c_1) (proj_uN_0 i) (λ (underscore_underscore :: lane_underscore). (packnum_underscore v_Lnn c_2))))) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc1 (admininstr_st1_CONST (unpack v_Lnn) c_2)), (admininstr_sc3 (admininstr_st3_VREPLACE_LANE (X v_Lnn (mk_dim v_N)) i))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vextunop :
		"(fun_vextunop__underscore sh_1 sh_2 vextunop c_1 var_0) ⟹
		 (wf_uN 128 var_0) ⟹
		 (var_0 = c) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc4 (admininstr_st4_VEXTUNOP sh_1 sh_2 vextunop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vextbinop :
		"(fun_vextbinop__underscore sh_1 sh_2 vextbinop c_1 c_2 var_0) ⟹
		 (wf_uN 128 var_0) ⟹
		 (var_0 = c) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc4 (admininstr_st4_VEXTBINOP sh_1 sh_2 vextbinop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vnarrow :
		"list_all (λ (ci_1 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_1) (mk_dim N_1))) ci_1)) ci_1_lst ⟹
		 list_all (λ (ci_2 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_1) (mk_dim N_1))) ci_2)) ci_2_lst ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_1) (mk_dim N_1))) iter)) (lanes_underscore (X (lanetype_Jnn Jnn_1) (mk_dim N_1)) c_1) ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_1) (mk_dim N_1))) iter)) (lanes_underscore (X (lanetype_Jnn Jnn_1) (mk_dim N_1)) c_2) ⟹
		 list_all (λ (ci_1 :: lane_underscore). ((proj_lane__2 ci_1) ≠ None)) ci_1_lst ⟹
		 list_all (λ (ci_1 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_2)) (narrow__underscore (lsize (lanetype_Jnn Jnn_1)) (lsize (lanetype_Jnn Jnn_2)) v_sx (the ((proj_lane__2 ci_1)))))) ci_1_lst ⟹
		 list_all (λ (ci_2 :: lane_underscore). ((proj_lane__2 ci_2) ≠ None)) ci_2_lst ⟹
		 list_all (λ (ci_2 :: lane_underscore). (wf_uN (lsize (lanetype_Jnn Jnn_2)) (narrow__underscore (lsize (lanetype_Jnn Jnn_1)) (lsize (lanetype_Jnn Jnn_2)) v_sx (the ((proj_lane__2 ci_2)))))) ci_2_lst ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn Jnn_2) (mk_dim N_2)) ((map (λ (cj_1 :: iN). (mk_lane__2 Jnn_2 cj_1)) cj_1_lst) @ (map (λ (cj_2 :: iN). (mk_lane__2 Jnn_2 cj_2)) cj_2_lst)))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_1) (mk_dim N_1))) ⟹
		 (wf_shape (X (lanetype_Jnn Jnn_2) (mk_dim N_2))) ⟹
		 list_all (λ (cj_1 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_2) (mk_dim N_2))) (mk_lane__2 Jnn_2 cj_1))) cj_1_lst ⟹
		 list_all (λ (cj_2 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_2) (mk_dim N_2))) (mk_lane__2 Jnn_2 cj_2))) cj_2_lst ⟹
		 (ci_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_1) (mk_dim N_1)) c_1)) ⟹
		 (ci_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_1) (mk_dim N_1)) c_2)) ⟹
		 (cj_1_lst = (map (λ (ci_1 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_1)) (lsize (lanetype_Jnn Jnn_2)) v_sx (the ((proj_lane__2 ci_1))))) ci_1_lst)) ⟹
		 (cj_2_lst = (map (λ (ci_2 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_1)) (lsize (lanetype_Jnn Jnn_2)) v_sx (the ((proj_lane__2 ci_2))))) ci_2_lst)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Jnn Jnn_2) (mk_dim N_2)) ((map (λ (cj_1 :: iN). (mk_lane__2 Jnn_2 cj_1)) cj_1_lst) @ (map (λ (cj_2 :: iN). (mk_lane__2 Jnn_2 cj_2)) cj_2_lst)))) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc4 (admininstr_st4_VNARROW (ishape_X Jnn_2 (mk_dim N_2)) (ishape_X Jnn_1 (mk_dim N_1)) v_sx))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vcvtop_full :
		"((length var_0_lst) = (length ci_lst)) ⟹
		 list_all2 (λ (var_0 :: (lane_underscore list)) (ci :: lane_underscore). (fun_vcvtop__underscore (X Lnn_1 (mk_dim v_M)) (X Lnn_2 (mk_dim v_M)) v_vcvtop ci var_0)) var_0_lst ci_lst ⟹
		 list_all (λ (ci :: lane_underscore). (wf_lane_underscore (fun_lanetype (X Lnn_1 (mk_dim v_M))) ci)) ci_lst ⟹
		 list_all (λ (cj_lst :: (lane_underscore list)). list_all (λ (cj :: lane_underscore). (wf_lane_underscore Lnn_2 cj)) cj_lst) cj_lst_lst ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X Lnn_1 (mk_dim v_M))) iter)) (lanes_underscore (X Lnn_1 (mk_dim v_M)) c_1) ⟹
		 list_all (λ (iter :: (lane_underscore list)). list_all (λ (iter :: lane_underscore). (wf_lane_underscore Lnn_2 iter)) iter) (setproduct_underscore  var_0_lst) ⟹
		 list_all (λ (var_0 :: (lane_underscore list)). list_all (λ (iter :: lane_underscore). (wf_lane_underscore Lnn_2 iter)) var_0) var_0_lst ⟹
		 list_all (λ (cj_lst :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X Lnn_2 (mk_dim v_M)) cj_lst))) cj_lst_lst ⟹
		 (wf_shape (X Lnn_1 (mk_dim v_M))) ⟹
		 (wf_shape (X Lnn_2 (mk_dim v_M))) ⟹
		 (((halfop v_vcvtop) = None) ∧ ((zeroop v_vcvtop) = None)) ⟹
		 (ci_lst = (lanes_underscore (X Lnn_1 (mk_dim v_M)) c_1)) ⟹
		 (cj_lst_lst = (setproduct_underscore  var_0_lst)) ⟹
		 ((length (map (λ (cj_lst :: (lane_underscore list)). (inv_lanes_underscore (X Lnn_2 (mk_dim v_M)) cj_lst)) cj_lst_lst)) > 0) ⟹
		 (c ∈ set (map (λ (cj_lst :: (lane_underscore list)). (inv_lanes_underscore (X Lnn_2 (mk_dim v_M)) cj_lst)) cj_lst_lst)) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc4 (admininstr_st4_VCVTOP (X Lnn_2 (mk_dim v_M)) (X Lnn_1 (mk_dim v_M)) v_vcvtop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vcvtop_half :
		"((length var_0_lst) = (length ci_lst)) ⟹
		 list_all2 (λ (var_0 :: (lane_underscore list)) (ci :: lane_underscore). (fun_vcvtop__underscore (X Lnn_1 (mk_dim M_1)) (X Lnn_2 (mk_dim M_2)) v_vcvtop ci var_0)) var_0_lst ci_lst ⟹
		 list_all (λ (ci :: lane_underscore). (wf_lane_underscore (fun_lanetype (X Lnn_1 (mk_dim M_1))) ci)) ci_lst ⟹
		 list_all (λ (cj_lst :: (lane_underscore list)). list_all (λ (cj :: lane_underscore). (wf_lane_underscore Lnn_2 cj)) cj_lst) cj_lst_lst ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X Lnn_1 (mk_dim M_1))) iter)) (lanes_underscore (X Lnn_1 (mk_dim M_1)) c_1) ⟹
		 list_all (λ (iter :: (lane_underscore list)). list_all (λ (iter :: lane_underscore). (wf_lane_underscore Lnn_2 iter)) iter) (setproduct_underscore  var_0_lst) ⟹
		 list_all (λ (var_0 :: (lane_underscore list)). list_all (λ (iter :: lane_underscore). (wf_lane_underscore Lnn_2 iter)) var_0) var_0_lst ⟹
		 list_all (λ (cj_lst :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X Lnn_2 (mk_dim M_2)) cj_lst))) cj_lst_lst ⟹
		 (wf_shape (X Lnn_1 (mk_dim M_1))) ⟹
		 (wf_shape (X Lnn_2 (mk_dim M_2))) ⟹
		 ((halfop v_vcvtop) = (Some v_half)) ⟹
		 (ci_lst = (list_slice (lanes_underscore (X Lnn_1 (mk_dim M_1)) c_1) (fun_half v_half 0 M_2) M_2)) ⟹
		 (cj_lst_lst = (setproduct_underscore  var_0_lst)) ⟹
		 ((length (map (λ (cj_lst :: (lane_underscore list)). (inv_lanes_underscore (X Lnn_2 (mk_dim M_2)) cj_lst)) cj_lst_lst)) > 0) ⟹
		 (c ∈ set (map (λ (cj_lst :: (lane_underscore list)). (inv_lanes_underscore (X Lnn_2 (mk_dim M_2)) cj_lst)) cj_lst_lst)) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc4 (admininstr_st4_VCVTOP (X Lnn_2 (mk_dim M_2)) (X Lnn_1 (mk_dim M_1)) v_vcvtop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vcvtop_zero :
		"((length var_0_lst) = (length ci_lst)) ⟹
		 list_all2 (λ (var_0 :: (lane_underscore list)) (ci :: lane_underscore). (fun_vcvtop__underscore (X (lanetype_numtype nt_1) (mk_dim M_1)) (X (lanetype_numtype nt_2) (mk_dim M_2)) v_vcvtop ci var_0)) var_0_lst ci_lst ⟹
		 list_all (λ (ci :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_numtype nt_1) (mk_dim M_1))) ci)) ci_lst ⟹
		 list_all (λ (cj_lst :: (lane_underscore list)). list_all (λ (cj :: lane_underscore). (wf_lane_underscore (lanetype_numtype nt_2) cj)) cj_lst) cj_lst_lst ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_numtype nt_1) (mk_dim M_1))) iter)) (lanes_underscore (X (lanetype_numtype nt_1) (mk_dim M_1)) c_1) ⟹
		 list_all (λ (iter :: (lane_underscore list)). list_all (λ (iter :: lane_underscore). (wf_lane_underscore (lanetype_numtype nt_2) iter)) iter) (setproduct_underscore  (var_0_lst @ (repeat M_1 [(mk_lane__0 nt_2 (fun_zero nt_2))]))) ⟹
		 list_all (λ (var_0 :: (lane_underscore list)). list_all (λ (iter :: lane_underscore). (wf_lane_underscore (lanetype_numtype nt_2) iter)) var_0) var_0_lst ⟹
		 list_all (λ (cj_lst :: (lane_underscore list)). (wf_uN 128 (inv_lanes_underscore (X (lanetype_numtype nt_2) (mk_dim M_2)) cj_lst))) cj_lst_lst ⟹
		 (wf_shape (X (lanetype_numtype nt_1) (mk_dim M_1))) ⟹
		 (wf_shape (X (lanetype_numtype nt_2) (mk_dim M_2))) ⟹
		 (wf_lane_underscore (lanetype_numtype nt_2) (mk_lane__0 nt_2 (fun_zero nt_2))) ⟹
		 ((zeroop v_vcvtop) = (Some ZERO)) ⟹
		 (ci_lst = (lanes_underscore (X (lanetype_numtype nt_1) (mk_dim M_1)) c_1)) ⟹
		 (cj_lst_lst = (setproduct_underscore  (var_0_lst @ (repeat M_1 [(mk_lane__0 nt_2 (fun_zero nt_2))])))) ⟹
		 ((length (map (λ (cj_lst :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_numtype nt_2) (mk_dim M_2)) cj_lst)) cj_lst_lst)) > 0) ⟹
		 (c ∈ set (map (λ (cj_lst :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_numtype nt_2) (mk_dim M_2)) cj_lst)) cj_lst_lst)) ⟹
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc4 (admininstr_st4_VCVTOP (X (lanetype_numtype nt_2) (mk_dim M_2)) (X (lanetype_numtype nt_1) (mk_dim M_1)) v_vcvtop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__local_tee :
		"Step_pure [(admininstr_val v_val), (admininstr_sc5 (admininstr_st5_LOCAL_TEE x))] [(admininstr_val v_val), (admininstr_val v_val), (admininstr_sc4 (admininstr_st4_LOCAL_SET x))]"

(* Auxiliary Definition at: ../specification/wasm-2.0/8-reduction.spectec:63.1-63.73 *)
function (sequential) fun_blocktype :: "state ⇒ blocktype ⇒ functype" where
		  "fun_blocktype z (underscore_RESULT None) = (mk_functype (mk_list []) (mk_list []))"
		| "fun_blocktype z (underscore_RESULT (Some t)) = (mk_functype (mk_list []) (mk_list [t]))"
		| "fun_blocktype z (underscore_IDX x) = (fun_type z x)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:127.1-129.15 *)
inductive Step_read_before_call_indirect_trap :: "config ⇒ bool" where
	  call_indirect_call_0 :
		"(wf_tableinst (fun_table z x)) ⟹
		 list_all (λ (iter :: funcinst). (wf_funcinst iter)) (fun_funcinst z) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i)))) < (length (REFS (fun_table z x)))) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (((REFS (fun_table z x)) ! (proj_uN_0 (the ((proj_num__0 i))))) = (REF_FUNC_ADDR a)) ⟹
		 (a < (length (fun_funcinst z))) ⟹
		 ((fun_type z y) = (funcinst_TYPE ((fun_funcinst z) ! a))) ⟹
		 Step_read_before_call_indirect_trap (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y))])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:436.1-439.14 *)
inductive Step_read_before_table_fill_zero :: "config ⇒ bool" where
	  table_fill_trap_0 :
		"(wf_tableinst (fun_table z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (REFS (fun_table z x)))) ⟹
		 Step_read_before_table_fill_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_FILL x))])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:452.1-455.14 *)
inductive Step_read_before_table_copy_zero :: "config ⇒ bool" where
	  table_copy_trap_0 :
		"(wf_tableinst (fun_table z y)) ⟹
		 (wf_tableinst (fun_table z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (REFS (fun_table z y)))) ∨ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (REFS (fun_table z x))))) ⟹
		 Step_read_before_table_copy_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:457.1-462.15 *)
inductive Step_read_before_table_copy_le :: "config ⇒ bool" where
	  table_copy_zero_0 :
		"(~(Step_read_before_table_copy_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))]))) ⟹
		 (v_n = 0) ⟹
		 Step_read_before_table_copy_le (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))])"
	| table_copy_trap_1 :
		"(wf_tableinst (fun_table z y)) ⟹
		 (wf_tableinst (fun_table z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (REFS (fun_table z y)))) ∨ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (REFS (fun_table z x))))) ⟹
		 Step_read_before_table_copy_le (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:475.1-478.14 *)
inductive Step_read_before_table_init_zero :: "config ⇒ bool" where
	  table_init_trap_0 :
		"(wf_tableinst (fun_table z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (eleminst_REFS (fun_elem z y)))) ∨ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (REFS (fun_table z x))))) ⟹
		 Step_read_before_table_init_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc6 (admininstr_st6_TABLE_INIT x y))])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:616.1-619.14 *)
inductive Step_read_before_memory_fill_zero :: "config ⇒ bool" where
	  memory_fill_trap_0 :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step_read_before_memory_fill_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_FILL)])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:632.1-635.14 *)
inductive Step_read_before_memory_copy_zero :: "config ⇒ bool" where
	  memory_copy_trap_0 :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0))))) ∨ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0)))))) ⟹
		 Step_read_before_memory_copy_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:637.1-642.15 *)
inductive Step_read_before_memory_copy_le :: "config ⇒ bool" where
	  memory_copy_zero_0 :
		"(~(Step_read_before_memory_copy_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)]))) ⟹
		 (v_n = 0) ⟹
		 Step_read_before_memory_copy_le (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)])"
	| memory_copy_trap_1 :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0))))) ∨ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0)))))) ⟹
		 Step_read_before_memory_copy_le (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:655.1-658.14 *)
inductive Step_read_before_memory_init_zero :: "config ⇒ bool" where
	  memory_init_trap_0 :
		"(wf_datainst (fun_data z x)) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (datainst_BYTES (fun_data z x)))) ∨ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0)))))) ⟹
		 Step_read_before_memory_init_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 (admininstr_st7_MEMORY_INIT x))])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.1-7.77 *)
inductive Step_read :: "config ⇒ (admininstr list) ⇒ bool" where
	  Step_read__block :
		"((fun_blocktype z bt) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (k = (length val_lst)) ⟹
		 (k = (length t_1_lst)) ⟹
		 (v_n = (length t_2_lst)) ⟹
		 Step_read (mk_config z ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc0 (admininstr_st0_BLOCK bt instr_lst))])) [(admininstr_sc8 (LABEL_underscore v_n [] ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))))]"
	| Step_read__loop :
		"((fun_blocktype z bt) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (k = (length val_lst)) ⟹
		 (k = (length t_1_lst)) ⟹
		 (v_n = (length t_2_lst)) ⟹
		 Step_read (mk_config z ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc0 (admininstr_st0_LOOP bt instr_lst))])) [(admininstr_sc8 (LABEL_underscore k [(instr_sc7 (LOOP bt instr_lst))] ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))))]"
	| Step_read__call :
		"((proj_uN_0 x) < (length (fun_funcaddr z))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CALL x))]) [(admininstr_sc7 (CALL_ADDR ((fun_funcaddr z) ! (proj_uN_0 x))))]"
	| call_indirect_call :
		"(wf_tableinst (fun_table z x)) ⟹
		 list_all (λ (iter :: funcinst). (wf_funcinst iter)) (fun_funcinst z) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i)))) < (length (REFS (fun_table z x)))) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (((REFS (fun_table z x)) ! (proj_uN_0 (the ((proj_num__0 i))))) = (REF_FUNC_ADDR a)) ⟹
		 (a < (length (fun_funcinst z))) ⟹
		 ((fun_type z y) = (funcinst_TYPE ((fun_funcinst z) ! a))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y))]) [(admininstr_sc7 (CALL_ADDR a))]"
	| call_indirect_trap :
		"(~(Step_read_before_call_indirect_trap (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y))]))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| call_addr :
		"list_all (λ (iter :: funcinst). (wf_funcinst iter)) (fun_funcinst z) ⟹
		 (wf_funcinst ⦇ funcinst_TYPE = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)), funcinst_MODULE = mm, CODE = v_func ⦈) ⟹
		 (wf_func (func_FUNC x (map (λ (t :: valtype). (LOCAL t)) t_lst) instr_lst)) ⟹
		 list_all (λ (t :: valtype). ((default_underscore t) ≠ None)) t_lst ⟹
		 (wf_frame ⦇ LOCALS = (val_lst @ (map (λ (t :: valtype). (the ((default_underscore t)))) t_lst)), frame_MODULE = mm ⦈) ⟹
		 (a < (length (fun_funcinst z))) ⟹
		 (((fun_funcinst z) ! a) = ⦇ funcinst_TYPE = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)), funcinst_MODULE = mm, CODE = v_func ⦈) ⟹
		 (v_func = (func_FUNC x (map (λ (t :: valtype). (LOCAL t)) t_lst) instr_lst)) ⟹
		 (f = ⦇ LOCALS = (val_lst @ (map (λ (t :: valtype). (the ((default_underscore t)))) t_lst)), frame_MODULE = mm ⦈) ⟹
		 (k = (length val_lst)) ⟹
		 (k = (length t_1_lst)) ⟹
		 (v_n = (length t_2_lst)) ⟹
		 Step_read (mk_config z ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc7 (CALL_ADDR a))])) [(admininstr_sc8 (FRAME_underscore v_n f [(admininstr_sc8 (LABEL_underscore v_n [] (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst)))]))]"
	| Step_read__ref_func :
		"((proj_uN_0 x) < (length (fun_funcaddr z))) ⟹
		 Step_read (mk_config z [(admininstr_sc4 (admininstr_st4_REF_FUNC x))]) [(admininstr_sc7 (admininstr_st7_REF_FUNC_ADDR ((fun_funcaddr z) ! (proj_uN_0 x))))]"
	| Step_read__local_get :
		"Step_read (mk_config z [(admininstr_sc4 (admininstr_st4_LOCAL_GET x))]) [(admininstr_val (fun_local z x))]"
	| Step_read__global_get :
		"Step_read (mk_config z [(admininstr_sc5 (admininstr_st5_GLOBAL_GET x))]) [(admininstr_val (VALUE (fun_global z x)))]"
	| table_get_trap :
		"(wf_tableinst (fun_table z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i)))) ≥ (length (REFS (fun_table z x)))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc5 (admininstr_st5_TABLE_GET x))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| table_get_val :
		"((proj_uN_0 (the ((proj_num__0 i)))) < (length (REFS (fun_table z x)))) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (wf_tableinst (fun_table z x)) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc5 (admininstr_st5_TABLE_GET x))]) [(admininstr_ref ((REFS (fun_table z x)) ! (proj_uN_0 (the ((proj_num__0 i))))))]"
	| Step_read__table_size :
		"(wf_tableinst (fun_table z x)) ⟹
		 ((length (REFS (fun_table z x))) = v_n) ⟹
		 Step_read (mk_config z [(admininstr_sc5 (admininstr_st5_TABLE_SIZE x))]) [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))))]"
	| table_fill_trap :
		"(wf_tableinst (fun_table z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (REFS (fun_table z x)))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_FILL x))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| table_fill_zero :
		"((proj_num__0 i) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (REFS (fun_table z x)))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_FILL x))]) []"
	| table_fill_succ :
		"((proj_num__0 i) ≠ None) ⟹
		 (v_n ≠ 0) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (REFS (fun_table z x)))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_FILL x))]) [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc5 (admininstr_st5_TABLE_SET x)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc5 (admininstr_st5_TABLE_FILL x))]"
	| table_copy_trap :
		"(wf_tableinst (fun_table z y)) ⟹
		 (wf_tableinst (fun_table z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (REFS (fun_table z y)))) ∨ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (REFS (fun_table z x))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| table_copy_zero :
		"((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (REFS (fun_table z y)))) ∧ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) ≤ (length (REFS (fun_table z x))))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))]) []"
	| table_copy_le :
		"((proj_num__0 j) ≠ None) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (v_n ≠ 0) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (REFS (fun_table z y)))) ∧ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) ≤ (length (REFS (fun_table z x))))) ⟹
		 ((proj_uN_0 (the ((proj_num__0 j)))) ≤ (proj_uN_0 (the ((proj_num__0 i))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))]) [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc5 (admininstr_st5_TABLE_GET y)), (admininstr_sc5 (admininstr_st5_TABLE_SET x)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 j)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))]"
	| table_copy_gt :
		"((proj_num__0 j) ≠ None) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 j)))) > (proj_uN_0 (the ((proj_num__0 i))))) ⟹
		 (v_n ≠ 0) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (REFS (fun_table z y)))) ∧ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) ≤ (length (REFS (fun_table z x))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))]) [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((((proj_uN_0 (the ((proj_num__0 j)))) + v_n) :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc5 (admininstr_st5_TABLE_GET y)), (admininstr_sc5 (admininstr_st5_TABLE_SET x)), (admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))]"
	| table_init_trap :
		"(wf_tableinst (fun_table z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (eleminst_REFS (fun_elem z y)))) ∨ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (REFS (fun_table z x))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc6 (admininstr_st6_TABLE_INIT x y))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| table_init_zero :
		"((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (eleminst_REFS (fun_elem z y)))) ∧ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) ≤ (length (REFS (fun_table z x))))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc6 (admininstr_st6_TABLE_INIT x y))]) []"
	| table_init_succ :
		"((proj_uN_0 (the ((proj_num__0 i)))) < (length (eleminst_REFS (fun_elem z y)))) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 (v_n ≠ 0) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (eleminst_REFS (fun_elem z y)))) ∧ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) ≤ (length (REFS (fun_table z x))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc6 (admininstr_st6_TABLE_INIT x y))]) [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_ref ((eleminst_REFS (fun_elem z y)) ! (proj_uN_0 (the ((proj_num__0 i)))))), (admininstr_sc5 (admininstr_st5_TABLE_SET x)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 j)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc6 (admininstr_st6_TABLE_INIT x y))]"
	| load_num_trap :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((size (valtype_numtype nt)) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_LOAD nt None ao))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| load_num_val :
		"list_all (λ (iter :: byte). (wf_byte iter)) (nbytes_underscore nt c) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((size (valtype_numtype nt)) ≠ None) ⟹
		 ((nbytes_underscore nt c) = (list_slice (BYTES (fun_mem z (mk_uN 0))) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat)) :: nat))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_LOAD nt None ao))]) [(admininstr_sc1 (admininstr_st1_CONST nt c))]"
	| load_pack_trap :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_n :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| load_pack_val :
		"((size (valtype_Inn v_Inn)) ≠ None) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_n c) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((ibytes_underscore v_n c) = (list_slice (BYTES (fun_mem z (mk_uN 0))) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_n :: nat) div (8 :: nat)) :: nat))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao))]) [(admininstr_sc1 (admininstr_st1_CONST (numtype_Inn v_Inn) (mk_num__0 v_Inn (extend__underscore v_n (the ((size (valtype_Inn v_Inn)))) v_sx c))))]"
	| vload_oob :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((size valtype_V128) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((the ((size valtype_V128))) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 None ao))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| vload_val :
		"list_all (λ (iter :: byte). (wf_byte iter)) (vbytes_underscore V128 c) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((size valtype_V128) ≠ None) ⟹
		 ((vbytes_underscore V128 c) = (list_slice (BYTES (fun_mem z (mk_uN 0))) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((the ((size valtype_V128))) :: nat) div (8 :: nat)) :: nat))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 None ao))]) [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vload_shape_oob :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((v_M * v_N) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SHAPEX_underscore v_M v_N v_sx)) ao))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| vload_shape_val :
		"list_alli (λ k (j :: iN). list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_M j)) j_lst ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (map (λ (j :: iN). (mk_lane__2 v_Jnn (extend__underscore v_M (jsize v_Jnn) v_sx j))) j_lst))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ⟹
		 list_all (λ (j :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) (mk_lane__2 v_Jnn (extend__underscore v_M (jsize v_Jnn) v_sx j)))) j_lst ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 list_alli (λ k (j :: iN). ((ibytes_underscore v_M j) = (list_slice (BYTES (fun_mem z (mk_uN 0))) (((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((k * v_M) :: nat) div (8 :: nat)) :: nat)) (((v_M :: nat) div (8 :: nat)) :: nat)))) j_lst ⟹
		 ((jsize v_Jnn) = (v_M * 2)) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (map (λ (j :: iN). (mk_lane__2 v_Jnn (extend__underscore v_M (jsize v_Jnn) v_sx j))) j_lst))) ⟹
		 (v_N = (length j_lst)) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SHAPEX_underscore v_M v_N v_sx)) ao))]) [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vload_splat_oob :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_N :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SPLAT v_N)) ao))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| vload_splat_val :
		"list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_N j) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (repeat v_M (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 j)))))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) ⟹
		 (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 j)))) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((ibytes_underscore v_N j) = (list_slice (BYTES (fun_mem z (mk_uN 0))) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_N :: nat) div (8 :: nat)) :: nat))) ⟹
		 (v_N = (jsize v_Jnn)) ⟹
		 ((v_M :: nat) = ((128 :: nat) div (v_N :: nat))) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (repeat v_M (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 j)))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SPLAT v_N)) ao))]) [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vload_zero_oob :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_N :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (vloadop_ZERO v_N)) ao))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| vload_zero_val :
		"(wf_uN v_N j) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_N j) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 128 (extend__underscore v_N (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) U j)) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((ibytes_underscore v_N j) = (list_slice (BYTES (fun_mem z (mk_uN 0))) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_N :: nat) div (8 :: nat)) :: nat))) ⟹
		 (c = (extend__underscore v_N (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) U j)) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (vloadop_ZERO v_N)) ao))]) [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vload_lane_oob :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_N :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc6 (admininstr_st6_VLOAD_LANE V128 (mk_sz v_N) ao j))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| vload_lane_val :
		"list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_N k) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 128 (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (list_update_func (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c_1) (proj_uN_0 j) (λ (underscore_underscore :: lane_underscore). (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 k))))))) ⟹
		 list_all (λ (iter :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) iter)) (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c_1) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) ⟹
		 (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 k)))) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((ibytes_underscore v_N k) = (list_slice (BYTES (fun_mem z (mk_uN 0))) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_N :: nat) div (8 :: nat)) :: nat))) ⟹
		 (v_N = (jsize v_Jnn)) ⟹
		 ((v_M :: nat) = ((128 :: nat) div (v_N :: nat))) ⟹
		 (c = (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (list_update_func (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c_1) (proj_uN_0 j) (λ (underscore_underscore :: lane_underscore). (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 k))))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc6 (admininstr_st6_VLOAD_LANE V128 (mk_sz v_N) ao j))]) [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_read__memory_size :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 (((v_n * 64) * (Ki )) = (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step_read (mk_config z [(admininstr_sc6 admininstr_st6_MEMORY_SIZE)]) [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))))]"
	| memory_fill_trap :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_FILL)]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| memory_fill_zero :
		"((proj_num__0 i) ≠ None) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_FILL)]) []"
	| memory_fill_succ :
		"((proj_num__0 i) ≠ None) ⟹
		 (v_n ≠ 0) ⟹
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_FILL)]) [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc6 (admininstr_st6_STORE I32 (Some (mk_sz 8)) (memarg0 ))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc7 admininstr_st7_MEMORY_FILL)]"
	| memory_copy_trap :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0))))) ∨ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0)))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| memory_copy_zero :
		"((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (BYTES (fun_mem z (mk_uN 0))))) ∧ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) ≤ (length (BYTES (fun_mem z (mk_uN 0)))))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)]) []"
	| memory_copy_le :
		"((proj_num__0 j) ≠ None) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 (v_n ≠ 0) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (BYTES (fun_mem z (mk_uN 0))))) ∧ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) ≤ (length (BYTES (fun_mem z (mk_uN 0)))))) ⟹
		 ((proj_uN_0 (the ((proj_num__0 j)))) ≤ (proj_uN_0 (the ((proj_num__0 i))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)]) [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_LOAD I32 (Some (mk_loadop__0 Inn_I32 (mk_loadop_Inn (mk_sz 8) U))) (memarg0 ))), (admininstr_sc6 (admininstr_st6_STORE I32 (Some (mk_sz 8)) (memarg0 ))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 j)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)]"
	| memory_copy_gt :
		"((proj_num__0 j) ≠ None) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 j)))) > (proj_uN_0 (the ((proj_num__0 i))))) ⟹
		 (v_n ≠ 0) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (BYTES (fun_mem z (mk_uN 0))))) ∧ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) ≤ (length (BYTES (fun_mem z (mk_uN 0)))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)]) [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((((proj_uN_0 (the ((proj_num__0 j)))) + v_n) :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc6 (admininstr_st6_LOAD I32 (Some (mk_loadop__0 Inn_I32 (mk_loadop_Inn (mk_sz 8) U))) (memarg0 ))), (admininstr_sc6 (admininstr_st6_STORE I32 (Some (mk_sz 8)) (memarg0 ))), (admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)]"
	| memory_init_trap :
		"(wf_datainst (fun_data z x)) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (datainst_BYTES (fun_data z x)))) ∨ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0)))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 (admininstr_st7_MEMORY_INIT x))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| memory_init_zero :
		"((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (datainst_BYTES (fun_data z x)))) ∧ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) ≤ (length (BYTES (fun_mem z (mk_uN 0)))))) ⟹
		 (v_n = 0) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 (admininstr_st7_MEMORY_INIT x))]) []"
	| memory_init_succ :
		"((proj_uN_0 (the ((proj_num__0 i)))) < (length (datainst_BYTES (fun_data z x)))) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_num__0 j) ≠ None) ⟹
		 (v_n ≠ 0) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) ≤ (length (datainst_BYTES (fun_data z x)))) ∧ (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) ≤ (length (BYTES (fun_mem z (mk_uN 0)))))) ⟹
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 (admininstr_st7_MEMORY_INIT x))]) [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (proj_byte_0 ((datainst_BYTES (fun_data z x)) ! (proj_uN_0 (the ((proj_num__0 i)))))))))), (admininstr_sc6 (admininstr_st6_STORE I32 (Some (mk_sz 8)) (memarg0 ))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 j)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc7 (admininstr_st7_MEMORY_INIT x))]"

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.77 *)
inductive Step :: "config ⇒ config ⇒ bool" where
	  pure :
		"(Step_pure admininstr_lst admininstr'_lst) ⟹
		 Step (mk_config z admininstr_lst) (mk_config z admininstr'_lst)"
	| read :
		"(wf_config (mk_config z admininstr_lst)) ⟹
		 (Step_read (mk_config z admininstr_lst) admininstr'_lst) ⟹
		 Step (mk_config z admininstr_lst) (mk_config z admininstr'_lst)"
	| ctxt_label :
		"(wf_config (mk_config z admininstr_lst)) ⟹
		 (wf_config (mk_config z' admininstr'_lst)) ⟹
		 (Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) ⟹
		 Step (mk_config z [(admininstr_sc8 (LABEL_underscore v_n instr_0_lst admininstr_lst))]) (mk_config z' [(admininstr_sc8 (LABEL_underscore v_n instr_0_lst admininstr'_lst))])"
	| ctxt_frame :
		"(wf_config (mk_config (mk_state s f') admininstr_lst)) ⟹
		 (wf_config (mk_config (mk_state s' f'') admininstr'_lst)) ⟹
		 (Step (mk_config (mk_state s f') admininstr_lst) (mk_config (mk_state s' f'') admininstr'_lst)) ⟹
		 Step (mk_config (mk_state s f) [(admininstr_sc8 (FRAME_underscore v_n f' admininstr_lst))]) (mk_config (mk_state s' f) [(admininstr_sc8 (FRAME_underscore v_n f'' admininstr'_lst))])"
	| ctxt_instrs :
		"(wf_config (mk_config z admininstr_lst)) ⟹
		 (wf_config (mk_config z' admininstr'_lst)) ⟹
		 (Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) ⟹
		 ((val_lst ≠ []) ∨ (admininstr_1_lst ≠ [])) ⟹
		 Step (mk_config z ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ (admininstr_lst @ admininstr_1_lst))) (mk_config z' ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ (admininstr'_lst @ admininstr_1_lst)))"
	| Step__local_set :
		"Step (mk_config z [(admininstr_val v_val), (admininstr_sc4 (admininstr_st4_LOCAL_SET x))]) (mk_config (with_local z x v_val) [])"
	| Step__global_set :
		"Step (mk_config z [(admininstr_val v_val), (admininstr_sc5 (admininstr_st5_GLOBAL_SET x))]) (mk_config (with_global z x v_val) [])"
	| table_set_trap :
		"(wf_tableinst (fun_table z x)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i)))) ≥ (length (REFS (fun_table z x)))) ⟹
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_ref v_ref), (admininstr_sc5 (admininstr_st5_TABLE_SET x))]) (mk_config z [(admininstr_sc7 admininstr_st7_TRAP)])"
	| table_set_val :
		"((proj_num__0 i) ≠ None) ⟹
		 (wf_tableinst (fun_table z x)) ⟹
		 ((proj_uN_0 (the ((proj_num__0 i)))) < (length (REFS (fun_table z x)))) ⟹
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_ref v_ref), (admininstr_sc5 (admininstr_st5_TABLE_SET x))]) (mk_config (with_table z x (proj_uN_0 (the ((proj_num__0 i)))) v_ref) [])"
	| table_grow_succeed :
		"(fun_growtable (fun_table z x) v_n v_ref var_0) ⟹
		 (var_0 ≠ None) ⟹
		 (wf_tableinst (the (var_0))) ⟹
		 (wf_tableinst (fun_table z x)) ⟹
		 ((the (var_0)) = ti) ⟹
		 Step (mk_config z [(admininstr_ref v_ref), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_GROW x))]) (mk_config (with_tableinst z x ti) [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (length (REFS (fun_table z x)))))))])"
	| table_grow_fail :
		"(fun_inv_signed_underscore 32 (0 - (1 :: nat)) var_0) ⟹
		 Step (mk_config z [(admininstr_ref v_ref), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_GROW x))]) (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN var_0))))])"
	| Step__elem_drop :
		"Step (mk_config z [(admininstr_sc6 (admininstr_st6_ELEM_DROP x))]) (mk_config (with_elem z x []) [])"
	| store_num_trap :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((size (valtype_numtype nt)) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST nt c)), (admininstr_sc6 (admininstr_st6_STORE nt None ao))]) (mk_config z [(admininstr_sc7 admininstr_st7_TRAP)])"
	| store_num_val :
		"((proj_num__0 i) ≠ None) ⟹
		 ((size (valtype_numtype nt)) ≠ None) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (nbytes_underscore nt c) ⟹
		 (b_lst = (nbytes_underscore nt c)) ⟹
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST nt c)), (admininstr_sc6 (admininstr_st6_STORE nt None ao))]) (mk_config (with_mem z (mk_uN 0) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat)) :: nat) b_lst) [])"
	| store_pack_trap :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_n :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST (numtype_Inn v_Inn) c)), (admininstr_sc6 (admininstr_st6_STORE (numtype_Inn v_Inn) (Some (mk_sz v_n)) ao))]) (mk_config z [(admininstr_sc7 admininstr_st7_TRAP)])"
	| store_pack_val :
		"((proj_num__0 i) ≠ None) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_n (wrap__underscore (the ((size (valtype_Inn v_Inn)))) v_n (the ((proj_num__0 c))))) ⟹
		 ((size (valtype_Inn v_Inn)) ≠ None) ⟹
		 ((proj_num__0 c) ≠ None) ⟹
		 (wf_uN v_n (wrap__underscore (the ((size (valtype_Inn v_Inn)))) v_n (the ((proj_num__0 c))))) ⟹
		 (b_lst = (ibytes_underscore v_n (wrap__underscore (the ((size (valtype_Inn v_Inn)))) v_n (the ((proj_num__0 c)))))) ⟹
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST (numtype_Inn v_Inn) c)), (admininstr_sc6 (admininstr_st6_STORE (numtype_Inn v_Inn) (Some (mk_sz v_n)) ao))]) (mk_config (with_mem z (mk_uN 0) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_n :: nat) div (8 :: nat)) :: nat) b_lst) [])"
	| vstore_oob :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((size valtype_V128) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((the ((size valtype_V128))) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc6 (admininstr_st6_VSTORE V128 ao))]) (mk_config z [(admininstr_sc7 admininstr_st7_TRAP)])"
	| vstore_val :
		"((proj_num__0 i) ≠ None) ⟹
		 ((size valtype_V128) ≠ None) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (vbytes_underscore V128 c) ⟹
		 (b_lst = (vbytes_underscore V128 c)) ⟹
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc6 (admininstr_st6_VSTORE V128 ao))]) (mk_config (with_mem z (mk_uN 0) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((the ((size valtype_V128))) :: nat) div (8 :: nat)) :: nat) b_lst) [])"
	| vstore_lane_oob :
		"(wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((proj_num__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + v_N) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz v_N) ao j))]) (mk_config z [(admininstr_sc7 admininstr_st7_TRAP)])"
	| vstore_lane_val :
		"((proj_num__0 i) ≠ None) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_N (mk_uN (proj_uN_0 (the ((proj_lane__2 ((lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c) ! (proj_uN_0 j)))))))) ⟹
		 ((proj_lane__2 ((lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c) ! (proj_uN_0 j))) ≠ None) ⟹
		 ((proj_uN_0 j) < (length (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c))) ⟹
		 (wf_uN v_N (mk_uN (proj_uN_0 (the ((proj_lane__2 ((lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c) ! (proj_uN_0 j)))))))) ⟹
		 (v_N = (jsize v_Jnn)) ⟹
		 ((v_M :: nat) = ((128 :: nat) div (v_N :: nat))) ⟹
		 (b_lst = (ibytes_underscore v_N (mk_uN (proj_uN_0 (the ((proj_lane__2 ((lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c) ! (proj_uN_0 j))))))))) ⟹
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz v_N) ao j))]) (mk_config (with_mem z (mk_uN 0) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_N :: nat) div (8 :: nat)) :: nat) b_lst) [])"
	| memory_grow_succeed :
		"(fun_growmemory (fun_mem z (mk_uN 0)) v_n var_0) ⟹
		 (var_0 ≠ None) ⟹
		 (wf_meminst (the (var_0))) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 ((the (var_0)) = mi) ⟹
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_GROW)]) (mk_config (with_meminst z (mk_uN 0) mi) [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((((length (BYTES (fun_mem z (mk_uN 0)))) :: nat) div ((64 * (Ki )) :: nat)) :: nat)))))])"
	| memory_grow_fail :
		"(fun_inv_signed_underscore 32 (0 - (1 :: nat)) var_0) ⟹
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_GROW)]) (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN var_0))))])"
	| Step__data_drop :
		"Step (mk_config z [(admininstr_sc7 (admininstr_st7_DATA_DROP x))]) (mk_config (with_data z x []) [])"

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:8.1-8.77 *)
inductive Steps :: "config ⇒ config ⇒ bool" where
	  Steps__refl :
		"Steps (mk_config z admininstr_lst) (mk_config z admininstr_lst)"
	| trans :
		"(wf_config (mk_config z admininstr_lst)) ⟹
		 (wf_config (mk_config z' admininstr'_lst)) ⟹
		 (wf_config (mk_config z'' admininstr''_lst)) ⟹
		 (Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) ⟹
		 (Steps (mk_config z' admininstr'_lst) (mk_config z'' admininstr''_lst)) ⟹
		 Steps (mk_config z admininstr_lst) (mk_config z'' admininstr''_lst)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:29.1-29.83 *)
inductive Eval_expr :: "state ⇒ expr ⇒ state ⇒ (val list) ⇒ bool" where
	  mk_Eval_expr :
		"(wf_config (mk_config z (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))) ⟹
		 (wf_config (mk_config z' (map (λ (v_val :: val). (admininstr_val v_val)) val_lst))) ⟹
		 (Steps (mk_config z (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst)) (mk_config z' (map (λ (v_val :: val). (admininstr_val v_val)) val_lst))) ⟹
		 Eval_expr z instr_lst z' val_lst"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:5.1-5.36 *)
inductive fun_funcs :: "(externaddr list) ⇒ (funcaddr list) ⇒ bool" where
	  fun_funcs_case_0 :
		"fun_funcs [] []"
	| fun_funcs_case_1 :
		"(fun_funcs externaddr'_lst var_0) ⟹
		 fun_funcs ([(externaddr_FUNC fa)] @ externaddr'_lst) ([fa] @ var_0)"
	| fun_funcs_case_2 :
		"(fun_funcs externaddr'_lst var_0) ⟹
		 fun_funcs ([v_externaddr] @ externaddr'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:11.1-11.40 *)
inductive fun_globals :: "(externaddr list) ⇒ (globaladdr list) ⇒ bool" where
	  fun_globals_case_0 :
		"fun_globals [] []"
	| fun_globals_case_1 :
		"(fun_globals externaddr'_lst var_0) ⟹
		 fun_globals ([(externaddr_GLOBAL ga)] @ externaddr'_lst) ([ga] @ var_0)"
	| fun_globals_case_2 :
		"(fun_globals externaddr'_lst var_0) ⟹
		 fun_globals ([v_externaddr] @ externaddr'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:17.1-17.38 *)
inductive fun_tables :: "(externaddr list) ⇒ (tableaddr list) ⇒ bool" where
	  fun_tables_case_0 :
		"fun_tables [] []"
	| fun_tables_case_1 :
		"(fun_tables externaddr'_lst var_0) ⟹
		 fun_tables ([(externaddr_TABLE ta)] @ externaddr'_lst) ([ta] @ var_0)"
	| fun_tables_case_2 :
		"(fun_tables externaddr'_lst var_0) ⟹
		 fun_tables ([v_externaddr] @ externaddr'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:23.1-23.34 *)
inductive fun_mems :: "(externaddr list) ⇒ (memaddr list) ⇒ bool" where
	  fun_mems_case_0 :
		"fun_mems [] []"
	| fun_mems_case_1 :
		"(fun_mems externaddr'_lst var_0) ⟹
		 fun_mems ([(externaddr_MEM ma)] @ externaddr'_lst) ([ma] @ var_0)"
	| fun_mems_case_2 :
		"(fun_mems externaddr'_lst var_0) ⟹
		 fun_mems ([v_externaddr] @ externaddr'_lst) var_0"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:36.6-36.16 *)
inductive fun_allocfunc :: "store ⇒ moduleinst ⇒ func ⇒ (store * funcaddr) ⇒ bool" where
	  fun_allocfunc_case_0 :
		"((proj_uN_0 x) < (length (TYPES v_moduleinst))) ⟹
		 (wf_funcinst ⦇ funcinst_TYPE = ((TYPES v_moduleinst) ! (proj_uN_0 x)), funcinst_MODULE = v_moduleinst, CODE = v_func ⦈) ⟹
		 (wf_func (func_FUNC x local_lst v_expr)) ⟹
		 (fi = ⦇ funcinst_TYPE = ((TYPES v_moduleinst) ! (proj_uN_0 x)), funcinst_MODULE = v_moduleinst, CODE = v_func ⦈) ⟹
		 (v_func = (func_FUNC x local_lst v_expr)) ⟹
		 fun_allocfunc s v_moduleinst v_func ((s ⦇ store_FUNCS := ((store_FUNCS s) @ [fi])  ⦈), (length (store_FUNCS s)))"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:41.1-41.63 *)
inductive fun_allocfuncs :: "store ⇒ moduleinst ⇒ (func list) ⇒ (store * (funcaddr list)) ⇒ bool" where
	  fun_allocfuncs_case_0 :
		"fun_allocfuncs s v_moduleinst [] (s, [])"
	| fun_allocfuncs_case_1 :
		"(fun_allocfuncs s_1 v_moduleinst func'_lst var_1) ⟹
		 (fun_allocfunc s v_moduleinst v_func var_0) ⟹
		 (wf_store s_1) ⟹
		 (wf_store (fst var_0)) ⟹
		 (wf_store (fst var_1)) ⟹
		 ((s_1, fa) = var_0) ⟹
		 ((s_2, fa'_lst) = var_1) ⟹
		 fun_allocfuncs s v_moduleinst ([v_func] @ func'_lst) (s_2, ([fa] @ fa'_lst))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:47.6-47.18 *)
inductive fun_allocglobal :: "store ⇒ globaltype ⇒ val ⇒ (store * globaladdr) ⇒ bool" where
	  fun_allocglobal_case_0 :
		"(wf_globalinst ⦇ globalinst_TYPE = v_globaltype, VALUE = v_val ⦈) ⟹
		 (gi = ⦇ globalinst_TYPE = v_globaltype, VALUE = v_val ⦈) ⟹
		 fun_allocglobal s v_globaltype v_val ((s ⦇ store_GLOBALS := ((store_GLOBALS s) @ [gi])  ⦈), (length (store_GLOBALS s)))"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:51.1-51.67 *)
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

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:57.6-57.17 *)
inductive fun_alloctable :: "store ⇒ tabletype ⇒ (store * tableaddr) ⇒ bool" where
	  fun_alloctable_case_0 :
		"(wf_tableinst ⦇ tableinst_TYPE = (mk_tabletype (mk_limits i j_opt) rt), REFS = (repeat (proj_uN_0 i) (ref_REF_NULL rt)) ⦈) ⟹
		 (ti = ⦇ tableinst_TYPE = (mk_tabletype (mk_limits i j_opt) rt), REFS = (repeat (proj_uN_0 i) (ref_REF_NULL rt)) ⦈) ⟹
		 fun_alloctable s (mk_tabletype (mk_limits i j_opt) rt) ((s ⦇ store_TABLES := ((store_TABLES s) @ [ti])  ⦈), (length (store_TABLES s)))"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:61.1-61.58 *)
inductive fun_alloctables :: "store ⇒ (tabletype list) ⇒ (store * (tableaddr list)) ⇒ bool" where
	  fun_alloctables_case_0 :
		"fun_alloctables s [] (s, [])"
	| fun_alloctables_case_1 :
		"(fun_alloctables s_1 tabletype'_lst var_1) ⟹
		 (fun_alloctable s v_tabletype var_0) ⟹
		 (wf_store s_1) ⟹
		 (wf_store (fst var_0)) ⟹
		 (wf_store (fst var_1)) ⟹
		 ((s_1, ta) = var_0) ⟹
		 ((s_2, ta'_lst) = var_1) ⟹
		 fun_alloctables s ([v_tabletype] @ tabletype'_lst) (s_2, ([ta] @ ta'_lst))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:67.6-67.15 *)
inductive fun_allocmem :: "store ⇒ memtype ⇒ (store * memaddr) ⇒ bool" where
	  fun_allocmem_case_0 :
		"(wf_meminst ⦇ meminst_TYPE = (PAGE (mk_limits i j_opt)), BYTES = (repeat ((proj_uN_0 i) * (64 * (Ki ))) (mk_byte 0)) ⦈) ⟹
		 (mi = ⦇ meminst_TYPE = (PAGE (mk_limits i j_opt)), BYTES = (repeat ((proj_uN_0 i) * (64 * (Ki ))) (mk_byte 0)) ⦈) ⟹
		 fun_allocmem s (PAGE (mk_limits i j_opt)) ((s ⦇ store_MEMS := ((store_MEMS s) @ [mi])  ⦈), (length (store_MEMS s)))"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:71.1-71.52 *)
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

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:77.6-77.16 *)
inductive fun_allocelem :: "store ⇒ reftype ⇒ (ref list) ⇒ (store * elemaddr) ⇒ bool" where
	  fun_allocelem_case_0 :
		"(ei = ⦇ eleminst_TYPE = rt, eleminst_REFS = ref_lst ⦈) ⟹
		 fun_allocelem s rt ref_lst ((s ⦇ store_ELEMS := ((store_ELEMS s) @ [ei])  ⦈), (length (store_ELEMS s)))"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:81.1-81.63 *)
inductive fun_allocelems :: "store ⇒ (reftype list) ⇒ ((ref list) list) ⇒ (store * (elemaddr list)) ⇒ bool" where
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

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:87.6-87.16 *)
inductive fun_allocdata :: "store ⇒ (byte list) ⇒ (store * dataaddr) ⇒ bool" where
	  fun_allocdata_case_0 :
		"(wf_datainst ⦇ datainst_BYTES = byte_lst ⦈) ⟹
		 (di = ⦇ datainst_BYTES = byte_lst ⦈) ⟹
		 fun_allocdata s byte_lst ((s ⦇ store_DATAS := ((store_DATAS s) @ [di])  ⦈), (length (store_DATAS s)))"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:91.1-91.54 *)
inductive fun_allocdatas :: "store ⇒ ((byte list) list) ⇒ (store * (dataaddr list)) ⇒ bool" where
	  fun_allocdatas_case_0 :
		"fun_allocdatas s [] (s, [])"
	| fun_allocdatas_case_1 :
		"(fun_allocdatas s_1 byte'_lst_lst var_1) ⟹
		 (fun_allocdata s byte_lst var_0) ⟹
		 (wf_store s_1) ⟹
		 (wf_store (fst var_0)) ⟹
		 (wf_store (fst var_1)) ⟹
		 ((s_1, da) = var_0) ⟹
		 ((s_2, da'_lst) = var_1) ⟹
		 fun_allocdatas s ([byte_lst] @ byte'_lst_lst) (s_2, ([da] @ da'_lst))"

(* Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:100.1-100.83 *)
function (sequential) instexport :: "(funcaddr list) ⇒ (globaladdr list) ⇒ (tableaddr list) ⇒ (memaddr list) ⇒ export ⇒ exportinst" where
		  "instexport fa_lst ga_lst ta_lst ma_lst (EXPORT v_name (externidx_FUNC x)) = ⦇ NAME = v_name, ADDR = (externaddr_FUNC (fa_lst ! (proj_uN_0 x))) ⦈"
		| "instexport fa_lst ga_lst ta_lst ma_lst (EXPORT v_name (externidx_GLOBAL x)) = ⦇ NAME = v_name, ADDR = (externaddr_GLOBAL (ga_lst ! (proj_uN_0 x))) ⦈"
		| "instexport fa_lst ga_lst ta_lst ma_lst (EXPORT v_name (externidx_TABLE x)) = ⦇ NAME = v_name, ADDR = (externaddr_TABLE (ta_lst ! (proj_uN_0 x))) ⦈"
		| "instexport fa_lst ga_lst ta_lst ma_lst (EXPORT v_name (externidx_MEM x)) = ⦇ NAME = v_name, ADDR = (externaddr_MEM (ma_lst ! (proj_uN_0 x))) ⦈"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:107.6-107.18 *)
inductive fun_allocmodule :: "store ⇒ module ⇒ (externaddr list) ⇒ (val list) ⇒ ((ref list) list) ⇒ (store * moduleinst) ⇒ bool" where
	  fun_allocmodule_case_0 :
		"(fun_mems externaddr_lst var_9) ⟹
		 (fun_tables externaddr_lst var_8) ⟹
		 (fun_globals externaddr_lst var_7) ⟹
		 (fun_funcs externaddr_lst var_6) ⟹
		 (fun_allocdatas s_5 byte_lst_lst var_5) ⟹
		 (fun_allocelems s_4 rt_lst ref_lst_lst var_4) ⟹
		 (fun_allocmems s_3 memtype_lst var_3) ⟹
		 (fun_alloctables s_2 tabletype_lst var_2) ⟹
		 (fun_allocglobals s_1 globaltype_lst val_lst var_1) ⟹
		 (fun_allocfuncs s v_moduleinst func_lst var_0) ⟹
		 (wf_store s_1) ⟹
		 (wf_store s_2) ⟹
		 (wf_store s_3) ⟹
		 (wf_store s_4) ⟹
		 (wf_store s_5) ⟹
		 list_all (λ (v_export :: export). (wf_exportinst (instexport (fa_ex_lst @ fa_lst) (ga_ex_lst @ ga_lst) (ta_ex_lst @ ta_lst) (ma_ex_lst @ ma_lst) v_export))) export_lst ⟹
		 (wf_store (fst var_0)) ⟹
		 (wf_store (fst var_1)) ⟹
		 (wf_store (fst var_2)) ⟹
		 (wf_store (fst var_3)) ⟹
		 (wf_store (fst var_4)) ⟹
		 (wf_store (fst var_5)) ⟹
		 (wf_module (MODULE (map (λ (ft :: functype). (res_TYPE ft)) ft_lst) import_lst func_lst (list_zipWith (λ (expr_1 :: expr) (v_globaltype :: globaltype). (global_GLOBAL v_globaltype expr_1)) expr_1_lst globaltype_lst) (map (λ (v_tabletype :: tabletype). (table_TABLE v_tabletype)) tabletype_lst) (map (λ (v_memtype :: memtype). (MEMORY v_memtype)) memtype_lst) (list_map3 (λ (v_elemmode :: elemmode) (expr_2_lst :: (expr list)) (rt :: reftype). (ELEM rt expr_2_lst v_elemmode)) elemmode_lst expr_2_lst_lst rt_lst) (list_zipWith (λ (byte_lst :: (byte list)) (v_datamode :: datamode). (DATA byte_lst v_datamode)) byte_lst_lst datamode_lst) start_opt export_lst)) ⟹
		 (wf_moduleinst ⦇ TYPES = ft_lst, FUNCS = (fa_ex_lst @ fa_lst), GLOBALS = (ga_ex_lst @ ga_lst), TABLES = (ta_ex_lst @ ta_lst), MEMS = (ma_ex_lst @ ma_lst), ELEMS = ea_lst, DATAS = da_lst, EXPORTS = xi_lst ⦈) ⟹
		 (v_module = (MODULE (map (λ (ft :: functype). (res_TYPE ft)) ft_lst) import_lst func_lst (list_zipWith (λ (expr_1 :: expr) (v_globaltype :: globaltype). (global_GLOBAL v_globaltype expr_1)) expr_1_lst globaltype_lst) (map (λ (v_tabletype :: tabletype). (table_TABLE v_tabletype)) tabletype_lst) (map (λ (v_memtype :: memtype). (MEMORY v_memtype)) memtype_lst) (list_map3 (λ (v_elemmode :: elemmode) (expr_2_lst :: (expr list)) (rt :: reftype). (ELEM rt expr_2_lst v_elemmode)) elemmode_lst expr_2_lst_lst rt_lst) (list_zipWith (λ (byte_lst :: (byte list)) (v_datamode :: datamode). (DATA byte_lst v_datamode)) byte_lst_lst datamode_lst) start_opt export_lst)) ⟹
		 (fa_ex_lst = var_6) ⟹
		 (ga_ex_lst = var_7) ⟹
		 (ta_ex_lst = var_8) ⟹
		 (ma_ex_lst = var_9) ⟹
		 (fa_lst = (mkseq (λ i_func. ((length (store_FUNCS s)) + i_func)) n_func)) ⟹
		 (ga_lst = (mkseq (λ i_global. ((length (store_GLOBALS s)) + i_global)) n_global)) ⟹
		 (ta_lst = (mkseq (λ i_table. ((length (store_TABLES s)) + i_table)) n_table)) ⟹
		 (ma_lst = (mkseq (λ i_mem. ((length (store_MEMS s)) + i_mem)) n_mem)) ⟹
		 (ea_lst = (mkseq (λ i_elem. ((length (store_ELEMS s)) + i_elem)) n_elem)) ⟹
		 (da_lst = (mkseq (λ i_data. ((length (store_DATAS s)) + i_data)) n_data)) ⟹
		 (xi_lst = (map (λ (v_export :: export). (instexport (fa_ex_lst @ fa_lst) (ga_ex_lst @ ga_lst) (ta_ex_lst @ ta_lst) (ma_ex_lst @ ma_lst) v_export)) export_lst)) ⟹
		 (v_moduleinst = ⦇ TYPES = ft_lst, FUNCS = (fa_ex_lst @ fa_lst), GLOBALS = (ga_ex_lst @ ga_lst), TABLES = (ta_ex_lst @ ta_lst), MEMS = (ma_ex_lst @ ma_lst), ELEMS = ea_lst, DATAS = da_lst, EXPORTS = xi_lst ⦈) ⟹
		 ((s_1, fa_lst) = var_0) ⟹
		 ((s_2, ga_lst) = var_1) ⟹
		 ((s_3, ta_lst) = var_2) ⟹
		 ((s_4, ma_lst) = var_3) ⟹
		 ((s_5, ea_lst) = var_4) ⟹
		 ((s_6, da_lst) = var_5) ⟹
		 fun_allocmodule s v_module externaddr_lst val_lst ref_lst_lst (s_6, v_moduleinst)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:154.6-154.14 *)
inductive fun_runelem :: "elem ⇒ idx ⇒ (instr list) ⇒ bool" where
	  fun_runelem_case_0 :
		"fun_runelem (ELEM v_reftype expr_lst PASSIVE) i []"
	| fun_runelem_case_1 :
		"fun_runelem (ELEM v_reftype expr_lst DECLARE) i [(instr_sc5 (ELEM_DROP i))]"
	| fun_runelem_case_2 :
		"(v_n = (length expr_lst)) ⟹
		 fun_runelem (ELEM v_reftype expr_lst (ACTIVE x instr_lst)) i (instr_lst @ [(instr_sc1 (res_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0)))), (instr_sc1 (res_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (instr_sc5 (TABLE_INIT x i)), (instr_sc5 (ELEM_DROP i))])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:161.6-161.14 *)
inductive fun_rundata :: "data ⇒ idx ⇒ (instr list) ⇒ bool" where
	  fun_rundata_case_0 :
		"fun_rundata (DATA byte_lst datamode_PASSIVE) i []"
	| fun_rundata_case_1 :
		"(v_n = (length byte_lst)) ⟹
		 fun_rundata (DATA byte_lst (datamode_ACTIVE (mk_uN 0) instr_lst)) i (instr_lst @ [(instr_sc1 (res_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0)))), (instr_sc1 (res_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (instr_sc7 (MEMORY_INIT i)), (instr_sc7 (DATA_DROP i))])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:167.6-167.18 *)
inductive fun_instantiate :: "store ⇒ module ⇒ (externaddr list) ⇒ config ⇒ bool" where
	  fun_instantiate_case_0 :
		"(fun_globals externaddr_lst var_4) ⟹
		 (fun_funcs externaddr_lst var_3) ⟹
		 (j < (length data_lst)) ⟹
		 (fun_rundata (data_lst ! j) (mk_uN j) var_2) ⟹
		 (i < (length elem_lst)) ⟹
		 (fun_runelem (elem_lst ! i) (mk_uN i) var_1) ⟹
		 (fun_allocmodule s v_module externaddr_lst val_lst ref_lst_lst var_0) ⟹
		 (wf_state z) ⟹
		 list_all (λ (v_val :: val). (wf_val v_val)) val_lst ⟹
		 (wf_store (fst var_0)) ⟹
		 (wf_moduleinst (snd var_0)) ⟹
		 list_all (λ (iter :: instr). (wf_instr iter)) (concat_underscore  (mkseq (λ i. var_1) n_E)) ⟹
		 list_all (λ (iter :: instr). (wf_instr iter)) var_1 ⟹
		 list_all (λ (iter :: instr). (wf_instr iter)) (concat_underscore  (mkseq (λ j. var_2) n_D)) ⟹
		 list_all (λ (iter :: instr). (wf_instr iter)) var_2 ⟹
		 (wf_module (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)) ⟹
		 ((length expr_G_lst) = (length globaltype_lst)) ⟹
		 list_all2 (λ (expr_G :: expr) (v_globaltype :: globaltype). (wf_global (global_GLOBAL v_globaltype expr_G))) expr_G_lst globaltype_lst ⟹
		 ((length elemmode_lst) = (length expr_E_lst_lst)) ⟹
		 ((length elemmode_lst) = (length reftype_lst)) ⟹
		 list_all3 (λ (v_elemmode :: elemmode) (expr_E_lst :: (expr list)) (v_reftype :: reftype). (wf_elem (ELEM v_reftype expr_E_lst v_elemmode))) elemmode_lst expr_E_lst_lst reftype_lst ⟹
		 list_all (λ (x :: idx). (wf_start (START x))) (option_to_list x_opt) ⟹
		 (wf_moduleinst ⦇ TYPES = functype_lst, FUNCS = (var_3 @ (mkseq (λ i_F. ((length (store_FUNCS s)) + i_F)) n_F)), GLOBALS = var_4, TABLES = [], MEMS = [], ELEMS = [], DATAS = [], EXPORTS = [] ⦈) ⟹
		 (wf_frame ⦇ LOCALS = [], frame_MODULE = moduleinst_init ⦈) ⟹
		 (wf_state (mk_state s f_init)) ⟹
		 (wf_frame ⦇ LOCALS = [], frame_MODULE = v_moduleinst ⦈) ⟹
		 (wf_uN 32 (mk_uN i)) ⟹
		 (wf_uN 32 (mk_uN j)) ⟹
		 (v_module = (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)) ⟹
		 (type_lst = (map (λ (v_functype :: functype). (res_TYPE v_functype)) functype_lst)) ⟹
		 (global_lst = (list_zipWith (λ (expr_G :: expr) (v_globaltype :: globaltype). (global_GLOBAL v_globaltype expr_G)) expr_G_lst globaltype_lst)) ⟹
		 (elem_lst = (list_map3 (λ (v_elemmode :: elemmode) (expr_E_lst :: (expr list)) (v_reftype :: reftype). (ELEM v_reftype expr_E_lst v_elemmode)) elemmode_lst expr_E_lst_lst reftype_lst)) ⟹
		 (start_opt = (map_option (λ (x :: idx). (START x)) x_opt)) ⟹
		 (n_F = (length func_lst)) ⟹
		 (n_E = (length elem_lst)) ⟹
		 (n_D = (length data_lst)) ⟹
		 (moduleinst_init = ⦇ TYPES = functype_lst, FUNCS = (var_3 @ (mkseq (λ i_F. ((length (store_FUNCS s)) + i_F)) n_F)), GLOBALS = var_4, TABLES = [], MEMS = [], ELEMS = [], DATAS = [], EXPORTS = [] ⦈) ⟹
		 (f_init = ⦇ LOCALS = [], frame_MODULE = moduleinst_init ⦈) ⟹
		 (z = (mk_state s f_init)) ⟹
		 ((length expr_G_lst) = (length val_lst)) ⟹
		 list_all2 (λ (expr_G :: expr) (v_val :: val). (Eval_expr z expr_G z [v_val])) expr_G_lst val_lst ⟹
		 ((length expr_E_lst_lst) = (length ref_lst_lst)) ⟹
		 list_all2 (λ (expr_E_lst :: (expr list)) (ref_lst :: (ref list)). ((length expr_E_lst) = (length ref_lst))) expr_E_lst_lst ref_lst_lst ⟹
		 list_all2 (λ (expr_E_lst :: (expr list)) (ref_lst :: (ref list)). list_all2 (λ (expr_E :: expr) (v_ref :: ref). (Eval_expr z expr_E z [(val_ref v_ref)])) expr_E_lst ref_lst) expr_E_lst_lst ref_lst_lst ⟹
		 ((s', v_moduleinst) = var_0) ⟹
		 (f = ⦇ LOCALS = [], frame_MODULE = v_moduleinst ⦈) ⟹
		 (instr_E_lst = (concat_underscore  (mkseq (λ i. var_1) n_E))) ⟹
		 (instr_D_lst = (concat_underscore  (mkseq (λ j. var_2) n_D))) ⟹
		 fun_instantiate s v_module externaddr_lst (mk_config (mk_state s' f) ((map (λ (instr_E :: instr). (admininstr_instr instr_E)) instr_E_lst) @ ((map (λ (instr_D :: instr). (admininstr_instr instr_D)) instr_D_lst) @ (option_to_list (map_option (λ (x :: idx). (admininstr_sc1 (admininstr_st1_CALL x))) x_opt)))))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:196.6-196.13 *)
inductive fun_invoke :: "store ⇒ funcaddr ⇒ (val list) ⇒ config ⇒ bool" where
	  fun_invoke_case_0 :
		"list_all (λ (iter :: funcinst). (wf_funcinst iter)) (fun_funcinst (mk_state s f)) ⟹
		 (wf_frame ⦇ LOCALS = [], frame_MODULE = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], EXPORTS = [] ⦈ ⦈) ⟹
		 (wf_state (mk_state s f)) ⟹
		 (f = ⦇ LOCALS = [], frame_MODULE = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], EXPORTS = [] ⦈ ⦈) ⟹
		 (fa < (length (fun_funcinst (mk_state s f)))) ⟹
		 ((funcinst_TYPE ((fun_funcinst (mk_state s f)) ! fa)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) ⟹
		 (v_n = (length val_lst)) ⟹
		 fun_invoke s fa val_lst (mk_config (mk_state s f) ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc7 (CALL_ADDR fa))]))"

(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:849.1-849.43 *)
type_synonym startopt = "(start list)"

(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:884.1-884.29 *)
type_synonym code = "((local list) * expr)"

(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:915.1-915.33 *)
type_synonym nopt = "(u32 list)"

end
