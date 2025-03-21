theory SpecTecNumerics

imports Main

begin

datatype bit = Bit0 | Bit1
type_synonym bits = "bit list"

primrec bit_to_nat :: "bit \<Rightarrow> nat" where
  "bit_to_nat Bit0 = 0" |
  "bit_to_nat Bit1 = 1"

definition sum_list :: "nat list \<Rightarrow> nat" where
  "sum_list xs \<equiv> fold (+) xs 0"

inductive ibits :: "nat \<Rightarrow> nat \<Rightarrow> bits \<Rightarrow> bool" where
  ibits_I: "\<lbrakk> length bs = N
            ; N > 0
            ; i = sum_list (map2 (\<lambda> b n. 2^n * bit_to_nat b) bs (rev [0 ..< N]))
            \<rbrakk> \<Longrightarrow> ibits N i bs"

fun nat_to_rev_bits :: "nat \<Rightarrow> bits" where
  "nat_to_rev_bits 0 = [Bit0]" |
  "nat_to_rev_bits (Suc 0) = [Bit1]" |
  "nat_to_rev_bits n = (if n mod 2 = 0 then Bit0 else Bit1) # nat_to_rev_bits (n div 2)"

fun ibits_f :: "nat \<Rightarrow> nat \<Rightarrow> bits option" where
  "ibits_f N i = (if i \<ge> 2^N \<or> N = 0 then None
                  else let bs = rev (nat_to_rev_bits i)
                        in Some (replicate (N - length bs) Bit0 @ bs))"

lemma N_ge_unpadded_bits: "\<lbrakk> 2 ^ N > i; N > 0 \<rbrakk> \<Longrightarrow> N \<ge> length (nat_to_rev_bits i)"
  sorry

lemma ibits_len: "ibits_f N i = Some bs \<Longrightarrow> N = length bs"
  apply (case_tac "i \<ge> 2^N \<or> N = 0")
   apply simp
  apply (simp add: Let_def)
  using N_ge_unpadded_bits by fastforce


lemma ibits_eqv: "ibits_f N i = Some bs \<Longrightarrow> ibits N i bs"
  apply (simp add: sum_list_def Let_def split: if_splits)
  apply (rule ibits_I)
    defer 1
    apply simp
   defer 1
   using N_ge_unpadded_bits add_diff_cancel_left' apply force
   apply (induct i arbitrary: bs)
    apply simp
    apply (subgoal_tac "bs = replicate N Bit0")
     apply (induct N)
      apply simp

  sorry


end