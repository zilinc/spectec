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

find_theorems name: "nat_to_rev_bits"

fun ibits_f :: "nat \<Rightarrow> nat \<Rightarrow> bits option" where
  "ibits_f N i = (if i \<ge> 2^N \<or> N = 0 then None
                  else let bs = rev (nat_to_rev_bits i)
                        in Some (replicate (N - length bs) Bit0 @ bs))"

lemma N_ge_unpadded_bits: "\<lbrakk> i < 2^N; N \<noteq> 0 \<rbrakk> \<Longrightarrow> N \<ge> length (nat_to_rev_bits i)"
  apply (induction i arbitrary: N rule: nat_to_rev_bits.induct)
    apply simp
   apply simp
  apply simp
  
  sorry

lemma ibits_len: "ibits_f N i = Some bs \<Longrightarrow> N = length bs"
  apply (case_tac "i \<ge> 2^N \<or> N = 0")
   apply simp
  apply (simp add: Let_def)
  using N_ge_unpadded_bits by fastforce


thm nat_to_rev_bits.induct

lemma ibits_eqv: "ibits_f N i = Some bs \<Longrightarrow> ibits N i bs"
proof (simp add: sum_list_def Let_def split: if_splits)
  assume N_range: "\<not> 2^N \<le> i \<and> 0 < N"
     and bs: "replicate (N - length (nat_to_rev_bits i)) Bit0 @ rev (nat_to_rev_bits i) = bs"
  show ?thesis
  proof (rule ibits_I)
    show "length bs = N" using N_range bs sorry
  next
    show "0 < N" using N_range by simp
  next
    fix N
    let ?bs = "(replicate (N - length (nat_to_rev_bits i)) Bit0 @ rev (nat_to_rev_bits i))"
    have "i = sum_list (map2 (\<lambda>b e. 2^e * bit_to_nat b) ?bs (rev [0..<N]))"
    proof (induction i rule: nat_to_rev_bits.induct)
      case 1
      then show ?case
        apply simp
        sorry
    next
      case 2
      then show ?case sorry
    next
      case (3 va)
      then show ?case sorry
    qed
      
    thus "i = SpecTecNumerics.sum_list (map2 (\<lambda>x y. 2 ^ y * bit_to_nat x) bs (rev [0..<N]))" using bs by simp
  qed
qed



end