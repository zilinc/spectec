theory SpecTecNumerics

imports Main

begin

datatype bit = Bit0 | Bit1
type_synonym bits = "bit list"

primrec bit_to_nat :: "bit \<Rightarrow> nat" where
  "bit_to_nat Bit0 = 0" |
  "bit_to_nat Bit1 = 1"

lemma bit_le_1: "bit_to_nat b \<le> 1"
  by (cases "b"; simp_all)

definition sum_list :: "nat list \<Rightarrow> nat" where
  "sum_list xs \<equiv> fold (+) xs 0"

abbreviation bitn where
  "bitn b n \<equiv> 2^n * bit_to_nat b"

inductive ibits :: "nat \<Rightarrow> nat \<Rightarrow> bits \<Rightarrow> bool" where
  ibits_I: "\<lbrakk> length bs = N
            ; N > 0
            ; i = sum_list (map2 bitn bs (rev [0 ..< N]))
            \<rbrakk> \<Longrightarrow> ibits N i bs"

lemma ibits_nonempty: "ibits N i bs \<Longrightarrow> bs \<noteq> []"
  using ibits.simps by fastforce

lemma ibits_length: "ibits N i bs \<Longrightarrow> N = length bs"
  using ibits.simps by simp

lemma ibits_i: "ibits N i bs \<Longrightarrow> i = sum_list (map2 bitn bs (rev [0 ..< N]))"
  using ibits.simps by simp

fun nat_to_rev_bits :: "nat \<Rightarrow> bits" where
  "nat_to_rev_bits 0 = [Bit0]" |
  "nat_to_rev_bits (Suc 0) = [Bit1]" |
  "nat_to_rev_bits n = (if even n then Bit0 else Bit1) # nat_to_rev_bits (n div 2)"

lemma bits_non_empty: "length (nat_to_rev_bits n) \<ge> 1"
  by (metis One_nat_def Suc_le_eq length_greater_0_conv list.simps(3) nat_to_rev_bits.elims)

lemma bits_nat_inv1: "nat_to_rev_bits (bit_to_nat b) = [b]"
  apply (cases b)
   by simp_all


lemma bits_nat_inv_h0:
  "bs \<noteq> [] \<Longrightarrow> length bs = N \<Longrightarrow>
   bs' = rev (nat_to_rev_bits (sum_list (map2 bitn (Bit0 # bs) (rev [0..<N+1])))) \<Longrightarrow>
   rev (nat_to_rev_bits (sum_list (map2 bitn bs (rev [0..<N])))) = bs'"
proof (induct bs arbitrary: N bs')
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case   sorry
qed


lemma bits_nat_inv_h1:
  "bs \<noteq> [] \<Longrightarrow> length bs = N \<Longrightarrow>
   bs' = rev (nat_to_rev_bits (sum_list (map2 bitn (Bit1 # bs) (rev [0..<N+1])))) \<Longrightarrow>
   Bit1 # bs = bs'"
  apply (induct bs arbitrary: N bs')
   apply simp
  apply simp
  
  sorry


lemma bits_nat_inv: "bs \<noteq> [] \<Longrightarrow> length bs = N \<Longrightarrow>
                     bs' = rev (nat_to_rev_bits (sum_list (map2 bitn bs (rev [0..<N])))) \<Longrightarrow>
                     bs = replicate (N - length bs') Bit0 @ bs'"
proof (induct bs arbitrary: bs' N rule: List.list_nonempty_induct)
  case (single b)
  then show ?case using bits_nat_inv1 sum_list_def by fastforce
next
  case (cons b bs)
  then show ?case
  proof (cases b)
    case Bit0
    then show ?thesis using cons bits_nat_inv_h0 sorry
  next
    case Bit1
    then show ?thesis using cons bits_nat_inv_h1
      by (metis Suc_eq_plus1 cancel_comm_monoid_add_class.diff_cancel length_Cons replicate_0 self_append_conv2)
  qed
qed



fun ibits_f :: "nat \<Rightarrow> nat \<Rightarrow> bits option" where
  "ibits_f N i = (if i \<ge> 2^N \<or> N = 0 then None
                  else let bs = rev (nat_to_rev_bits i)
                        in Some (replicate (N - length bs) Bit0 @ bs))"


lemma N_ge_unpadded_bits: "\<lbrakk> i < 2^N; N > 0 \<rbrakk> \<Longrightarrow> N \<ge> length (nat_to_rev_bits i)"
proof (induction i arbitrary: N rule: nat_to_rev_bits.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 n)
  have N_gt_1: "N - 1 > 0" using 3(2) nat_neq_iff by fastforce
  have "Suc (Suc n) div 2 < 2 ^ (N - 1)" using 3(2)
    by (metis "3.prems"(2) less_mult_imp_div_less power_minus_mult)
  hence "length (nat_to_rev_bits ((Suc (Suc n)) div 2)) \<le> N - 1" using N_gt_1 3(1) by simp
  thus ?case using N_gt_1 by fastforce
qed


lemma ibits_len: "ibits_f N i = Some bs \<Longrightarrow> N = length bs"
  apply (case_tac "i \<ge> 2^N \<or> N = 0")
   apply simp
  apply (simp add: Let_def)
  using N_ge_unpadded_bits by fastforce


lemma pad0_helper:
  "map2 bitn (replicate q Bit0 @ bs) (rev [0..<q + length bs]) =
   replicate q 0 @ map2 bitn bs (rev [0..<length bs])"
  apply (induct q)
   apply simp
  apply simp
  done

lemma pad0: "n = length (bs :: bits) \<Longrightarrow>
             sum_list (map2 bitn (replicate p Bit0 @ bs) (rev [0..<p+n])) = sum_list (map2 bitn (replicate q Bit0 @ bs) (rev [0..<q+n]))"
  apply (simp add: pad0_helper sum_list_def)
  by (metis Suc_funpow funpow_simps_right(1) id_funpow)


lemma pad0': "n = length (bs :: bits) \<Longrightarrow>
             sum_list (map2 bitn (replicate p Bit0 @ bs) (rev [0..<p+n])) =
             sum_list (map2 bitn bs (rev [0..<n]))"
  using pad0[where ?q=0] by simp


lemma mult2_append0: "length bs \<ge> 1 \<Longrightarrow>
                         2 * sum_list (map2 bitn bs (rev [0 ..< length bs])) = sum_list (map2 bitn (bs @ [Bit0]) (rev [0 ..< length bs + 1]))"
proof (rule list_nonempty_induct[of "bs"])
  show "1 \<le> length bs \<Longrightarrow> bs \<noteq> []" by fastforce
next
  show "\<And>x. 1 \<le> length bs \<Longrightarrow>
         2 * sum_list (map2 bitn [x] (rev [0..<length [x]])) =
             sum_list (map2 bitn ([x] @ [Bit0]) (rev [0..<length [x] + 1]))"
    by (simp add: sum_list_def)
next
  fix x xs
  assume "1 \<le> length bs"
     and xs_not_null: "xs \<noteq> []"
     and IH: "2 * sum_list (map2 bitn xs (rev [0..<length xs])) =
       sum_list (map2 bitn (xs @ [Bit0]) (rev [0..<length xs + 1]))" (is "?l = ?r")
  show "2 * sum_list (map2 bitn (x # xs) (rev [0..<length (x # xs)])) =
       sum_list (map2 bitn ((x # xs) @ [Bit0]) (rev [0..<length (x # xs) + 1]))" (is "?L = ?R")
  proof -
    have top_bit: "bitn x (length xs) + sum_list (map2 bitn xs (rev [0..<length xs])) = sum_list (map2 bitn (x # xs) (rev [0..<length (x # xs)]))" if "xs \<noteq> []" for x xs
      apply (simp add: sum_list_def)
      by (simp add: fold_plus_sum_list_rev)
    hence eq1: "2 * bitn x (length xs) + ?l = ?L"
      by (metis \<open>xs \<noteq> []\<close> distrib_left_numeral)
    from top_bit xs_not_null have eq2: "bitn x (length xs + 1) + ?r = ?R"
      by (metis (mono_tags, lifting) Nil_is_append_conv Suc_eq_plus1 append_Cons length_append_singleton)
    from eq1 eq2 IH show "?L = ?R" by simp
  qed
qed



lemma mult2_plus1_append1: "length bs \<ge> 1 \<Longrightarrow>
                      2 * sum_list (map2 bitn bs (rev [0 ..< length bs])) + 1 = sum_list (map2 bitn (bs @ [Bit1]) (rev [0 ..< length bs + 1]))"
proof (rule list_nonempty_induct[of "bs"])
  show "1 \<le> length bs \<Longrightarrow> bs \<noteq> []" by fastforce
next
  show "\<And>x. 1 \<le> length bs \<Longrightarrow>
         2 * sum_list (map2 bitn [x] (rev [0..<length [x]])) + 1 =
             sum_list (map2 bitn ([x] @ [Bit1]) (rev [0..<length [x] + 1]))"
    by (simp add: sum_list_def)
next
  fix x xs
  assume "1 \<le> length bs"
     and xs_not_null: "xs \<noteq> []"
     and IH: "2 * sum_list (map2 bitn xs (rev [0..<length xs])) + 1 =
       sum_list (map2 bitn (xs @ [Bit1]) (rev [0..<length xs + 1]))" (is "?l = ?r")
  show "2 * sum_list (map2 bitn (x # xs) (rev [0..<length (x # xs)])) + 1 =
       sum_list (map2 bitn ((x # xs) @ [Bit1]) (rev [0..<length (x # xs) + 1]))" (is "?L = ?R")
  proof -
    have top_bit: "bitn x (length xs) + sum_list (map2 bitn xs (rev [0..<length xs])) = sum_list (map2 bitn (x # xs) (rev [0..<length (x # xs)]))" if "xs \<noteq> []" for x xs
      apply (simp add: sum_list_def)
      by (simp add: fold_plus_sum_list_rev)
    hence eq1: "2 * bitn x (length xs) + ?l = ?L"
      by (metis (no_types, lifting) add.assoc distrib_left_numeral xs_not_null)
    from top_bit xs_not_null have eq2: "bitn x (length xs + 1) + ?r = ?R"
      by (metis (mono_tags, lifting) Nil_is_append_conv Suc_eq_plus1 append_Cons length_append_singleton)
    from eq1 eq2 IH show "?L = ?R" by simp
  qed
qed



lemma ibits_soundness: "\<And>N i bs. ibits_f N i = Some bs \<Longrightarrow> ibits N i bs"
proof (simp add: sum_list_def Let_def split: if_splits)
  fix N i bs
  assume N_range: "(\<not> 2^N \<le> i) \<and> 0 < N"
     and bs: "replicate (N - length (nat_to_rev_bits i)) Bit0 @ rev (nat_to_rev_bits i) = bs"
  show "ibits N i bs"
  proof (rule ibits_I)
    show "length bs = N" using N_range bs
      using N_ge_unpadded_bits by fastforce
  next
    show "0 < N" using N_range by simp
  next
    let ?bs = "(replicate (N - length (nat_to_rev_bits i)) Bit0 @ rev (nat_to_rev_bits i))"
    have "i = sum_list (map2 bitn ?bs (rev [0..<N]))" using N_range
    proof (induction i rule: nat_to_rev_bits.induct)
      case 1
      have "0 = sum_list (replicate N 0)"
        apply (simp add: sum_list_def)
        by (metis Suc_funpow funpow_simps_right(1) id_apply id_funpow)
      have "map2 (\<lambda>x y. 2 ^ y * x) (replicate N 0) (rev [0..<N]) = replicate N (0::nat)"
        apply (induct N) by simp_all
      hence assm: "0 = sum_list (map2 (\<lambda>x y. 2 ^ y * x) (replicate N 0) (rev [0..<N]))" using sum_list_def
        by (metis \<open>0 = sum_list (replicate N 0)\<close>)
      have "map2 (\<lambda>x y. 2 ^ y * x) (replicate N 0) (rev [0..<N]) = map2 bitn (replicate N Bit0) (rev [0..<N])"
        using bit_to_nat.simps(1)
              map_replicate[of bit_to_nat N Bit0]
              map_zip_map[of "\<lambda>(uu, uua). 2 ^ uua * uu" bit_to_nat "replicate N Bit0" "rev [0..<N]"]
              split_conv[of "\<lambda>uu uua. 2 ^ uua * uu" "bit_to_nat _"]
        by presburger
      hence "0 = SpecTecNumerics.sum_list (map2 bitn (replicate N Bit0) (rev [0..<N]))" using assm by simp
      thus ?case using N_ge_unpadded_bits N_range
        apply (simp add: sum_list_def)
        by (metis Cons_replicate_eq One_nat_def replicate_append_same)
    next
      case 2
      hence "Suc 0 = sum_list (map2 bitn (replicate (N - 1) Bit0 @ [Bit1]) (rev [0..<N]))"
      proof (induct "N - 1" arbitrary: N)
        case 0
        hence "N = 1" by simp
        then show ?case by (simp add: sum_list_def)
      next
        case (Suc x)
        hence "Suc 0 = SpecTecNumerics.sum_list (map2 bitn (replicate (N - 2) Bit0 @ [Bit1]) (rev [0..<N - 1]))"
          by (metis (no_types, lifting) One_nat_def Suc_1 add_diff_cancel_left' diff_diff_left length_upt lessI list.size(3) nat.distinct(1) plus_1_eq_Suc power_0
              power_increasing_iff upt_conv_Nil zero_less_Suc)
        have N_ge_2: "N \<ge> 2" using Suc(2) by simp
        hence N_eq1: "N - 2 + 1 = N - 1" by simp
        have N_eq2: "N - 1 + 1 = N" using N_ge_2 by simp
        thus ?case using pad0[where ?p="N-2" and ?q="N-1" and ?bs="[Bit1]" and ?n=1] N_ge_2 N_eq1 Suc(1)
        by (metis One_nat_def \<open>Suc 0 = SpecTecNumerics.sum_list (map2 bitn (replicate (N - 2) Bit0 @ [Bit1]) (rev [0..<N - 1]))\<close> length_Suc_conv
              list.size(3))
      qed
      then show ?case by simp
    next
      case (3 k)
      let ?n = "(Suc (Suc k)) div 2"
      from 3 have IH: "?n = sum_list (map2 bitn (replicate (N - length (nat_to_rev_bits ?n)) Bit0 @ rev (nat_to_rev_bits ?n)) (rev [0..<N]))" by fastforce
      thus ?case
        proof (cases "even k")
          case True
          from "3.prems" have "N \<ge> length (nat_to_rev_bits ?n)"
            by (meson N_ge_unpadded_bits div_le_dividend dual_order.trans leI)
          with IH pad0'[where ?bs="rev (nat_to_rev_bits ?n)" and ?p="N - length (nat_to_rev_bits ?n)"] "3.prems"
          have n_eq: "?n = sum_list (map2 bitn (rev (nat_to_rev_bits ?n)) (rev [0..<length (nat_to_rev_bits ?n)]))" by fastforce
          from True have n2: "Suc (Suc k) = 2 * ?n" by simp
          from "3.prems" have "N \<ge> length (nat_to_rev_bits (2 * ?n))"
            by (metis N_ge_unpadded_bits leI n2)
          with IH pad0'[where ?bs="rev (nat_to_rev_bits (2 * ?n))" and ?p="N - length (nat_to_rev_bits (2 * ?n))"] "3.prems"
          have n2_eq: "sum_list (map2 bitn (replicate (N - length (nat_to_rev_bits (2 * ?n))) Bit0 @ rev (nat_to_rev_bits (2 * ?n))) (rev [0..<N])) = sum_list (map2 bitn (rev (nat_to_rev_bits (2 * ?n))) (rev [0..<length (nat_to_rev_bits (2 * ?n))]))" by fastforce
          from n2
          have "Suc (Suc k) = 2 * (sum_list (map2 bitn (rev (nat_to_rev_bits ?n)) (rev [0..<length (nat_to_rev_bits ?n)])))" using n_eq by simp
          also have "... = sum_list (map2 bitn (rev (nat_to_rev_bits ?n) @ [Bit0]) (rev [0 ..< length (nat_to_rev_bits ?n) + 1]))" using mult2_append0 "3.prems" bits_non_empty
            by (metis length_rev)
          also have "... = sum_list (map2 bitn (rev (nat_to_rev_bits (2 * ?n))) (rev [0 ..< length (nat_to_rev_bits (2 * ?n))]))" by fastforce
          finally show ?thesis using pad0'[where ?p="N - length (nat_to_rev_bits (2 * ?n))" and
                                                 ?bs="rev (nat_to_rev_bits (2 * ?n))"]
            using n2 n2_eq by argo
        next
          case False
          from "3.prems" have "N \<ge> length (nat_to_rev_bits ?n)"
            by (meson N_ge_unpadded_bits div_le_dividend dual_order.trans leI)
          with IH pad0'[where ?bs="rev (nat_to_rev_bits ?n)" and ?p="N - length (nat_to_rev_bits ?n)"] "3.prems"
          have n_eq: "?n = sum_list (map2 bitn (rev (nat_to_rev_bits ?n)) (rev [0..<length (nat_to_rev_bits ?n)]))" by fastforce
          from False have Sn2: "Suc (Suc k) = 2 * ?n + 1" by simp
          from "3.prems" have "N \<ge> length (nat_to_rev_bits (2 * ?n + 1))"
            by (metis N_ge_unpadded_bits linorder_not_le Sn2 linorder_not_le)
          with IH pad0'[where ?bs="rev (nat_to_rev_bits (2 * ?n + 1))" and ?p="N - length (nat_to_rev_bits (2 * ?n + 1))"] "3.prems"
          have Sn2_eq: "sum_list (map2 bitn (replicate (N - length (nat_to_rev_bits (2 * ?n + 1))) Bit0 @ rev (nat_to_rev_bits (2 * ?n + 1))) (rev [0..<N])) = sum_list (map2 bitn (rev (nat_to_rev_bits (2 * ?n + 1))) (rev [0..<length (nat_to_rev_bits (2 * ?n + 1))]))" by fastforce
          from Sn2
          have "(Suc (Suc k)) = 2 * (sum_list (map2 bitn (rev (nat_to_rev_bits ?n)) (rev [0..<length (nat_to_rev_bits ?n)]))) + 1" using n_eq Sn2 by simp
          also have "... = sum_list (map2 bitn (rev (nat_to_rev_bits ?n) @ [Bit1]) (rev [0 ..< length (nat_to_rev_bits ?n) + 1]))" using mult2_plus1_append1 "3.prems" bits_non_empty
            by (metis length_rev)
          also have "... = sum_list (map2 bitn (rev (nat_to_rev_bits (2 * ?n + 1))) (rev [0 ..< length (nat_to_rev_bits (2 * ?n + 1))]))" by fastforce
          finally show ?thesis using pad0'[where ?p="N - length (nat_to_rev_bits (2 * ?n + 1))" and
                                                 ?bs="rev (nat_to_rev_bits (2 * ?n + 1))"]
            using Sn2 Sn2_eq by argo
        qed
    qed
    thus "i = SpecTecNumerics.sum_list (map2 bitn bs (rev [0..<N]))"
      using bs by fastforce
  qed
qed

lemma add_msb: "N > 0 \<Longrightarrow> N = length bs \<Longrightarrow> 
                sum_list (map2 bitn bs (rev [0..<N])) + 2^N * bit_to_nat b =
                sum_list (map2 bitn (b#bs) (rev [0..<N+1]))"
  by (simp add: sum_list_def fold_plus_sum_list_rev)


lemma ibits_N_i_rel: "ibits N i bs \<Longrightarrow> N > 0 \<and> 2^N > i"
proof -
  presume "ibits N i bs \<Longrightarrow> bs \<noteq> [] \<Longrightarrow> N > 0 \<and> 2^N > i"
  thus "ibits N i bs \<Longrightarrow> N > 0 \<and> 2^N > i"
    using ibits_nonempty by blast
next
  show "ibits N i bs \<Longrightarrow> bs \<noteq> [] \<Longrightarrow> N > 0 \<and> 2^N > i"
  proof (rotate_tac 1; induct bs arbitrary: N i rule: List.list_nonempty_induct)
    case (single b)
    hence "N = 1" using ibits.simps by fastforce
    hence "i = bit_to_nat b" using ibits.simps sum_list_def single by simp
    then show ?case using \<open>N = 1\<close> bit_le_1
      by (simp add: less_2_cases_iff order_le_less)
  next
    case (cons b bs)
    hence N_gt_1: "N > 1" using ibits_length by fastforce
    hence bs_length: "N - 1 = length bs" using cons.prems ibits_length by fastforce
    let ?i' = "sum_list (map2 bitn bs (rev [0..<N-1]))"
    have "ibits (N-1) ?i' bs" using N_gt_1 bs_length[symmetric] ibits_I by simp
    hence i'_range: "?i' < 2^(N-1)" using cons.hyps by simp
    from cons have "i = sum_list (map2 bitn (b#bs) (rev [0..<N]))" using ibits.simps by simp
    hence i_i': "i = ?i' + 2^(N-1) * bit_to_nat b" using N_gt_1 sum_list_def bs_length add_msb
      by (simp add: Nat.le_imp_diff_is_add)
    have "x1 < 2^N" if asm0: "N > 1" and asm1: "x1 = x2 + 2^(N-1) * bit_to_nat b" and asm2: "x2 < 2^(N-1)" for N b x1 x2
    proof -
      from bit_le_1 have "2^(N-1) * bit_to_nat b \<le> 2^(N-1)" by simp
      thus "x1 < 2^N" using asm0 asm1 asm2
        by (metis add_diff_inverse_nat add_mono_thms_linordered_field(3) mult.commute mult_2_right order_less_imp_not_less plus_1_eq_Suc power_Suc)
    qed
    thus ?case using N_gt_1 by (metis i_i' bot_nat_0.extremum_strict i'_range not_gr0)
  qed
qed


lemma ibits_completeness:
  fixes N i bs
  assumes "ibits N i bs"
  shows "ibits_f N i = Some bs"
proof (simp only: ibits_f.simps)
  from assms have N_range: "N > 0 \<and> 2^N > i" using ibits_N_i_rel by simp
  hence "bs \<noteq> []" using assms ibits_length by blast
  thus "(if 2 ^ N \<le> i \<or> N = 0 then None else let bs = rev (nat_to_rev_bits i) in Some (replicate (N - length bs) Bit0 @ bs)) = Some bs" using assms
  proof (induct bs arbitrary: N i rule: List.list_nonempty_induct)
    case (single b)
    hence "N > 0 \<and> 2^N > i" using ibits_N_i_rel by simp
    from single ibits_length have asm_N: "N = 1" by force 
    with single ibits_i sum_list_def have asm_i: "i = bit_to_nat b" by fastforce
    then show ?case using bits_nat_inv1 asm_N asm_i
      using \<open>0 < N \<and> i < 2 ^ N\<close> by fastforce
  next
    case (cons b bs)
    hence N_gt_1: "N > 1" using ibits_length by fastforce
    hence bs_length: "N - 1 = length bs" using cons.prems ibits_length by fastforce
    let ?i' = "sum_list (map2 bitn bs (rev [0..<N-1]))"
    have "ibits (N-1) ?i' bs" using N_gt_1 bs_length[symmetric] ibits_I by simp
    from cons(3) ibits_N_i_rel have "N > 0 \<and> 2^N > i" by simp
    hence asm_N: "\<not> (2 ^ (N-1) \<le> ?i' \<or> N-1 = 0)"
      by (metis \<open>ibits (N - 1) (sum_list (map2 bitn bs (rev [0..<N - 1]))) bs\<close> cons.hyps(2) option.distinct(1))
    from cons(3) have asm_i: "i = sum_list (map2 bitn (b#bs) (rev [0..<N]))" using ibits_i by simp
    with cons(2) have "(if 2 ^ (N-1) \<le> ?i' \<or> N-1 = 0 then None else let bs = rev (nat_to_rev_bits ?i') in Some (replicate (N-1 - length bs) Bit0 @ bs)) = Some bs"
      using \<open>ibits (N - 1) (sum_list (map2 bitn bs (rev [0..<N - 1]))) bs\<close> by blast
    hence "(let bs = rev (nat_to_rev_bits (sum_list (map2 bitn bs (rev [0..<N - 1])))) in Some (replicate (N - 1 - length bs) Bit0 @ bs)) = Some bs" using asm_N asm_i by simp
    hence "(let bs = rev (nat_to_rev_bits i) in Some (replicate (N - length bs) Bit0 @ bs)) = Some (b # bs)" using asm_i N_gt_1 bits_nat_inv cons.prems ibits.simps by simp
    thus ?case using cons(3) ibits_N_i_rel[of N i] by fastforce
  qed
    from assms have asm_i: "i = sum_list (map2 bitn bs (rev [0 ..< N]))" using ibits_i by simp
qed


end