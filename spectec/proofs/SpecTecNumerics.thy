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

abbreviation bitn where
  "bitn b n \<equiv> 2^n * bit_to_nat b"

inductive ibits :: "nat \<Rightarrow> nat \<Rightarrow> bits \<Rightarrow> bool" where
  ibits_I: "\<lbrakk> length bs = N
            ; N > 0
            ; i = sum_list (map2 bitn bs (rev [0 ..< N]))
            \<rbrakk> \<Longrightarrow> ibits N i bs"

fun nat_to_rev_bits :: "nat \<Rightarrow> bits" where
  "nat_to_rev_bits 0 = [Bit0]" |
  "nat_to_rev_bits (Suc 0) = [Bit1]" |
  "nat_to_rev_bits n = (if even n then Bit0 else Bit1) # nat_to_rev_bits (n div 2)"

lemma bits_non_empty: "length (nat_to_rev_bits n) \<ge> 1"
  by (metis One_nat_def Suc_le_eq length_greater_0_conv list.simps(3) nat_to_rev_bits.elims)


find_theorems name: "nat_to_rev_bits"

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



end