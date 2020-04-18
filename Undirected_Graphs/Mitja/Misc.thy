theory Misc
  imports "HOL-Library.Extended_Real"
begin

section \<open>nat\<close>

lemma less_implies_Suc_le:
  assumes "n \<le> m"
  assumes "n \<noteq> m"
  shows "Suc n \<le> m"
  using assms
  by simp

section \<open>list\<close>

lemma list_length_1:
  assumes "length l = Suc 0"
  assumes "x = hd l"
  assumes "y = last l"
  shows "l = [x] \<and> x = y"
  using assms
  by (auto simp add: length_Suc_conv)

lemma list_length_2:
  assumes "length l = Suc (Suc 0)"
  assumes "x = hd l"
  assumes "y = last l"
  shows "l = [x, y]"
  using assms
  by (auto simp add: length_Suc_conv)

lemma tl_non_empty_conv:
  shows "tl l \<noteq> [] \<longleftrightarrow> Suc 0 < length l"
proof -
  have "tl l \<noteq> [] \<longleftrightarrow> 0 < length (tl l)"
    by blast
  also have "... \<longleftrightarrow> Suc 0 < length l"
    by simp
  finally show ?thesis
    .
qed

(* Adapted from the formalization of directed graphs (Graph_Theory). *)
lemma not_distinct_decomp:
  assumes "\<not> distinct as"
  shows "\<exists>xs y ys zs. as = xs @ y # ys @ y # zs \<and> distinct xs \<and> y \<notin> set xs \<and> y \<notin> set ys"
proof -
  obtain xs y ys where
    "y \<in> set xs"
    "distinct xs"
    "as = xs @ y # ys"
    using assms
    by (auto simp add: not_distinct_conv_prefix)
  moreover then obtain xs' ys' where
    "xs = xs' @ y # ys'"
    by (auto simp add: in_set_conv_decomp)
  ultimately show ?thesis
    by auto
qed

section \<open>Extended real\<close>

lemma ereal_add_commute_2:
  fixes a b c d :: ereal
  shows "a + b + c + d = b + c + a + d"
proof -
  have "a + b + c + d = a + (b + c) + d"
    by (simp add: ab_semigroup_add_class.add_ac(1))
  also have "... = b + c + a + d"
    by (intro add_mono_thms_linordered_semiring(4)) (simp add: add.commute)
  finally show ?thesis
    .
qed

lemma ereal_add_mono_2:
  fixes a b c x y z :: ereal
  assumes "a \<le> b + c"
  assumes "x \<le> y + z"
  shows "a + x \<le> b + c + y + z"
  using add_mono[OF assms]
  by (simp add: add.assoc)

lemma ereal_add_left_mono:
  fixes a b c :: ereal
  assumes "\<bar>b\<bar> \<noteq> \<infinity>"
  assumes "a - b \<le> c"
  shows "a \<le> b + c"
  using assms
  by (simp add: ereal_minus_le add.commute)

lemma ereal_add_add_left_mono:
  fixes a b c :: ereal
  assumes "\<bar>b\<bar> \<noteq> \<infinity>"
  assumes "a - b - b \<le> c"
  shows "a \<le> b + b + c"
proof -
  have "\<bar>b + b\<bar> \<noteq> \<infinity>"
    using assms(1)
    by auto
  moreover have "a - (b + b) \<le> c"
    using assms
    by (simp add: ereal_diff_add_eq_diff_diff_swap)
  ultimately show ?thesis
    by (rule ereal_add_left_mono)
qed

lemma ereal_minus_mono:
  fixes a b c :: ereal
  assumes "\<bar>b\<bar> \<noteq> \<infinity>"
  assumes "a \<le> b + c"
  shows "a - b \<le> c"
proof -
  have "a - b \<le> b + c - b"
    using assms(2)
    by (rule ereal_minus_mono) simp
  also have "... = c"
    using assms(1)
    by (rule ereal_diff_add_inverse)
  finally show ?thesis
    .
qed

lemma ereal_minus_mono_2:
  fixes a b c :: ereal
  assumes "\<bar>c\<bar> \<noteq> \<infinity>"
  assumes "a \<le> b + c"
  shows "a - c \<le> b"
proof -
  have "a \<le> c + b"
    using assms(2)
    by (simp add: algebra_simps)
  hence "a - c \<le> c + b - c"
    by (rule Extended_Real.ereal_minus_mono) simp
  also have "... = b"
    using assms(1)
    by (rule ereal_diff_add_inverse)
  finally show ?thesis
    .
qed

lemma ereal_minus_minus_mono:
  fixes a b c d :: ereal
  assumes "\<bar>c\<bar> \<noteq> \<infinity>"
  assumes "a \<le> b + c + c + d"
  shows "a - c - c \<le> b + d"
proof -
  have "\<bar>c + c\<bar> \<noteq> \<infinity>"
    using assms(1)
    by auto
  moreover have "a \<le> (b + d) + (c + c)"
    using assms(2)
    by (metis add.assoc add.commute)
  ultimately have "a - (c + c) \<le> (b + d)"
    by (rule ereal_minus_mono_2)
  thus ?thesis
    using assms(1)
    by (simp add: ereal_diff_add_eq_diff_diff_swap)
qed

lemma ereal_plus_minus_mono:
  fixes a b c :: ereal
  assumes "\<bar>b\<bar> \<noteq> \<infinity>"
  assumes "\<bar>c\<bar> \<noteq> \<infinity>"
  assumes "a - b \<le> c"
  shows "a - c \<le> b"
proof -
  have "a - b + b \<le> c + b"
    using assms(3)
    by (rule add_right_mono)
  hence "b + a - b \<le> c + b"
    by (simp add: ereal_diff_add_assoc2 add.commute)
  hence "a \<le> c + b"
    using ereal_diff_add_inverse[OF assms(1)]
    by simp
  hence "a \<le> b + c"
    by (simp add: add.commute)
  with assms(2) show ?thesis
    by (rule ereal_minus_mono_2)
qed

lemma ereal_plus_minus_minus_mono:
  fixes a b c :: ereal
  assumes "\<bar>b\<bar> \<noteq> \<infinity>"
  assumes "\<bar>c\<bar> \<noteq> \<infinity>"
  assumes "a - b - b \<le> c"
  shows "a - c \<le> b + b"
proof -
  have "\<bar>b + b\<bar> \<noteq> \<infinity>"
    using assms(1)
    by auto
  moreover have "\<bar>c\<bar> \<noteq> \<infinity>"
    using assms(2)
    by simp
  moreover have "a - (b + b) \<le> c"
    using assms(3)
    by (simp add: ereal_diff_add_eq_diff_diff_swap[OF assms(1)])
  ultimately show ?thesis
    by (rule ereal_plus_minus_mono)
qed

lemma INF_in_image:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes S_finite: "finite S"
  assumes S_non_empty: "S \<noteq> {}"
  shows "Inf (f ` S) \<in> f ` S"
proof -
  have image_finite: "finite (f ` S)"
    using S_finite
    by simp
  have image_non_empty: "(f ` S) \<noteq> {}"
    using S_non_empty
    by simp

  have "Inf (f ` S) = Min (f ` S)"
    using image_finite image_non_empty
    by (rule cInf_eq_Min)
  moreover have "Min (f ` S) \<in> (f ` S)"
    using image_finite image_non_empty
    by (rule Min_in)
  ultimately show ?thesis
    by simp
qed

end