theory Weighted_Graph
  imports
    "HOL-Library.Extended_Real"
    Walk
begin

type_synonym 'a cost_fun = "'a set \<Rightarrow> real"

definition walk_edges_cost :: "'a cost_fun \<Rightarrow> 'a set list \<Rightarrow> real" where
  "walk_edges_cost f l = sum_list (map f (l))"

definition walk_cost :: "'a cost_fun \<Rightarrow> 'a list \<Rightarrow> real" where
  "walk_cost f p = walk_edges_cost f (walk_edges p)"

section \<open>Walks\<close>

subsection \<open>Basic Lemmas\<close>

lemma walk_edges_cost_Nil [simp]:
  shows "walk_edges_cost f [] = 0"
  by (simp add: walk_edges_cost_def)

lemma walk_cost_Nil [simp]:
  shows "walk_cost f [] = 0"
  by (simp add: walk_cost_def)

lemma walk_edges_cost_Cons [simp]:
  shows "walk_edges_cost f (x # xs) = f x + walk_edges_cost f xs"
  by (simp add: walk_edges_cost_def)

lemma walk_cost_non_negative_if_cost_non_negative:
  assumes "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
  assumes "walk G u p w"
  shows "0 \<le> walk_cost f p"
  using assms
  by (induction p arbitrary: u rule: walk_induct) (auto simp add: walk_def walk_cost_def)

subsection \<open>Appending walks\<close>

lemma walk_edges_cost_append [simp]:
  shows "walk_edges_cost f (xs @ ys) = walk_edges_cost f xs + walk_edges_cost f ys"
  by (simp add: walk_edges_cost_def)

lemma walk_cost_append:
  assumes "p \<noteq> []"
  shows "walk_cost f (p @ q) = walk_cost f p + walk_cost f ([last p] @ q)"
  using assms
  by (simp add: walk_cost_def walk_edges_append)

lemma walk_cost_append_2:
  assumes "p \<noteq> []"
  assumes "q \<noteq> []"
  assumes "last p = hd q"
  shows "walk_cost f (p @ tl q) = walk_cost f p + walk_cost f q"
  using assms
  by (simp add: walk_cost_append)

lemma walk_cost_append_append:
  assumes "p \<noteq> []"
  assumes "Suc 0 < length q"
  assumes "r \<noteq> []"
  assumes "last p = hd q"
  assumes "last q = hd r"
  shows "walk_cost f (p @ tl q @ tl r) = walk_cost f p + walk_cost f q + walk_cost f r"
proof -
  have "walk_cost f (p @ tl q @ tl r) = walk_cost f (p @ tl q) + walk_cost f r"
    using assms(2, 3, 5) walk_cost_append[where ?p = "p @ tl q"]
    by (simp add: tl_non_empty_conv last_tl)
  also have "... = walk_cost f p + walk_cost f q + walk_cost f r"
    using assms(1, 2, 4)
    by (auto intro: walk_cost_append_2)
  finally show ?thesis
    .
qed

subsection \<open>Reversing walks\<close>

lemma walk_edges_cost_rev [simp]:
  shows "walk_edges_cost f (rev l) = walk_edges_cost f l"
  by (simp add: walk_edges_cost_def rev_map[symmetric])

lemma walk_cost_rev [simp]:
  shows "walk_cost f (rev p) = walk_cost f p"
  by (simp add: walk_cost_def walk_edges_rev[symmetric])

subsection \<open>Decomposing walks\<close>

lemma (in graph) walk_cost_closed_walk_decomp:
  assumes "walk G u p v"
  assumes "\<not> distinct p"
  assumes "walk_closed_walk_decomp G p = (q, r, s)"
  shows "walk_cost f p = walk_cost f q + walk_cost f r + walk_cost f s"
proof -
  obtain
    "p = q @ tl r @ tl s"
    "\<exists>w. walk G u q w \<and> closed_walk G w r \<and> walk G w s v"
    using assms
    by (elim walk_closed_walk_decompE_2)
  thus ?thesis
    by (auto simp add: walk_def intro: walk_cost_append_append)
qed

section \<open>Paths\<close>

lemma (in graph) walk_cost_ge_walk_to_path_cost:
  assumes f_non_negative: "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
  assumes "walk G u p v"
  shows "walk_cost f (walk_to_path p) \<le> walk_cost f p"
  using assms(2)
proof (induction rule: walk_to_path_induct)
  case path
  thus ?case by simp
next
  case (decomp p q r s)
  have walks: "\<exists>w. walk G u q w \<and> closed_walk G w r \<and> walk G w s v"
    using decomp.hyps
    by (elim walk_closed_walk_decompE_2)

  have "walk_cost f (walk_to_path p) = walk_cost f (walk_to_path (q @ tl s))"
    using decomp.hyps(1, 2)
    by (auto simp add: decomp.hyps(3))
  also have "... \<le> walk_cost f (q @ tl s)"
    using decomp.IH
    .
  also have "... = walk_cost f q + walk_cost f s"
    using walks
    by (auto simp add: walk_def intro: walk_cost_append_2)
  also have "... \<le> walk_cost f q + walk_cost f r + walk_cost f s"
    using f_non_negative walks
    by (auto intro: walk_cost_non_negative_if_cost_non_negative)
  also have "... = walk_cost f p"
    using decomp.hyps
    by (rule walk_cost_closed_walk_decomp[symmetric])
  finally show ?case
    .
qed

end