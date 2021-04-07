theory Walk
  imports
    Graph
    "Misc"
begin

section \<open>Walks\<close>

text \<open>
A walk is an alternating sequence $v_0, e_1, v_2, ..., e_k, v_k$ of vertices $v_i$ and edges $e_i$
such that the endpoints of $e_i$ are $v_{i-1}$ and $v_i$ for every i = 1, ..., k.
We represent a walk by the sequence of its vertices.
\<close>

type_synonym 'a walk = "'a list"

(* Adapted from the formalization of undirected graphs by Mohammad Abdulaziz. *)
inductive consistent_seq where
  consistent_seq_Nil: "consistent_seq G []" |
  consistent_seq_Cons: "v \<in> vertices G \<Longrightarrow> consistent_seq G [v]" |
  consistent_seq_Cons_Cons: "\<lbrakk> {v, v'} \<in> edges G; consistent_seq G (v' # vs) \<rbrakk> \<Longrightarrow>
    consistent_seq G (v # v' # vs)"

declare consistent_seq_Nil [simp]
inductive_simps consistent_seq_Cons [simp]: "consistent_seq G [v]"
inductive_simps consistent_seq_Cons_Cons [simp]: "consistent_seq G (v # v' # vs)"

definition walk :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a walk \<Rightarrow> 'a \<Rightarrow> bool" where
  "walk G u p v \<equiv> p \<noteq> [] \<and> u = hd p \<and> v = last p \<and> consistent_seq G p"

text \<open>A walk is closed if its endpoints are the same.\<close>

abbreviation closed_walk :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a walk \<Rightarrow> bool" where
  "closed_walk G v c \<equiv> walk G v c v \<and> Suc 0 < length c"

(* Adapted from the formalization of undirected graphs by Mohammad Abdulaziz. *)
fun walk_edges :: "'a walk \<Rightarrow> 'a set list" where
  "walk_edges [] = []" |
  "walk_edges [v] = []" |
  "walk_edges (v # v' # vs) = {v, v'} # (walk_edges (v' # vs))"

lemmas walk_induct = walk_edges.induct

text \<open>The length of a walk is the number of its edges.\<close>

abbreviation walk_length :: "'a walk \<Rightarrow> nat" where
  "walk_length p \<equiv> length (walk_edges p)"

subsection \<open>Basic Lemmas\<close>

lemma Cons_Cons_walk_iff:
  shows "walk G u (v # v' # vs) w \<longleftrightarrow> u = v \<and> {v, v'} \<in> edges G \<and> walk G v' (v' # vs) w"
  by (auto simp add: walk_def)

lemma singleton_is_walk:
  assumes "v \<in> vertices G"
  shows "walk G v [v] v"
  using assms
  by (simp add: walk_def)

lemma (in graph) edge_is_walk:
  assumes "{u, v} \<in> edges G"
  shows "walk G u [u, v] v"
proof -
  have "{u, v} \<subseteq> vertices G"
    using assms
    by (rule edge_subset_vertices)
  hence "v \<in> vertices G"
    by simp
  hence "walk G v [v] v"
    by (simp add: walk_def)
  thus ?thesis
    using assms
    by (simp add: Cons_Cons_walk_iff)
qed

lemma (in graph) edge_iff_walk:
  shows "{u, v} \<in> edges G = walk G u [u, v] v"
proof
  assume "{u, v} \<in> edges G"
  thus "walk G u [u, v] v"
    by (rule edge_is_walk)
next
  assume "walk G u [u, v] v"
  thus "{u, v} \<in> edges G"
    by (simp add: Cons_Cons_walk_iff)
qed

lemma walk_length:
  assumes "p \<noteq> []"
  shows "length p = Suc (walk_length p)"
  using assms
  by (induction p rule: walk_induct) simp+

(**)
subsection \<open>\<close>

lemma (in graph) walk_in_vertices:
  assumes "walk G u p v"
  assumes "w \<in> set p"
  shows "w \<in> vertices G"
  using assms
proof (induction p arbitrary: u rule: walk_induct)
  case 1
  thus ?case
    by simp
next
  case (2 _)
  thus ?case
    by (simp add: walk_def)
next
  case (3 _ _ _)
  thus ?case
    using Union_edges_subset_vertices
    by (auto simp add: walk_def)
qed

lemma (in graph) walk_hd_in_vertices:
  assumes "walk G u p v"
  shows "u \<in> vertices G"
  using assms
  by (intro walk_in_vertices) (simp add: walk_def)+

lemma (in graph) walk_last_in_vertices:
  assumes "walk G u p v"
  shows "v \<in> vertices G"
  using assms
  by (intro walk_in_vertices) (simp add: walk_def)+

lemma walk_hd_neq_last_implies_edges_non_empty:
  assumes "walk G u p v"
  assumes "u \<noteq> v"
  shows "edges G \<noteq> {}"
  using assms
  by (induction p rule: walk_induct) (auto simp add: walk_def)

lemma walk_edges_in_edges:
  assumes "walk G u p w"
  shows "set (walk_edges p) \<subseteq> edges G"
  using assms
proof (induction p arbitrary: u rule: walk_induct)
  case 1
  thus ?case
    by simp
next
  case (2 _)
  thus ?case
    by simp
next
  case (3 v v' vs)
  have "walk G v' (v' # vs) w"
    using "3.prems"
    by (simp add: Cons_Cons_walk_iff)
  hence "set (walk_edges (v' # vs)) \<subseteq> edges G"
    by (rule "3.IH")
  moreover have "{v, v'} \<in> edges G"
    using "3.prems"
    by (simp add: Cons_Cons_walk_iff)
  ultimately show ?case
    by simp
qed

subsection \<open>Prefixes/suffixes of walks\<close>

lemma (in graph) walk_prefix_is_walk:
  assumes "p \<noteq> []"
  assumes "walk G u (p @ q) w"
  shows "walk G u p (last p)"
  using assms
proof (induction p arbitrary: u rule: walk_induct)
  case 1
  thus ?case
    by simp
next
  case (2 _)
  thus ?case
    by (auto simp add: walk_def intro: walk_in_vertices)
next
  case (3 _ _ _)
  thus ?case
    by (simp add: walk_def)
qed

lemma tl_consistent_seq:
  assumes "consistent_seq G p"
  shows "consistent_seq G (tl p)"
  using assms
  by (induction p rule: walk_induct) simp+

lemma suffix_consistent_seq:
  assumes "consistent_seq G (p @ q)"
  shows "consistent_seq G q"
  using assms
proof (induction p rule: walk_induct)
  case 1
  thus ?case
    by simp
next
  case (2 v)
  hence "consistent_seq G (v # q)"
    by simp
  hence "consistent_seq G (tl (v # q))"
    by (rule tl_consistent_seq)
  thus ?case
    by simp
next
  case (3 _ _ _)
  thus ?case
    by simp
qed

lemma (in graph) walk_suffix_is_walk:
  assumes "q \<noteq> []"
  assumes "walk G u (p @ q) w"
  shows "walk G (hd q) q w"
  using assms
proof (induction q arbitrary: u rule: walk_induct)
  case 1
  thus ?case
    by simp
next
  case (2 v)
  have "v \<in> vertices G"
    using "2.prems"(2)
    by (rule walk_in_vertices) simp
  thus ?case
    using "2.prems"(2)
    by (simp add: walk_def)
next
  case (3 v v' vs)
  have "consistent_seq G (p @ v # v' # vs)"
    using "3.prems"(2)
    by (simp add: walk_def)
  hence "consistent_seq G (v # v' # vs)"
    by (rule suffix_consistent_seq)
  thus ?case
    using "3.prems"(2)
    by (simp add: walk_def)
qed

subsection \<open>Appending walks\<close>

lemma append_consistent_seq:
  assumes "consistent_seq G p"
  assumes q_consistent_seq: "consistent_seq G q"
  assumes "{last p, hd q} \<in> edges G"
  shows "consistent_seq G (p @ q)"
  using assms(1, 3)
proof (induction p rule: walk_induct)
case 1
  show ?case
    using q_consistent_seq
    by simp
next
  case (2 _)
  show ?case
  proof (cases q)
    case Nil
    thus ?thesis
      using "2.prems"(1)
      by simp
  next
    case (Cons _ _)
    thus ?thesis
      using "2.prems"(2) q_consistent_seq
      by simp
  qed
next
  case (3 _ _ _)
  thus ?case
    by simp
qed

lemma append_consistent_seq_2:
  assumes p_consistent_seq: "consistent_seq G p"
  assumes q_consistent_seq: "consistent_seq G q"
  assumes "last p = hd q"
  shows "consistent_seq G (p @ tl q)"
proof (cases "tl q")
  case Nil
  thus ?thesis
    using p_consistent_seq
    by simp
next
  case (Cons _ _)
  hence "q \<noteq> []"
    by auto
  hence "q = hd q # tl q"
    by (rule hd_Cons_tl[symmetric])
  hence "consistent_seq G (hd q # tl q)"
    using q_consistent_seq
    by simp
  hence "{hd q, hd (tl q)} \<in> edges G"
    using q_consistent_seq
    by (simp add: Cons)
  thus ?thesis
    using assms
    by (intro tl_consistent_seq append_consistent_seq) simp+
qed

lemma walk_append_is_walk:
  notes walk_def [simp]
  assumes p_walk: "walk G u p v"
  assumes q_walk: "walk G v q w"
  shows "walk G u (p @ tl q) w"
proof -
  have "q = v # tl q"
    using q_walk
    by simp
  hence "w = last (p @ tl q)"
    using assms
    by (cases "tl q") simp+
  moreover have "consistent_seq G (p @ tl q)"
    using assms
    by (intro append_consistent_seq_2) simp+
  ultimately show ?thesis
    using p_walk
    by simp
qed

lemma walk_append_append_is_walk:
  assumes p_walk: "walk G u p v"
  assumes q_walk: "walk G v q w"
  assumes r_walk: "walk G w r x"
  shows "walk G u (p @ tl q @ tl r) x"
proof -
  have "walk G u (p @ tl q) w"
    using p_walk q_walk
    by (rule walk_append_is_walk)
  from walk_append_is_walk[OF this r_walk]
  show ?thesis
    by simp
qed

lemma walk_edges_append:
  assumes "p \<noteq> []"
  shows "walk_edges (p @ q) = walk_edges p @ walk_edges ([last p] @ q)"
  using assms
  by (induction p rule: walk_induct) simp+

lemma walk_edges_append_2:
  assumes "q \<noteq> []"
  shows "walk_edges (p @ q) = walk_edges (p @ [hd q]) @ walk_edges q"
  using assms walk_edges_append[of "p @ [hd q]" "tl q"]
  by simp

subsection \<open>Reversing walks\<close>

lemma (in graph) rev_consistent_seq:
  assumes "consistent_seq G p"
  shows "consistent_seq G (rev p)"
  using assms
proof (induction p rule: walk_induct)
case 1
  thus ?case
    by simp
next
  case (2 _)
  thus ?case
    by simp
next
  case (3 v v' vs)
  have "consistent_seq G (rev (v' # vs))"
    using "3.prems"
    by (intro "3.IH") simp
  moreover have "consistent_seq G [v]"
    using "3.prems" Union_edges_subset_vertices
    by auto
  moreover have "{last (rev (v' # vs)), hd [v]} \<in> edges G"
    using "3.prems"
    by (simp add: insert_commute)
  ultimately have "consistent_seq G (rev (v' # vs) @ [v])"
    by (rule append_consistent_seq)
  thus ?case
    by simp
qed

lemma (in graph) walk_rev_is_walk:
  notes walk_def [simp]
  assumes "walk G u p v"
  shows "walk G v (rev p) u"
proof -
  have "(rev p) \<noteq> []"
    using assms
    by simp
  moreover have "v = hd (rev p)"
    using assms
    by (auto intro: hd_rev[symmetric])
  moreover have "u = last (rev p)"
    using assms
    by (auto intro: last_rev[symmetric])
  moreover have "consistent_seq G (rev p)"
    using assms
    by (intro rev_consistent_seq) simp
  ultimately show ?thesis
    by simp
qed

lemma (in graph) walk_rev:
  shows "walk G v (rev p) u = walk G u p v"
proof
  assume "walk G v (rev p) u"
  from walk_rev_is_walk[OF this]
  show "walk G u p v"
    by simp
next
  assume "walk G u p v"
  from walk_rev_is_walk[OF this]
  show "walk G v (rev p) u"
    by simp
qed

lemma walk_edges_rev:
  shows "rev (walk_edges p) = walk_edges (rev p)"
proof (induction p rule: walk_induct)
case 1
  thus ?case
    by simp
next
  case (2 _)
  thus ?case
    by simp
next
  case (3 v v' vs)
  have "rev (walk_edges (v # v' # vs)) = rev ({v, v'} # walk_edges (v' # vs))"
    by simp
  also have "... = rev (walk_edges (v' # vs)) @ [{v, v'}]"
    by simp
  also have "... = walk_edges (rev (v' # vs)) @ [{v, v'}]"
    by (simp add: "3.IH")
  also have "... = walk_edges (rev (v' # vs)) @ walk_edges ([last (rev (v' # vs))] @ [v])"
    by (simp add: insert_commute)
  also have "... = walk_edges (rev (v' # vs) @ [v])"
    by (intro walk_edges_append[symmetric]) simp
  finally show ?case
    by simp
qed

subsection \<open>Decomposing walks\<close>

subsubsection \<open>Splitting a walk at a vertex\<close>

fun is_walk_vertex_decomp :: "'a graph \<Rightarrow> 'a walk \<Rightarrow> 'a \<Rightarrow> 'a walk \<times> 'a walk \<Rightarrow> bool" where
  "is_walk_vertex_decomp G p v (q, r) \<longleftrightarrow> p = q @ tl r \<and> (\<exists>u w. walk G u q v \<and> walk G v r w)"

definition walk_vertex_decomp :: "'a graph \<Rightarrow> 'a walk \<Rightarrow> 'a \<Rightarrow> 'a walk \<times> 'a walk" where
  "walk_vertex_decomp G p v \<equiv> SOME qr. is_walk_vertex_decomp G p v qr"

lemma (in graph) walk_vertex_decompE:
  assumes p_walk: "walk G u p v"
  assumes p_decomp: "p = xs @ y # ys"
  obtains q r where
    "p = q @ tl r"
    "q = xs @ [y]"
    "r = y # ys"
    "walk G u q y"
    "walk G y r v"
proof
  define q r where
    "q = xs @ [y]" and
    "r = y # ys"
  thus
    "p = q @ tl r"
    "q = xs @ [y]"
    "r = y # ys"
    by (simp add: p_decomp)+
  thus "walk G u q y"
    using p_walk walk_prefix_is_walk[where ?p = q]
    by simp
  show "walk G y r v"
    using p_walk walk_suffix_is_walk[where ?q = r]
    by (simp add: p_decomp r_def)
qed

lemma (in graph) walk_vertex_decomp_is_walk_vertex_decomp:
  assumes p_walk: "walk G u p w"
  assumes v_in_p: "v \<in> set p"
  shows "is_walk_vertex_decomp G p v (walk_vertex_decomp G p v)"
proof -
  obtain xs ys where
    "p = xs @ v # ys"
    using v_in_p
    by (auto simp add: in_set_conv_decomp)
  with p_walk
  obtain q r where
    "p = q @ tl r"
    "walk G u q v"
    "walk G v r w"
    by (blast elim: walk_vertex_decompE)
  hence "is_walk_vertex_decomp G p v (q, r)"
    using p_walk
    by (simp add: walk_def)
  hence "\<exists>qr. is_walk_vertex_decomp G p v qr"
    by blast
  thus ?thesis
    unfolding walk_vertex_decomp_def
    ..
qed

lemma (in graph) walk_vertex_decompE_2:
  assumes p_walk: "walk G u p w"
  assumes v_in_p: "v \<in> set p"
  assumes qr_def: "walk_vertex_decomp G p v = (q, r)"
  obtains
    "p = q @ tl r"
    "walk G u q v"
    "walk G v r w"
proof
  have "is_walk_vertex_decomp G p v (q, r)"
    unfolding qr_def[symmetric]
    using p_walk v_in_p
    by (rule walk_vertex_decomp_is_walk_vertex_decomp)
  then obtain u' w' where
    p_decomp: "p = q @ tl r" and
    q_walk: "walk G u' q v" and
    r_walk: "walk G v r w'"
    by auto
  hence "walk G u' p w'"
    by (blast intro: walk_append_is_walk)
  hence
    "u' = u"
    "w' = w"
    using p_walk
    by (simp add: walk_def)+
  thus
    "p = q @ tl r"
    "walk G u q v"
    "walk G v r w"
    using p_decomp q_walk r_walk
    by simp+
qed

(**)
subsubsection \<open>\<close>

(* This subsubsection is largely based on the formalization of directed graphs (Graph_Theory). *)

fun is_walk_closed_walk_decomp :: "'a graph \<Rightarrow> 'a walk \<Rightarrow> 'a walk \<times> 'a walk \<times> 'a walk \<Rightarrow> bool" where
  "is_walk_closed_walk_decomp G p (q, r, s) \<longleftrightarrow>
    p = q @ tl r @ tl s \<and>
    (\<exists>u v w. walk G u q v \<and> closed_walk G v r \<and> walk G v s w) \<and>
    distinct q"

definition walk_closed_walk_decomp :: "'a graph \<Rightarrow> 'a walk \<Rightarrow> 'a walk \<times> 'a walk \<times> 'a walk" where
  "walk_closed_walk_decomp G p \<equiv> SOME qrs. is_walk_closed_walk_decomp G p qrs"

lemma (in graph) walk_closed_walk_decompE:
  assumes p_walk: "walk G u p v"
  assumes p_decomp: "p = xs @ y # ys @ y # zs"
  obtains q r s where
    "p = q @ tl r @ tl s"
    "q = xs @ [y]"
    "r = y # ys @ [y]"
    "s = y # zs"
    "walk G u q y"
    "walk G y r y"
    "walk G y s v"
proof -
  have "p = (xs @ y # ys) @ y # zs"
    using p_decomp
    by simp
  with p_walk
  obtain qr s where
    "p = qr @ tl s"
    "qr = xs @ y # ys @ [y]"
    "s = y # zs"
    "walk G u qr y"
    "walk G y s v"
    by (rule walk_vertex_decompE) simp
  moreover from this(4, 2)
  obtain q r where
    "qr = q @ tl r"
    "q = xs @ [y]"
    "r = y # ys @ [y]"
    "walk G u q y"
    "walk G y r y"
    by (erule walk_vertex_decompE)
  ultimately show ?thesis
    by (auto intro!: that)
qed

lemma (in graph) walk_closed_walk_decomp_is_walk_closed_walk_decomp:
  assumes p_walk: "walk G u p v"
  assumes p_not_distinct: "\<not> distinct p"
  shows "is_walk_closed_walk_decomp G p (walk_closed_walk_decomp G p)"
proof -
  obtain xs y ys zs where
    "p = xs @ y # ys @ y # zs" and
    xs_distinct: "distinct xs" and
    y_not_in_xs: "y \<notin> set xs"
    using p_not_distinct not_distinct_decomp
    by blast
  from p_walk this(1)
  obtain q r s where
    "p = q @ tl r @ tl s"
    "q = xs @ [y]"
    "r = y # ys @ [y]"
    "s = y # zs"
    "walk G u q y"
    "walk G y r y"
    "walk G y s v"
    by (erule walk_closed_walk_decompE)
  moreover hence
    "distinct q"
    "Suc 0 < length r"
    using xs_distinct y_not_in_xs
    by simp+
  ultimately have
    "\<exists>q r s.
      p = q @ tl r @ tl s \<and>
      (\<exists>u v w. walk G u q v \<and> closed_walk G v r \<and> walk G v s w) \<and>
      distinct q"
    by blast
  hence "\<exists>qrs. is_walk_closed_walk_decomp G p qrs"
    by simp
  thus ?thesis
    unfolding walk_closed_walk_decomp_def
    ..
qed

lemma (in graph) walk_closed_walk_decompE_2:
  assumes p_walk: "walk G u p v"
  assumes p_not_distinct: "\<not> distinct p"
  assumes qrs_def: "walk_closed_walk_decomp G p = (q, r, s)"
  obtains
    "p = q @ tl r @ tl s"
    "\<exists>w. walk G u q w \<and> closed_walk G w r \<and> walk G w s v"
    "distinct q"
proof -
  have "is_walk_closed_walk_decomp G p (q, r, s)"
    unfolding qrs_def[symmetric]
    using p_walk p_not_distinct
    by (rule walk_closed_walk_decomp_is_walk_closed_walk_decomp)
  then obtain u' w' v' where
    p_decomp: "p = q @ tl r @ tl s" and
    q_distinct: "distinct q" and
    walks: "walk G u' q w'"
    "closed_walk G w' r"
    "walk G w' s v'"
    by auto
  hence "walk G u' p v'"
    by (auto simp add: p_decomp intro: walk_append_append_is_walk)
  hence "u' = u" "v' = v"
    using p_walk
    by (simp add: walk_def)+
  hence "\<exists>w. walk G u q w \<and> closed_walk G w r \<and> walk G w s v"
    using walks
    by blast
  with p_decomp
  show ?thesis
    using q_distinct
    by (rule that)
qed

subsection \<open>Walks in subgraphs/supergraphs\<close>

lemma (in subgraph) consistent_seq_in_subgraph_implies_consistent_seq_in_supergraph:
  assumes "consistent_seq H p"
  shows "consistent_seq G p"
  using assms vertices_subset edges_subset
  by (induction p rule: walk_induct) auto

lemma (in subgraph) walk_subgraph_is_walk_supergraph:
  assumes "walk H u p v"
  shows "walk G u p v"
  using assms
  by (auto simp add: walk_def intro: consistent_seq_in_subgraph_implies_consistent_seq_in_supergraph)

lemma (in induced_subgraph) walk_supergraph_is_walk_subgraph:
  assumes "walk G u p w"
  assumes "set p \<subseteq> V"
  shows "walk H u p w"
  using assms
  by (induction p arbitrary: u rule: walk_induct) (auto simp add: walk_def induced)
  
section \<open>Trails\<close>

text \<open>A trail is a walk in which all edges are distinct.\<close>

definition trail :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a walk \<Rightarrow> 'a \<Rightarrow> bool" where
  "trail G u p v \<equiv> walk G u p v \<and> distinct (walk_edges p)"

text \<open>A trail is closed if its endpoints are the same.\<close>

abbreviation closed_trail :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a walk \<Rightarrow> bool" where
  "closed_trail G v c \<equiv> trail G v c v \<and> Suc 0 < length c"

subsection \<open>Basic Lemmas\<close>

lemma closed_trail_implies_Cons:
  assumes "closed_trail G v c"
  shows "c = v # tl c"
  using assms
  by (simp add: trail_def walk_def)

lemma closed_trail_implies_tl_non_empty:
  assumes "closed_trail G v c"
  shows "tl c \<noteq> []"
  using assms
  by (simp add: tl_non_empty_conv)

(**)
subsection \<open>\<close>

lemma (in graph) trail_in_vertices:
  assumes "trail G u p v"
  assumes "w \<in> set p"
  shows "w \<in> vertices G"
  using assms
  by (auto simp add: trail_def intro: walk_in_vertices)

lemma (in graph) trail_hd_in_vertices:
  assumes "trail G u p v"
  shows "u \<in> vertices G"
  using assms
  by (auto simp add: trail_def intro: walk_hd_in_vertices)

lemma (in graph) trail_last_in_vertices:
  assumes "trail G u p v"
  shows "v \<in> vertices G"
  using assms
  by (auto simp add: trail_def intro: walk_last_in_vertices)

lemma (in graph) closed_trail_tl_hd_in_vertices:
  assumes "closed_trail G v c"
  shows "hd (tl c) \<in> vertices G"
proof -
  have "hd (tl c) \<in> set (tl c)"
    using assms
    by (intro closed_trail_implies_tl_non_empty hd_in_set)
  hence "hd (tl c) \<in> set c"
    by (auto intro: closed_trail_implies_tl_non_empty list.set_sel(2))
  with assms
  show ?thesis
    by (blast intro: trail_in_vertices)
qed

subsection \<open>Prefixes/suffixes of trails\<close>

lemma (in graph) trail_prefix_is_trail:
  notes trail_def [simp]
  assumes p_non_empty: "p \<noteq> []"
  assumes p_append_q_trail: "trail G u (p @ q) v"
  shows "trail G u p (last p)"
proof -
  have "walk G u p (last p)"
    using assms
    by (auto intro: walk_prefix_is_walk)
  moreover have "distinct (walk_edges p)"
    using p_append_q_trail p_non_empty
    by (simp add: walk_edges_append)
  ultimately show ?thesis
    by simp
qed

lemma (in graph) trail_suffix_is_trail:
  notes trail_def [simp]
  assumes q_non_empty: "q \<noteq> []"
  assumes p_append_q_trail: "trail G u (p @ q) v"
  shows "trail G (hd q) q v"
proof -
  have "walk G (hd q) q v"
    using assms
    by (auto intro: walk_suffix_is_walk)
  moreover have "distinct (walk_edges q)"
    using p_append_q_trail
    by (simp add: walk_edges_append_2[OF q_non_empty])
  ultimately show ?thesis
    by simp
qed

subsection \<open>Reversing trails\<close>

lemma (in graph) trail_rev_is_trail:
  assumes "trail G u p v"
  shows "trail G v (rev p) u"
proof -
  have "walk_edges (rev p) = rev (walk_edges p)"
    using walk_edges_rev[symmetric]
    .
  moreover have "distinct ..."
    using assms
    by (simp add: trail_def)
  ultimately have "distinct (walk_edges (rev p))"
    by simp
  moreover have "walk G v (rev p) u"
    using assms
    by (intro walk_rev_is_walk) (simp add: trail_def)
  ultimately show ?thesis
    by (simp add: trail_def)
qed

lemma (in graph) closed_trail_rev_is_closed_trail:
  assumes "closed_trail G v c"
  shows "closed_trail G v (rev c)"
proof -
  have "trail G v (rev c) v"
    using assms
    by (intro trail_rev_is_trail) simp
  moreover have "Suc 0 < length (rev c)"
    using assms
    by simp
  ultimately show ?thesis
    by simp
qed

subsection \<open>Convenience Lemmas\<close>

lemma (in graph) closed_trail_hd_tl_hd_is_trail:
  assumes "closed_trail G v c"
  shows "trail G v [v, hd (tl c)] (hd (tl c))"
proof -
  have "c = [v, hd (tl c)] @ tl (tl c)"
    using assms closed_trail_implies_tl_non_empty
    by (fastforce simp add: closed_trail_implies_Cons)
  hence "trail G v ([v, hd (tl c)] @ tl (tl c)) v"
    using assms
    by simp
  from trail_prefix_is_trail[OF _ this]
  show ?thesis
    by simp
qed

lemma (in graph) closed_trail_tl_rev_is_trail:
  assumes "closed_trail G v c"
  shows "trail G v (rev (tl c)) (hd (tl c))"
proof -
  have "c = [v] @ tl c"
    using assms
    by (auto simp add: closed_trail_implies_Cons)
  hence "trail G v ([v] @ tl c) v"
    using assms
    by simp
  hence "trail G (hd (tl c)) (tl c) v"
    using assms
    by (intro closed_trail_implies_tl_non_empty trail_suffix_is_trail)
  thus ?thesis
    by (rule trail_rev_is_trail)
qed

lemma (in graph) closed_trail_hd_tl_hd_neq_tl_rev:
  assumes "closed_trail G v c"
  shows "[v, hd (tl c)] \<noteq> rev (tl c)"
proof (rule ccontr)
  define u where
    "u = hd (tl c)"
  assume "\<not> [v, u] \<noteq> rev (tl c)"
  hence "rev [u, v] = rev (tl c)"
    by simp
  hence "[u, v] = tl c"
    by blast
  hence "c = [v, u, v]"
    using assms
    by (auto simp add: closed_trail_implies_Cons)
  hence "\<not> distinct (walk_edges c)"
    by auto
  hence "\<not> trail G v c v"
    by (simp add: trail_def)
  thus "False"
    using assms
    by simp
qed

section \<open>Paths\<close>

(* This section is largely based on the formalization of directed graphs (Graph_Theory). *)

text \<open>A path is a walk in which all vertices are distinct.\<close>

definition path :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a walk \<Rightarrow> 'a \<Rightarrow> bool" where
  "path G u p v \<equiv> walk G u p v \<and> distinct p"

(**)
subsection \<open>\<close>

lemma (in finite_graph) path_length_le_card_vertices:
  assumes "path G u p v"
  shows "length p \<le> card (vertices G)"
proof -
  have "length p = card (set p)"
    using assms
    by (intro distinct_card[symmetric]) (simp add: path_def)
  also have "... \<le> card (vertices G)"
    using vertices_finite assms
    by (auto simp add: path_def intro: walk_in_vertices card_mono)
  finally show ?thesis
    .
qed

lemma (in finite_graph) path_triples_finite:
  shows "finite {(u, p, v). path G u p v}"
proof (rule finite_subset)
  have "\<And>u p v. walk G u p v \<Longrightarrow> distinct p \<Longrightarrow> length p \<le> card (vertices G)"
    by (intro path_length_le_card_vertices) (simp add: path_def)
  thus
    "{(u, p, v). path G u p v} \<subseteq>
      vertices G \<times> {p. set p \<subseteq> vertices G \<and> length p \<le> card (vertices G)} \<times> vertices G"
    by (auto simp add: path_def intro: walk_hd_in_vertices walk_in_vertices walk_last_in_vertices)
  show "finite ..."
    using vertices_finite
    by (intro finite_lists_length_le finite_cartesian_product)
qed

lemma (in finite_graph) paths_finite:
  shows "finite {p. path G u p v}"
proof -
  have "{p. path G u p v} \<subseteq> (fst \<circ> snd) ` {(u, p, v). path G u p v}"
    by (auto simp add: image_def)
  with path_triples_finite
  show ?thesis
    by (rule finite_surj)
qed

subsection \<open>Transforming walks into paths\<close>

function (in graph) walk_to_path :: "'a walk \<Rightarrow> 'a walk" where
  "walk_to_path p =
    (if (\<exists>u v. walk G u p v) \<and> \<not> distinct p
     then let (q, r, s) = walk_closed_walk_decomp G p in walk_to_path (q @ tl s)
     else p)"
  by auto

termination (in graph) walk_to_path
proof (relation "measure length")
  fix p qrs rs q r s
  assume
    p_not_path: "(\<exists>u v. walk G u p v) \<and> \<not> distinct p" and
    assms: "qrs = walk_closed_walk_decomp G p"
    "(q, rs) = qrs"
    "(r, s) = rs"
  then obtain u v where
    p_walk: "walk G u p v"
    by blast
  hence "(q, r, s) = walk_closed_walk_decomp G p"
    using assms
    by simp
  then obtain
    "p = q @ tl r @ tl s"
    "Suc 0 < length r"
    using p_walk p_not_path
    by (elim walk_closed_walk_decompE_2) auto
  thus "(q @ tl s, p) \<in> measure length"
    by auto
qed simp

lemma (in graph) walk_to_path_induct [consumes 1, case_names path decomp]:
  assumes "walk G u p v"
  assumes distinct: "\<And>p. \<lbrakk> walk G u p v; distinct p \<rbrakk> \<Longrightarrow> P p"
  assumes
    decomp: "\<And>p q r s. \<lbrakk> walk G u p v; \<not> distinct p;
      walk_closed_walk_decomp G p = (q, r, s); P (q @ tl s) \<rbrakk> \<Longrightarrow> P p"
  shows "P p"
  using assms(1)
proof (induct "length p" arbitrary: p rule: less_induct)
  case less
  show ?case
  proof (cases "distinct p")
    case True
    with less.prems
    show ?thesis
      by (rule distinct)
  next
    case False
    obtain q r s where
      qrs_def: "walk_closed_walk_decomp G p = (q, r, s)"
      by (cases "walk_closed_walk_decomp G p")
    with less.prems False
    obtain
      "p = q @ tl r @ tl s"
      "\<exists>w. walk G u q w \<and> closed_walk G w r \<and> walk G w s v"
      by (elim walk_closed_walk_decompE_2)
    hence
      "length (q @ tl s) < length p"
      "walk G u (q @ tl s) v"
      by (auto simp add: tl_non_empty_conv intro: walk_append_is_walk)
    hence "P (q @ tl s)"
      by (rule less.hyps)
    with less.prems False qrs_def
    show ?thesis
      by (rule decomp)
  qed
qed

lemma (in graph) walk_to_path_is_path:
  assumes "walk G u p v"
  shows "path G u (walk_to_path p) v"
  using assms
  by (induction rule: walk_to_path_induct) (auto simp add: path_def)

section \<open>Reachability\<close>

definition reachable :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "reachable G u v \<equiv> \<exists>p. walk G u p v"

definition connected :: "'a graph \<Rightarrow> bool" where
  "connected G \<equiv> \<forall>u\<in>vertices G. \<forall>v\<in>vertices G. reachable G u v"

lemma reachable_trans:
  assumes "reachable G u v"
  assumes "reachable G v w"
  shows "reachable G u w"
proof -
  obtain p q where
    "walk G u p v"
    "walk G v q w"
    using assms
    by (auto simp add: reachable_def)
  hence "walk G u (p @ (tl q)) w"
    by (rule walk_append_is_walk)
  thus ?thesis
    by (auto simp add: reachable_def)
qed

lemma (in graph) reachable_symmetric:
  assumes "reachable G u v"
  shows "reachable G v u"
proof -
  obtain p where
    "walk G u p v"
    using assms
    by (auto simp add: reachable_def)
  hence "walk G v (rev p) u"
    by (rule walk_rev_is_walk)
  thus ?thesis
    by (auto simp add: reachable_def)
qed

lemma (in graph) not_reachable_if_not_in_vertices:
  assumes "u \<notin> vertices G \<or> v \<notin> vertices G"
  shows "\<not> reachable G u v"
proof (rule ccontr)
  assume "\<not> \<not> reachable G u v"
  then obtain p where
    "walk G u p v"
    by (auto simp add: reachable_def)
  hence
    "u \<in> vertices G"
    "v \<in> vertices G"
    by (auto intro: walk_hd_in_vertices walk_last_in_vertices)
  thus "False"
    using assms
    by simp
qed

lemma (in subgraph) not_reachable_in_subgraph_if_not_reachable_in_supergraph:
  assumes "\<not> reachable G u v"
  shows "\<not> reachable H u v"
  using assms
  by (auto simp add: reachable_def intro: walk_subgraph_is_walk_supergraph)

lemmas (in induced_subgraph) not_reachable_in_subgraph_if_not_reachable_in_supergraph =
  not_reachable_in_subgraph_if_not_reachable_in_supergraph

end