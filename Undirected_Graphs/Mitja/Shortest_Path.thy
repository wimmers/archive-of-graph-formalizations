theory Shortest_Path
  imports
    Weighted_Graph
begin

section \<open>Shortest walk cost\<close>

definition shortest_walk_cost :: "'a graph \<Rightarrow> 'a cost_fun \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ereal" where
  "shortest_walk_cost G f u v \<equiv> INF p\<in>{p. walk G u p v}. ereal (walk_cost f p)"

definition is_shortest_walk :: "'a graph \<Rightarrow> 'a cost_fun \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_shortest_walk G f u p v \<equiv> walk G u p v \<and> walk_cost f p = shortest_walk_cost G f u v"

lemma is_shortest_walkI:
  assumes "walk G u p v"
  assumes "walk_cost f p = shortest_walk_cost G f u v"
  shows "is_shortest_walk G f u p v"
  using assms
  by (simp add: is_shortest_walk_def)

subsection \<open>Basic Lemmas\<close>

lemma (in graph) shortest_walk_cost_symmetric_aux:
  shows
    "(\<lambda>p. ereal (walk_cost f p)) ` {p. walk G u p v} \<subseteq>
      (\<lambda>p. ereal (walk_cost f p)) ` {p. walk G v p u}"
    (is "?A \<subseteq> ?B")
proof
  fix x
  assume "x \<in> ?A"
  then obtain p where
    "p \<in> {p. walk G u p v}"
    "x = walk_cost f p"
    by blast
  hence
    "(rev p) \<in> {p. walk G v p u}"
    "x = walk_cost f (rev p)"
    by (simp add: walk_rev)+
  thus "x \<in> ?B"
    by blast
qed

lemma (in graph) shortest_walk_cost_symmetric:
  shows "shortest_walk_cost G f u v = shortest_walk_cost G f v u"
proof -
  have
    "(\<lambda>p. ereal (walk_cost f p)) ` {p. walk G u p v} =
      (\<lambda>p. ereal (walk_cost f p)) ` {p. walk G v p u}"
    (is "?A = ?B")
  proof
    show "?A \<subseteq> ?B"
      using shortest_walk_cost_symmetric_aux[where ?u = u and ?v = v]
      by simp
  next
    show "?B \<subseteq> ?A"
      using shortest_walk_cost_symmetric_aux[where ?u = v and ?v = u]
      by simp
  qed
  thus ?thesis
    by (simp add: shortest_walk_cost_def)
qed

lemma shortest_walk_cost_non_negative_if_cost_non_negative:
  assumes "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
  shows "0 \<le> shortest_walk_cost G f u v"
proof -
  { fix p
    assume "p \<in> {p. walk G u p v}"
    hence "0 \<le> walk_cost f p"
      using assms
      by (blast intro: walk_cost_non_negative_if_cost_non_negative) }
  thus ?thesis
    by (auto simp add: shortest_walk_cost_def intro: INF_greatest)
qed

lemma shortest_walk_cost_le_walk_cost:
  assumes "walk G u p v"
  shows "shortest_walk_cost G f u v \<le> walk_cost f p"
  using assms
  by (auto simp add: shortest_walk_cost_def intro: INF_lower)

lemma (in graph) shortest_walk_cost_edge_le_cost:
  assumes "{u, v} \<in> edges G"
  shows "shortest_walk_cost G f u v \<le> f {u, v}"
proof -
  have "walk G u [u, v] v"
    using assms
    by (rule edge_is_walk)
  hence "shortest_walk_cost G f u v \<le> walk_cost f [u, v]"
    by (rule shortest_walk_cost_le_walk_cost)
  also have "... = f {u, v}"
    by (simp add: walk_cost_def)
  finally show ?thesis
    .
qed

lemma shortest_walk_cost_reachable_conv:
  shows "shortest_walk_cost G f u v \<noteq> \<infinity> = reachable G u v"
proof
  assume shortest_walk_cost_finite: "shortest_walk_cost G f u v \<noteq> \<infinity>"
  show "reachable G u v"
  proof (rule ccontr)
    assume "\<not> reachable G u v"
    hence "{p. walk G u p v} = {}"
      by (simp add: reachable_def)
    thus "False"
      using shortest_walk_cost_finite
      by (simp add: shortest_walk_cost_def top_ereal_def)
  qed
next
  assume "reachable G u v"
  then obtain p where
    "walk G u p v"
    by (auto simp add: reachable_def)
  hence "shortest_walk_cost G f u v \<le> walk_cost f p"
    by (rule shortest_walk_cost_le_walk_cost)
  also have "... < \<infinity>"
    by (simp add: walk_cost_def)
  finally show "shortest_walk_cost G f u v \<noteq> \<infinity>"
    by simp
qed

lemma singleton_is_shortest_walk:
  assumes f_non_negative: "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
  assumes v_in_vertices: "v \<in> vertices G"
  shows "is_shortest_walk G f v [v] v"
proof (intro antisym is_shortest_walkI)
  show v_walk: "walk G v [v] v"
    using v_in_vertices
    by (rule singleton_is_walk)
  have "walk_cost f [v] = 0"
    by (simp add: walk_cost_def)
  also have "... \<le> shortest_walk_cost G f v v"
    unfolding zero_ereal_def[symmetric]
    using f_non_negative
    by (rule shortest_walk_cost_non_negative_if_cost_non_negative)
  finally show "walk_cost f [v] \<le> shortest_walk_cost G f v v"
    .
  show "shortest_walk_cost G f v v \<le> walk_cost f [v]"
    using v_walk
    by (rule shortest_walk_cost_le_walk_cost)
qed

subsection \<open>Shortest path cost\<close>

(* This subsection is largely based on the formalization of directed graphs (Graph_Theory). *)

lemma (in graph) shortest_walk_cost_ge_shortest_walk_to_path_cost:
  assumes "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
  shows
    "(INF p\<in>{p. walk G u p v}. ereal (walk_cost f (walk_to_path p))) \<le>
      shortest_walk_cost G f u v"
proof -
  { fix p
    assume "p \<in> {p. walk G u p v}"
    hence "walk_cost f (walk_to_path p) \<le> walk_cost f p"
      using assms
      by (intro walk_cost_ge_walk_to_path_cost) simp+ }
  thus ?thesis
    by (fastforce simp add: shortest_walk_cost_def intro: INF_mono)
qed

lemma (in graph) shortest_walk_cost_eq_shortest_path_cost:
  assumes "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
  shows "shortest_walk_cost G f u v = (INF p\<in>{p. path G u p v}. ereal (walk_cost f p))"
proof (rule antisym)
  define walks where "walks = {p. walk G u p v}"
  define paths where "paths = {p. path G u p v}"

  have "paths \<subseteq> walks"
    by (auto simp add: walks_def paths_def path_def)
  thus "shortest_walk_cost G f u v \<le> (INF p\<in>{p. path G u p v}. ereal (walk_cost f p))"
    unfolding shortest_walk_cost_def walks_def[symmetric] paths_def[symmetric]
    by (rule INF_superset_mono) simp  

  have "walk_to_path ` walks \<subseteq> paths"
    unfolding walks_def paths_def
    by (blast intro: walk_to_path_is_path)
  hence
    "(INF p\<in>paths. ereal (walk_cost f p)) \<le>
      (INF p\<in>walk_to_path ` walks. ereal (walk_cost f p))"
    by (rule INF_superset_mono) simp
  also have "... = (INF p\<in>walks. ereal (walk_cost f (walk_to_path p)))"
    unfolding image_image
    by simp
  also have "... \<le> (INF p\<in>walks. ereal (walk_cost f p))" 
    unfolding walks_def shortest_walk_cost_def[symmetric]
    using assms
    by (rule shortest_walk_cost_ge_shortest_walk_to_path_cost)
  finally show "(INF p\<in>{p. path G u p v}. ereal (walk_cost f p)) \<le> shortest_walk_cost G f u v"
    by (simp add: walks_def paths_def shortest_walk_cost_def)
qed

lemma (in finite_graph) shortest_walk_cost_path:
  assumes reachable: "reachable G u v"
  assumes f_non_negative: "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
  shows "\<exists>p. path G u p v \<and> walk_cost f p = shortest_walk_cost G f u v"
proof -
  have paths_non_empty: "{p. path G u p v} \<noteq> {}"
    (is "?A \<noteq> {}")
    using reachable
    by (auto simp add: reachable_def intro: walk_to_path_is_path)

  have "shortest_walk_cost G f u v = (INF p\<in>?A. ereal (walk_cost f p))"
    using f_non_negative
    by (rule shortest_walk_cost_eq_shortest_path_cost)
  also have "... \<in> (\<lambda>p. ereal (walk_cost f p)) ` ?A"
    using paths_finite paths_non_empty
    by (rule INF_in_image)
  finally show ?thesis
    by (auto simp add: image_def)
qed

subsection \<open>Triangle inequality\<close>

lemma (in finite_graph) shortest_walk_cost_triangle_inequality_case_real:
  assumes f_non_negative: "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
  assumes
    assm: "shortest_walk_cost G f u v + shortest_walk_cost G f v w <
      shortest_walk_cost G f u w"
    (is "?b + ?c < ?a")
  assumes real: "shortest_walk_cost G f u w = ereal r"
  shows "False"
proof -
  have
    "?b \<noteq> \<infinity>"
    "?c \<noteq> \<infinity>"
    using assm real
    by auto
  hence
    "reachable G u v"
    "reachable G v w"
    by (simp add: shortest_walk_cost_reachable_conv)+
  hence
    "\<exists>p. path G u p v \<and> walk_cost f p = ?b"
    "\<exists>p. path G v p w \<and> walk_cost f p = ?c"
    using f_non_negative
    by (auto intro: shortest_walk_cost_path)
  then obtain p q where
    p_walk: "walk G u p v" and
    p_walk_cost: "walk_cost f p = ?b" and
    q_walk: "walk G v q w" and
    q_walk_cost: "walk_cost f q = ?c"
    by (auto simp add: path_def)

  have "walk G u (p @ tl q) w"
    using p_walk q_walk
    by (rule walk_append_is_walk)
  hence "?a \<le> walk_cost f (p @ tl q)"
    by (rule shortest_walk_cost_le_walk_cost)
  also have "... = walk_cost f p + walk_cost f q"
    using p_walk q_walk
    by (auto simp add: walk_def intro: walk_cost_append_2)
  finally have "?a \<le> ?b + ?c"
    by (simp add: plus_ereal.simps(1)[symmetric] p_walk_cost q_walk_cost)
  thus ?thesis
    using assm
    by simp
qed

lemma (in finite_graph) shortest_walk_cost_triangle_inequality_case_PInf:
  assumes "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
  assumes assm: "shortest_walk_cost G f u v + shortest_walk_cost G f v w < shortest_walk_cost G f u w"
    (is "?b + ?c < ?a")
  assumes PInf: "shortest_walk_cost G f u w = \<infinity>"
  shows "False"
proof -
  have
    "?b \<noteq> \<infinity>"
    "?c \<noteq> \<infinity>"
    using assm PInf
    by simp+
  hence
    "reachable G u v"
    "reachable G v w"
    by (simp add: shortest_walk_cost_reachable_conv)+
  hence "reachable G u w"
    by (rule reachable_trans)
  hence "shortest_walk_cost G f u w \<noteq> \<infinity>"
    by (simp add: shortest_walk_cost_reachable_conv)
  thus ?thesis
    using PInf
    by simp
qed

lemma (in finite_graph) shortest_walk_cost_triangle_inequality:
  assumes "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
  shows "shortest_walk_cost G f u w \<le> shortest_walk_cost G f u v + shortest_walk_cost G f v w"
    (is "?a \<le> ?b + ?c")
proof (rule ccontr)
  assume "\<not> ?a \<le> ?b + ?c"
  hence assm: "?b + ?c < ?a"
    by simp
  show "False"
  proof (cases ?a)
    case (real r)
    with assms assm
    show ?thesis
      by (rule shortest_walk_cost_triangle_inequality_case_real)
  next
    case PInf
    with assms assm
    show ?thesis
      by (rule shortest_walk_cost_triangle_inequality_case_PInf)
  next
    case MInf
    thus ?thesis
      using assm
      by simp
  qed
qed

subsection \<open>Decomposing shortest walks\<close>

lemma (in finite_graph) shortest_walk_cost_walk_vertex_decomp:
  assumes f_non_negative: "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
  assumes p_shortest_walk: "is_shortest_walk G f u p w"
  assumes v_in_p: "v \<in> set p"
  assumes qr_def: "walk_vertex_decomp G p v = (q, r)"
  shows "shortest_walk_cost G f u w = shortest_walk_cost G f u v + shortest_walk_cost G f v w"
    (is "?a = ?b + ?c")
proof (rule antisym)
  show "?a \<le> ?b + ?c"
    using f_non_negative
    by (rule shortest_walk_cost_triangle_inequality)
next
  have
    p_decomp: "p = q @ tl r" and
    q_walk: "walk G u q v" and
    r_walk: "walk G v r w"
    using p_shortest_walk v_in_p qr_def
    by (auto simp add: is_shortest_walk_def elim: walk_vertex_decompE_2)

  have "?b + ?c \<le> walk_cost f q + walk_cost f r"
    unfolding plus_ereal.simps(1)[symmetric]
    using q_walk r_walk
    by (intro shortest_walk_cost_le_walk_cost add_mono)
  also have "... = walk_cost f (q @ tl r)"
    using q_walk r_walk
    by (auto simp add: walk_def intro: walk_cost_append_2[symmetric])
  finally show "?b + ?c \<le> ?a"
    using p_shortest_walk
    by (simp add: p_decomp is_shortest_walk_def)
qed

subsection \<open>Shortest walks in subgraphs/supergraphs\<close>

lemma (in subgraph) shortest_walk_cost_subgraph_ge_shortest_walk_cost_supergraph:
  shows "shortest_walk_cost G f u v \<le> shortest_walk_cost H f u v"
proof -
  have "{p. walk H u p v} \<subseteq> {p. walk G u p v}"
    by (blast intro: walk_subgraph_is_walk_supergraph)
  hence
    "(\<lambda>p. ereal (walk_cost f p)) ` {p. walk H u p v} \<subseteq>
      (\<lambda>p. ereal (walk_cost f p)) ` {p. walk G u p v}"
    (is "?A \<subseteq> ?B")
    by blast
  hence "Inf ?B \<le> Inf ?A"
    by (rule Inf_superset_mono)
  thus ?thesis
    by (simp add: shortest_walk_cost_def)
qed

lemmas (in induced_subgraph) shortest_walk_cost_subgraph_ge_shortest_walk_cost_supergraph =
  shortest_walk_cost_subgraph_ge_shortest_walk_cost_supergraph

lemma (in induced_subgraph) shortest_walk_supergraph_is_shortest_walk_subgraph:
  assumes p_shortest_walk: "is_shortest_walk G f u p v"
  assumes "set p \<subseteq> V"
  shows "is_shortest_walk H f u p v"
proof (intro antisym is_shortest_walkI)
  show p_walk: "walk H u p v"
    using assms
    by (auto simp add: is_shortest_walk_def intro: walk_supergraph_is_walk_subgraph)
  show "walk_cost f p \<le> shortest_walk_cost H f u v"
    using p_shortest_walk shortest_walk_cost_subgraph_ge_shortest_walk_cost_supergraph
    by (simp add: is_shortest_walk_def)
  show "shortest_walk_cost H f u v \<le> walk_cost f p"
    using p_walk
    by (rule shortest_walk_cost_le_walk_cost)
qed

subsection \<open>Convenience Lemmas\<close>

lemma (in graph) shortest_walk_cost_infinite_if_not_in_vertices:
  assumes "v \<notin> vertices G"
  shows "shortest_walk_cost G f u v = \<infinity>"
proof (rule ccontr)
  assume "shortest_walk_cost G f u v \<noteq> \<infinity>"
  hence "reachable G u v"
    by (simp add: shortest_walk_cost_reachable_conv)
  then obtain p where
    "walk G u p v"
    by (auto simp add: reachable_def)
  hence "v \<in> vertices G"
    by (rule walk_last_in_vertices)
  thus "False"
    using assms
    by simp
qed

lemma (in finite_graph) shortest_walk_cost_walk:
  assumes p_walk: "walk G u p v"
  assumes f_non_negative: "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
  shows "\<exists>q. is_shortest_walk G f u q v \<and> walk_cost f q \<le> walk_cost f p"
proof -
  have "reachable G u v"
    using p_walk
    by (auto simp add: reachable_def)
  hence "\<exists>q. path G u q v \<and> walk_cost f q = shortest_walk_cost G f u v"
    using f_non_negative
    by (rule shortest_walk_cost_path)
  then obtain q where
    q_walk: "walk G u q v" and
    q_walk_cost: "walk_cost f q = shortest_walk_cost G f u v"
    by (auto simp add: path_def)

  have "walk_cost f q \<le> walk_cost f p"
    unfolding ereal_less_eq(3)[symmetric] q_walk_cost
    using p_walk
    by (rule shortest_walk_cost_le_walk_cost)
  moreover have "is_shortest_walk G f u q v"
    using q_walk q_walk_cost
    by (rule is_shortest_walkI)
  ultimately show ?thesis
    by blast
qed

definition shortest_walk :: "'a graph \<Rightarrow> 'a cost_fun \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "shortest_walk G f u v \<equiv> SOME p. is_shortest_walk G f u p v"

lemma (in finite_graph) shortest_walk_is_shortest_walk:
  assumes "reachable G u v"
  assumes "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
  shows "is_shortest_walk G f u (shortest_walk G f u v) v"
proof -
  have "\<exists>p. path G u p v \<and> walk_cost f p = shortest_walk_cost G f u v"
    using assms
    by (rule shortest_walk_cost_path)
  hence "\<exists>p. walk G u p v \<and> walk_cost f p = shortest_walk_cost G f u v"
    by (auto simp add: path_def)
  hence "\<exists>p. is_shortest_walk G f u p v"
    by (auto simp add: is_shortest_walk_def)
  thus ?thesis
    unfolding shortest_walk_def
    ..
qed

section \<open>Shortest walk length\<close>

(*
TODO: Is there a way to define shortest_walk_length as

definition shortest_walk_length :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> enat" where
  "shortest_walk_length G u v \<equiv> INF p\<in>{p. walk G u p v}. enat (walk_length p)"

and prove

  "ereal_of_enat (shortest_walk_length G u v) = shortest_walk_cost G (\<lambda>_. 1) u v"

If not, would it be better to change the type of shortest_walk_cost to enat?
*)

abbreviation shortest_walk_length :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ereal" where
  "shortest_walk_length G \<equiv> shortest_walk_cost G (\<lambda>_. 1)"

lemma walk_length_eq_walk_cost:
  shows "walk_length p = walk_cost (\<lambda>_. 1) p"
proof (induction p rule: walk_induct)
case 1
  thus ?case
    by simp
next
  case (2 _)
  thus ?case
    by (simp add: walk_cost_def)
next
  case (3 v v' vs)
  define f :: "'a set \<Rightarrow> real" where
    "f = (\<lambda>_. 1)"
  have "walk_length (v # v' # vs) = 1 + walk_length (v' # vs)"
    by simp
  also have "... = 1 + walk_cost f (v' # vs)"
    by (simp add: "3.IH" f_def)
  also have "... = f {v, v'} + walk_edges_cost f (walk_edges (v' # vs))"
    by (simp add: f_def walk_cost_def)
  also have "... = walk_cost f (v # v' # vs)"
    by (simp add: walk_cost_def)
  finally show ?case
    by (simp add: f_def)
qed

lemma (in finite_graph) shortest_walk_length_eq_1:
  shows
    "0 < shortest_walk_length G u v \<and> shortest_walk_length G u v \<le> 1 \<longleftrightarrow>
      shortest_walk_length G u v = 1"
proof
  assume assm: "0 < shortest_walk_length G u v \<and> shortest_walk_length G u v \<le> 1"
  define f :: "'a set \<Rightarrow> real" where
    "f = (\<lambda>_. 1)"
  have f_non_negative: "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
    by (simp add: f_def)

  have "shortest_walk_length G u v \<noteq> \<infinity>"
    using assm
    by auto
  hence "reachable G u v"
    by (simp add: shortest_walk_cost_reachable_conv)
  hence "\<exists>p. path G u p v \<and> walk_cost f p = shortest_walk_cost G f u v"
    using f_non_negative
    by (rule shortest_walk_cost_path)
  then obtain p where
    p_walk_cost: "walk_cost f p = shortest_walk_length G u v"
    by (auto simp add: f_def)
  hence
    "0 < walk_cost f p"
    "walk_cost f p \<le> 1"
    using assm
    by (simp add: ereal_less(2)[symmetric] ereal_less_eq(3)[symmetric] one_ereal_def)+
  hence
    "0 < walk_length p"
    "walk_length p \<le> 1"
    by (simp add: f_def walk_length_eq_walk_cost[symmetric])+
  hence "walk_length p = 1"
    by linarith
  hence "walk_cost f p = 1"
    by (simp add: walk_length_eq_walk_cost[symmetric] f_def)
  thus "shortest_walk_length G u v = 1"
    by (simp add: p_walk_cost[symmetric])
qed simp

lemma (in finite_graph) shortest_walk_length_eq_1_implies_edge:
  assumes "shortest_walk_length G u v = 1"
  shows "{u, v} \<in> edges G"
proof -
  define f :: "'a set \<Rightarrow> real" where
    "f = (\<lambda>_. 1)"
  have f_non_negative: "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
    by (simp add: f_def)

  have "shortest_walk_length G u v \<noteq> \<infinity>"
    using assms
    by simp
  hence "reachable G u v"
    by (simp add: shortest_walk_cost_reachable_conv)
  hence "\<exists>p. path G u p v \<and> walk_cost f p = shortest_walk_cost G f u v"
    using f_non_negative
    by (rule shortest_walk_cost_path)
  then obtain p where
    p_walk: "walk G u p v" and
    "walk_cost f p = 1"
    using assms
    by (auto simp add: path_def f_def)
  hence "walk_length p = 1"
    by (simp add: f_def walk_length_eq_walk_cost[symmetric])
  hence "length p = Suc 1"
    using p_walk
    by (simp add: walk_def walk_length)
  hence "p = [u, v]"
    using p_walk
    by (intro list_length_2) (simp add: walk_def)+
  thus ?thesis
    using p_walk
    by (simp add: edge_iff_walk)
qed

lemma (in finite_graph) shortest_walk_length_le_1_if_edge:
  assumes "{u, v} \<in> edges G"
  shows "shortest_walk_length G u v \<le> 1"
proof -
  have "walk G u [u, v] v"
    using assms
    by (rule edge_is_walk)
  hence "shortest_walk_length G u v \<le> walk_cost (\<lambda>_. 1) [u, v]"
    by (rule shortest_walk_cost_le_walk_cost)
  also have "... = 1"
    by (simp add: walk_cost_def)
  finally show ?thesis
    .
qed

lemma (in finite_graph) shortest_walk_length_ge_1_if_edge:
  assumes "{u, v} \<in> edges G"
  shows "1 \<le> shortest_walk_length G u v"
proof (rule ccontr)
  assume assm: "\<not> 1 \<le> shortest_walk_length G u v"
  define f :: "'a set \<Rightarrow> real" where
    "f = (\<lambda>_. 1)"
  have f_non_negative: "\<And>e. e \<in> edges G \<Longrightarrow> 0 \<le> f e"
    by (simp add: f_def)

  have "walk G u [u, v] v"
    using assms
    by (rule edge_is_walk)
  hence "reachable G u v"
    by (auto simp add: reachable_def)
  hence "\<exists>p. path G u p v \<and> walk_cost f p = shortest_walk_cost G f u v"
    using f_non_negative
    by (rule shortest_walk_cost_path)
  then obtain p where
    p_walk: "walk G u p v" and
    "walk_cost f p = shortest_walk_length G u v"
    by (auto simp add: path_def f_def)
  hence "walk_cost f p < 1"
    using assm
    by (simp add: ereal_less(3)[symmetric])
  hence "walk_length p = 0"
    unfolding f_def walk_length_eq_walk_cost[symmetric]
    by linarith
  hence "length p = 1"
    using p_walk
    by (simp add: walk_def walk_length)
  hence "p = [u] \<and> u = v"
    using p_walk
    by (intro list_length_1) (simp add: walk_def)+
  thus "False"
    using assms graph
    by auto
qed

lemma (in finite_graph) shortest_walk_length_eq_1_if_edge:
  assumes "{u, v} \<in> edges G"
  shows "shortest_walk_length G u v = 1"
proof (rule antisym)
  show "shortest_walk_length G u v \<le> 1"
    using assms
    by (rule shortest_walk_length_le_1_if_edge)
next
  show "1 \<le> shortest_walk_length G u v"
    using assms
    by (rule shortest_walk_length_ge_1_if_edge)
qed

lemma (in finite_graph) shortest_walk_length_eq_1_iff_edge:
  shows "shortest_walk_length G u v = 1 \<longleftrightarrow> {u, v} \<in> edges G"
proof
  show "shortest_walk_length G u v = 1 \<Longrightarrow> {u, v} \<in> edges G"
    using shortest_walk_length_eq_1_implies_edge
    .
next
  show "{u, v} \<in> edges G \<Longrightarrow> shortest_walk_length G u v = 1"
    using shortest_walk_length_eq_1_if_edge
    .
qed

end