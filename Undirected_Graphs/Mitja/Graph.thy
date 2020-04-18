theory Graph
  imports Main
begin

section \<open>Graphs\<close>

record 'a graph =
  vertices :: "'a set"
  edges :: "'a set set"

locale graph =
  fixes G :: "'a graph"
  assumes graph: "\<forall>e\<in>edges G. \<exists>u v. u \<in> vertices G \<and> v \<in> vertices G \<and> u \<noteq> v \<and> e = {u, v}"

lemma (in graph) Union_edges_subset_vertices:
  shows "\<Union> (edges G) \<subseteq> vertices G"
  using graph
  by fastforce

lemma (in graph) edge_subset_vertices:
  assumes "e \<in> edges G"
  shows "e \<subseteq> vertices G"
  using assms Union_edges_subset_vertices
  by blast
  
locale finite_graph = graph G for G +
  assumes vertices_finite: "finite (vertices G)"

lemma (in finite_graph) edges_finite:
  shows "finite (edges G)"
proof -
  have "\<Union> (edges G) \<subseteq> vertices G"
    using Union_edges_subset_vertices
    by simp
  moreover have "finite ..."
    using vertices_finite
    by simp
  ultimately have "finite (\<Union> (edges G))"
    by (rule finite_subset)
  thus ?thesis
    by (rule finite_UnionD)
qed

section \<open>Subgraphs\<close>

locale subgraph = supergraph: graph G + subgraph: graph H for G H +
  assumes vertices_subset: "vertices H \<subseteq> vertices G"
  assumes edges_subset: "edges H \<subseteq> edges G"

locale induced_subgraph = graph G for G +
  fixes H :: "'a graph"
  fixes V :: "'a set"
  assumes induced: "H = \<lparr>vertices = vertices G \<inter> V, edges = {e \<in> edges G. e \<subseteq> V}\<rparr>"

sublocale induced_subgraph \<subseteq> subgraph
proof (rule subgraph.intro)
  show "graph G"
    using graph_axioms
    .
next
  { fix e
    assume "e \<in> edges H"
    hence
      "e \<in> edges G"
      "e \<subseteq> V"
      by (simp add: induced)+
    then obtain u v where
      "u \<noteq> v" and
      "e = {u, v}" and
      "u \<in> vertices H"
      "v \<in> vertices H"
      using graph
      by (auto simp add: induced)
    hence "\<exists>u v. u \<in> vertices H \<and> v \<in> vertices H \<and> u \<noteq> v \<and> e = {u, v}"
      by blast }
  thus "graph H"
    by (simp add: graph_def)
next
  have "vertices H \<subseteq> vertices G"
    by (simp add: induced)
  moreover have "edges H \<subseteq> edges G"
    by (simp add: induced)
  ultimately show "subgraph_axioms G H"
    by (rule subgraph_axioms.intro)
qed

lemmas (in induced_subgraph) vertices_subset = vertices_subset
lemmas (in induced_subgraph) edges_subset = edges_subset
lemmas (in induced_subgraph) subgraph_graph_axioms = subgraph.graph_axioms

lemma (in induced_subgraph) vertices_subgraph_subset:
  shows "vertices H \<subseteq> V"
  by (simp add: induced)

lemma (in induced_subgraph) vertices_subgraph_eq:
  assumes "V \<subseteq> vertices G"
  shows "vertices H = V"
  using assms
  by (auto simp add: induced)

lemma induced_subgraph_trans:
  assumes G_induced_subgraph: "induced_subgraph F G V"
  assumes H_induced_subgraph: "induced_subgraph G H W"
  shows "induced_subgraph F H (V \<inter> W)"
proof (rule induced_subgraph.intro)
  show "graph F"
    using G_induced_subgraph
    by (rule induced_subgraph.axioms(1))
next
  have
    "vertices H = vertices G \<inter> W"
    "edges H = {e \<in> edges G. e \<subseteq> W}"
    by (simp add: induced_subgraph.induced[OF H_induced_subgraph])+
  hence
    "vertices H = vertices F \<inter> V \<inter> W"
    "edges H = {e \<in> {e \<in> edges F. e \<subseteq> V}. e \<subseteq> W}"
    by (simp add: induced_subgraph.induced[OF G_induced_subgraph])+
  hence
    "vertices H = vertices F \<inter> (V \<inter> W)"
    "edges H = {e \<in> edges F. e \<subseteq> (V \<inter> W)}"
    by blast+
  thus "induced_subgraph_axioms F H (V \<inter> W)"
    by (intro induced_subgraph_axioms.intro) simp
qed

section \<open>Neighborhood\<close>

definition neighborhood :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "neighborhood G v \<equiv> {u \<in> vertices G. {v, u} \<in> edges G}"

lemma (in graph) in_neighborhood_iff:
  shows "u \<in> neighborhood G v \<longleftrightarrow> {v, u} \<in> edges G"
  using edge_subset_vertices
  by (auto simp add: neighborhood_def)

lemma (in graph) neighborhood_symmetric:
  shows "u \<in> neighborhood G v \<longleftrightarrow> v \<in> neighborhood G u"
  by (simp add: in_neighborhood_iff insert_commute)

lemma neighborhood_subset_vertices:
  shows "neighborhood G v \<subseteq> vertices G"
  by (simp add: neighborhood_def)

lemma in_neighborhood_implies_in_vertices:
  assumes "u \<in> neighborhood G v"
  shows "u \<in> vertices G"
  using assms neighborhood_subset_vertices
  by fastforce

lemma (in finite_graph) neighborhood_finite:
  shows "finite (neighborhood G v)"
  using neighborhood_subset_vertices vertices_finite
  by (rule finite_subset)

section \<open>Degree\<close>

abbreviation degree :: "'a graph \<Rightarrow> 'a \<Rightarrow> nat" where
  "degree G v \<equiv> card (neighborhood G v)"

lemma (in finite_graph) degree_0_conv:
  shows "degree G v = 0 \<longleftrightarrow> (\<nexists>e. e \<in> edges G \<and> v \<in> e)"
proof -
  have "finite (neighborhood G v)"
    using neighborhood_finite
    .
  hence "card (neighborhood G v) = 0 \<longleftrightarrow> neighborhood G v = {}"
    by (rule card_0_eq)
  also have "... \<longleftrightarrow> (\<nexists>u. {v, u} \<in> edges G)"
    by (auto simp add: in_neighborhood_iff)
  finally show ?thesis
    using graph
    by (auto simp add: insert_commute)
qed

end