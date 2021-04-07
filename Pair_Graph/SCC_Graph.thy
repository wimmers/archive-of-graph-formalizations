theory SCC_Graph
  imports
    Component_Defs
    AGF.Pair_Graph_Library_Component_Adaptor
    AGF.More_Graph_Theory
    AGF.TA_Graph_Library_Adaptor
begin

section\<open>SCC graph and DAGs\<close>
definition scc_graph :: "'a dgraph \<Rightarrow> ('a set) dgraph" where
  "scc_graph G \<equiv> {(x,y). \<exists>a \<in> x. \<exists>b \<in> y. x \<noteq> y \<and> x \<in> sccs_dVs G \<and> y \<in> sccs_dVs G \<and> (a,b) \<in> G}"

lemma dVs_scc_graph_subset_sccs_verts:
  "S \<in> dVs (scc_graph G) \<Longrightarrow> S \<in> sccs_dVs G"
  unfolding scc_graph_def dVs_def
  by auto

lemma (in pre_digraph) scc_graph_verts: "verts scc_graph = sccs_verts"
  unfolding scc_graph_def by simp

lemma (in wf_digraph) wf_digraph_scc_graph: "wf_digraph scc_graph"
  by (simp add: dag.axioms(1) scc_digraphI)
text \<open>
  The SCC graph represented as a set of pairs in general is just a subgraph of the
  SCC graph in \<^theory>\<open>Graph_Theory.Digraph\<close>:

  When the graph is strongly connected, then in the set of pairs
  representation the SCC graph is the empty set, while in \<^theory>\<open>Graph_Theory.Digraph\<close> it is a graph with 
  a single vertex (i.e.\ the set of all vertices) and no edges.

  Additionally, when there is an SCC with no outgoing edges, it cannot be captured by the
  set of pairs representation, while that is no problem in \<^theory>\<open>Graph_Theory.Digraph\<close> (or any graph
  representation with an explicit vertex set).
\<close>
lemma scc_graph_subset: "subgraph_digraph (ddfs.digraph_of (scc_graph G)) (pre_digraph.scc_graph (ddfs.digraph_of G))"
  by (auto intro!: Digraph_Component.subgraphI dest!: dVs_scc_graph_subset_sccs_verts 
      simp: sccs_dVs_eq pre_digraph.scc_graph_verts compatible_def wf_digraph.wf_digraph_scc_graph)
     (auto simp: scc_graph_def pre_digraph.scc_graph_def sccs_dVs_eq)


locale ddfs_dag = ddfs +
  assumes acyclic: "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> u \<Longrightarrow> False"
begin

interpretation dag_digraph_of: dag digraph_of
  by standard
     (auto dest: acyclic simp: dVsI)

lemma topological_numbering:
  assumes "finite S"
  shows "\<exists>f :: _ \<Rightarrow> nat. inj_on f S \<and> (\<forall>x\<in>S. \<forall>y\<in>S. (x,y) \<in> E \<longrightarrow> f x < f y)"
  using assms dag_digraph_of.topological_numbering by auto

end

lemma ddfs_dagI_digraph_of:
  notes ddfs_library_adaptor_simps[simp del]
  assumes "\<And>u. u \<rightarrow>\<^sup>+\<^bsub>ddfs.digraph_of E\<^esub> u \<Longrightarrow> False"
  shows "ddfs_dag E"
  using assms 
  by unfold_locales
     (auto simp flip: ddfs.reachable1_iff)

text \<open>How to pose this as interpretation/sublocale without breaking?\<close>
(* interpretation ddfs_scc_graph_dag: ddfs_dag "scc_graph E" *)
lemma ddfs_scc_graph_dag: "ddfs_dag (scc_graph E)"
  by (intro ddfs_dagI_digraph_of)
     (meson arcs_ends_mono dag.acyclic ddfs.wf_digraph_digraph_of scc_graph_subset trancl_mono wf_digraph.scc_digraphI)

declare ddfs_library_adaptor_simps[simp del]
end