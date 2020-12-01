theory DDFS_Library_Component_Adaptor
  imports
    DDFS_Library_Adaptor
    Graph_Theory.Digraph_Component
    "../Graph_Theory/More_Graph_Theory"
    "../TA_Graphs/TA_Graph_Library_Adaptor"
begin

lemma compatible_digraph_of[simp]:
  "compatible (ddfs.digraph_of G) (ddfs.digraph_of H)"
  by (simp add: compatible_def)

lemma compatible_digraph_of_compatible_digraph_of_arcs:
  "compatible H (ddfs.digraph_of G) \<Longrightarrow> compatible H (ddfs.digraph_of (arcs H))"
  unfolding compatible_def
  by auto

lemma compatible_sym: "compatible H G \<Longrightarrow> compatible G H"
  unfolding compatible_def
  by simp

lemma subgraph_digraph_of_dVs_arcs_subset:
  assumes "subgraph H (ddfs.digraph_of G)"
  shows "dVs (arcs H) \<subseteq> verts H"
  using assms
  unfolding subgraph_def dVs_def compatible_def
  by (auto dest: wf_digraph.wellformed)

lemma subgraph_digraph_of_dVs_arcs_subset':
  "subgraph H (ddfs.digraph_of G) \<Longrightarrow> x \<in> dVs (arcs H) \<Longrightarrow> x \<in> verts H"
  using subgraph_digraph_of_dVs_arcs_subset by blast

abbreviation "subgraph_ddfs \<equiv> Noschinski_to_DDFS.subgraph"

definition induce_subgraph :: "'a dgraph \<Rightarrow> 'a set \<Rightarrow> 'a dgraph" (infix "\<restriction>" 67) where
  "G \<restriction> vs \<equiv> {(u,v) \<in> G. u \<in> vs \<and> v \<in> vs}"

definition induced_subgraph :: "'a dgraph \<Rightarrow> 'a dgraph \<Rightarrow> bool" where
  "induced_subgraph H G \<equiv> H = G \<restriction> dVs H"

definition spanning :: "'a dgraph \<Rightarrow> 'a dgraph \<Rightarrow> bool" where
  "spanning H G \<equiv> subgraph_ddfs H G \<and> dVs G = dVs H"

definition strongly_connected :: "'a dgraph \<Rightarrow> bool" where
  "strongly_connected G \<equiv> G \<noteq> {} \<and> (\<forall>u \<in> dVs G. \<forall>v \<in> dVs G. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v)"

definition mk_symmetric :: "'a dgraph \<Rightarrow> 'a dgraph" where
  "mk_symmetric G \<equiv> G \<union> {(v,u). (u,v) \<in> G}"

definition connected :: "'a dgraph \<Rightarrow> bool" where
  "connected G \<equiv> strongly_connected (mk_symmetric G)"

definition max_subgraph :: "'a dgraph \<Rightarrow> ('a dgraph \<Rightarrow> bool) \<Rightarrow> 'a dgraph \<Rightarrow> bool" where
  "max_subgraph G P H \<equiv> subgraph_ddfs H G \<and> P H \<and> 
    (\<forall>H'. H' \<noteq> H \<and> subgraph_ddfs H H' \<longrightarrow> \<not>(subgraph_ddfs H' G \<and> P H'))"

definition sccs :: "'a dgraph \<Rightarrow> 'a dgraph set" where
  "sccs G \<equiv> {H. induced_subgraph H G \<and> strongly_connected H \<and> \<not>(\<exists>H'. induced_subgraph H' G
      \<and> strongly_connected H' \<and> dVs H \<subset> dVs H')}"

definition sccs_verts :: "'a dgraph \<Rightarrow> 'a set set" where
  "sccs_verts G \<equiv> {S. S \<noteq> {} \<and> (\<forall>u \<in> S. \<forall>v \<in> S. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v) \<and> (\<forall>u \<in> S. \<forall>v. v \<notin> S \<longrightarrow> \<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)}"

definition scc_of :: "'a dgraph \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "scc_of G u \<equiv> {v. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<and> v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u}"

abbreviation "induced_subgraph_digraph \<equiv> Digraph_Component.induced_subgraph"
abbreviation "spanning_digraph \<equiv> Digraph_Component.spanning"
abbreviation "strongly_connected_digraph \<equiv> Digraph_Component.strongly_connected"
abbreviation "mk_symmetric_digraph \<equiv> Digraph_Component.mk_symmetric"
abbreviation "connected_digraph \<equiv> Digraph_Component.connected"


lemma subgraph_iff:
  "subgraph_ddfs H G \<longleftrightarrow> subgraph (ddfs.digraph_of H) (ddfs.digraph_of G)"
  by (auto simp: subgraph_def)

lemma subgraph_digraph_ofE[elim]:
  assumes "subgraph H (ddfs.digraph_of G)"
  obtains H' where "H' = arcs H" "subgraph_ddfs H' G"
  using assms subgraph_iff
  by fastforce

lemma subgraph_digraph_ofD:
  assumes "subgraph H (ddfs.digraph_of G)"
  shows "subgraph (ddfs.digraph_of (arcs H)) (ddfs.digraph_of G)"
  using assms by (auto simp: subgraph_iff)

lemma subgraph_digraph_of_arcs:
  "subgraph H (ddfs.digraph_of G) \<Longrightarrow> subgraph (ddfs.digraph_of (arcs H)) H"
  by (auto intro!: subgraphI compatible_digraph_of_compatible_digraph_of_arcs 
      simp: subgraph_digraph_of_dVs_arcs_subset' 
      dest: compatible_digraph_of_compatible_digraph_of_arcs compatible_sym)
  

lemma subgraph_induce_subgraph:
  "subgraph_ddfs (G \<restriction> vs) G"
  by (auto simp: induce_subgraph_def)

lemma subgraph_induce_subgraph':
  "H = (G \<restriction> vs) \<Longrightarrow> subgraph_ddfs H G"
  by (simp add: subgraph_induce_subgraph)

lemma subgraph_induced_subgraph:
  "induced_subgraph H G \<Longrightarrow> subgraph_ddfs H G"
  unfolding induced_subgraph_def
  by (simp add: subgraph_induce_subgraph')

lemma induced_imp_induced:
  "induced_subgraph H G \<Longrightarrow> induced_subgraph_digraph (ddfs.digraph_of H) (ddfs.digraph_of G)"
  unfolding Digraph_Component.induced_subgraph_def
  by (auto simp flip: subgraph_iff dest: subgraph_induced_subgraph simp: adj_in_dVs)
     (auto simp add: induced_subgraph_def induce_subgraph_def)

lemma induced_subgraph_sets_conv: 
  "{e \<in> G. fst e \<in> dVs H \<and> snd e \<in> dVs H} = {(u,v). (u,v) \<in> G \<and> u \<in> dVs H \<and> v \<in> dVs H}"
  by auto

lemma dVs_union_distr: "dVs (G \<union> H) = dVs G \<union> dVs H"
  unfolding dVs_def by blast

lemma dVs_sym: "dVs {(v,u). (u,v) \<in> G} = dVs G"
  unfolding dVs_def by blast

lemma dVs_mk_symmetric: "dVs (mk_symmetric G) = dVs G"
  unfolding mk_symmetric_def by (simp add: dVs_union_distr dVs_sym)

lemma mk_symmetric_conv: "mk_symmetric G = (\<Union>x\<in>G. {x, (snd x, fst x)})"
  by (auto simp: mk_symmetric_def)

lemma induced_imp_induced':
  "induced_subgraph_digraph (ddfs.digraph_of H) (ddfs.digraph_of G) \<Longrightarrow> induced_subgraph H G"
  unfolding induced_subgraph_def Digraph_Component.induced_subgraph_def induce_subgraph_def
  by (simp add: induced_subgraph_sets_conv)

lemma induced_subgraph_iff:
  "induced_subgraph H G \<longleftrightarrow> induced_subgraph_digraph (ddfs.digraph_of H) (ddfs.digraph_of G)"
  using induced_imp_induced induced_imp_induced' by blast

lemma induced_subgraph_digraph_of_arcs:
  assumes "induced_subgraph_digraph H (ddfs.digraph_of G)"
  shows "induced_subgraph (arcs H) G"
  using assms
  by (auto simp: induced_subgraph_iff induced_imp_subgraph subgraph_digraph_ofD dVsI
      intro!: induced_subgraphI)
     (auto simp: Digraph_Component.induced_subgraph_def dest: subgraph_digraph_of_dVs_arcs_subset')

lemma induced_subgraph_digraph_ofE:
  assumes "induced_subgraph_digraph H (ddfs.digraph_of G)"
  obtains H' where "H' = arcs H" "induced_subgraph H' G"
  using assms induced_subgraph_digraph_of_arcs by auto

lemma spanning_iff:
  "spanning H G \<longleftrightarrow> spanning_digraph (ddfs.digraph_of H) (ddfs.digraph_of G)"
  unfolding spanning_def Digraph_Component.spanning_def
  by (auto simp: subgraph_iff)

lemma strongly_connected_iff:
  "strongly_connected G \<longleftrightarrow> strongly_connected_digraph (ddfs.digraph_of G)"
  unfolding strongly_connected_def Digraph_Component.strongly_connected_def
  by (auto simp: ddfs.reachable_iff dest: adj_in_dVs)

lemma mk_symmetric_eq: "ddfs.digraph_of (mk_symmetric G) \<equiv> mk_symmetric_digraph (ddfs.digraph_of G)"
  unfolding Digraph_Component.mk_symmetric_def with_proj_def
  by (auto simp: ddfs.digraph_of_def dVs_mk_symmetric)
     (simp add: mk_symmetric_conv)

lemma connected_iff: "connected G \<longleftrightarrow> connected_digraph (ddfs.digraph_of G)"
  unfolding connected_def Digraph_Component.connected_def
  by (auto simp: strongly_connected_iff mk_symmetric_eq)

lemma max_subgraph_iff:
  "max_subgraph G P H \<longleftrightarrow> pre_digraph.max_subgraph (ddfs.digraph_of G) (P \<circ> arcs) (ddfs.digraph_of H)"
  unfolding max_subgraph_def pre_digraph.max_subgraph_def
  apply (intro iffI)
  subgoal
    apply (auto simp: subgraph_iff)
    sorry
  subgoal
    apply (auto simp: subgraph_iff subgraph_def subsetD)
    by (metis compatible_digraph_of ddfs.arcs_eq ddfs.verts_eq ddfs.wf_digraph_digraph_of)
  oops

lemma
  "c \<in> sccs G \<Longrightarrow> (ddfs.digraph_of c) \<in> pre_digraph.sccs (ddfs.digraph_of G)"
  unfolding sccs_def pre_digraph.sccs_def
  apply (auto simp: induced_subgraph_iff strongly_connected_iff)
  oops

lemma
  "(ddfs.digraph_of c) \<in> pre_digraph.sccs (ddfs.digraph_of G) \<Longrightarrow> c \<in> sccs G"
  unfolding sccs_def pre_digraph.sccs_def
  apply (simp add: induced_subgraph_iff strongly_connected_iff)
  by (metis ddfs.verts_eq)

lemma sccs_verts_eq: "sccs_verts G = pre_digraph.sccs_verts (ddfs.digraph_of G)"
  by (auto simp: sccs_verts_def pre_digraph.sccs_verts_def ddfs.reachable_iff)

lemma scc_of_eq: "scc_of G u = pre_digraph.scc_of (ddfs.digraph_of G) u"
  by (auto simp: scc_of_def pre_digraph.scc_of_def ddfs.reachable_iff)

definition scc_graph :: "'a dgraph \<Rightarrow> ('a set) dgraph" where
  "scc_graph G \<equiv> {(x,y). \<exists>a \<in> x. \<exists>b \<in> y. x \<noteq> y \<and> x \<in> sccs_verts G \<and> y \<in> sccs_verts G \<and> (a,b) \<in> G}"

lemma dVs_scc_graph_subset_sccs_verts:
  "S \<in> dVs (scc_graph G) \<Longrightarrow> S \<in> sccs_verts G"
  unfolding scc_graph_def dVs_def
  by auto

lemma (in pre_digraph) scc_graph_verts: "verts scc_graph = sccs_verts"
  unfolding scc_graph_def by simp

lemma (in wf_digraph) wf_digraph_scc_graph: "wf_digraph scc_graph"
  by (simp add: dag.axioms(1) scc_digraphI)
text \<open>
  The SCC graph represented as a set of pairs in general is just a subgraph of the
  SCC graph in Graph_Theory:

  When the graph is strongly connected, then in the set of pairs
  representation the SCC graph is the empty set, while in Graph_Theory it is a graph with 
  a single vertex (i.e.\ the set of all vertices) and no edges.

  Additionally, when there is an SCC with no outgoing edges, it cannot be captured by the
  set of pairs representation, while that is no problem in Graph_Theory (or any graph
  representation with an explicit vertex set).
\<close>
lemma scc_graph_subset: "subgraph (ddfs.digraph_of (scc_graph G)) (pre_digraph.scc_graph (ddfs.digraph_of G))"
  by (auto intro!: subgraphI dest!: dVs_scc_graph_subset_sccs_verts 
      simp: sccs_verts_eq pre_digraph.scc_graph_verts compatible_def wf_digraph.wf_digraph_scc_graph)
     (auto simp: scc_graph_def pre_digraph.scc_graph_def sccs_verts_eq)


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
  apply standard
  using assms by (auto simp: ddfs.reachable1_iff assms)

interpretation ddfs_scc_graph_dag: ddfs_dag "scc_graph E"
  by (intro ddfs_dagI_digraph_of)
     (meson arcs_ends_mono dag.acyclic ddfs.wf_digraph_digraph_of scc_graph_subset trancl_mono wf_digraph.scc_digraphI)
end
