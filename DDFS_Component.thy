theory DDFS_Component
  imports
    DDFS_Component_Defs
    Adaptors.DDFS_Library_Component_Adaptor
begin

subsection \<open>Basic lemmas\<close>
lemma subgraph_imp_subverts:
  assumes "subgraph H G"
  shows "dVs H \<subseteq> dVs G"
  using assms
  by (auto simp add: subgraph_iff dest!: Digraph_Component.subgraph_imp_subverts)

lemma induced_subgraph_refl: "induced_subgraph G G"
  by (simp add: induced_subgraph_iff wf_digraph.induced_subgraph_refl)

subsection \<open>The underlying symmetric graph of a digraph\<close>
lemma reachable_mk_symmetricI:
  fixes G :: "'a dgraph"
  assumes "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" shows "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> v"
  using assms
  by (auto simp flip: ddfs.reachable_iff simp: mk_symmetric_eq intro: wf_digraph.reachable_mk_symmetricI)

lemma reachable_mk_symmetric_eq:
  assumes "sym G"
  shows "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using assms
  by (auto simp flip: ddfs.reachable_iff ddfs.symmetric_iff simp: mk_symmetric_eq 
      intro!: wf_digraph.reachable_mk_symmetric_eq)

lemma mk_symmetric_awalk_imp_awalk:
  assumes "sym G"
  assumes "awalk (mk_symmetric G) u p v"
  obtains q where "awalk G u q v"
  using assms
  by (auto simp flip: ddfs.symmetric_iff simp: ddfs.awalk_iff_awalk mk_symmetric_eq)
     (meson ddfs.wf_digraph_digraph_of wf_digraph.mk_symmetric_awalk_imp_awalk)

subsection \<open>Subgraphs and Induced Subgraphs\<close>
lemma subgraph_trans:
  assumes "subgraph G H" "subgraph H I" shows "subgraph G I"
  using assms
  by (auto simp: subgraph_iff intro: subgraph_trans)

lemma adj_mono:
  fixes H G :: "'a dgraph"
  assumes "u \<rightarrow>\<^bsub>H\<^esub> v" "subgraph H G"
  shows "u \<rightarrow>\<^bsub>G\<^esub> v"
  using assms
  by auto

lemma reachable_mono:
  fixes H G :: "'a dgraph"
  assumes "u \<rightarrow>\<^sup>*\<^bsub>H\<^esub> v" "subgraph H G"
  shows "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using assms
  by (auto simp flip: ddfs.reachable_iff simp: subgraph_iff intro: pre_digraph.reachable_mono)

lemma subgraph_awalk_imp_awalk:
  assumes "awalk H u p v"
  assumes "subgraph H G"
  shows "awalk G u p v"
  using assms
  by (auto simp: ddfs.awalk_iff_awalk subgraph_iff intro: wf_digraph.subgraph_awalk_imp_awalk)

lemma subgraph_apath_imp_apath:
  assumes "apath H u p v"
  assumes "subgraph H G"
  shows "apath G u p v"
  using assms
  by (simp add: ddfs.apath_iff_apath subgraph_iff wf_digraph.subgraph_apath_imp_apath)

lemma subgraph_mk_symmetric:
  assumes "subgraph H G"
  shows "subgraph (mk_symmetric H) (mk_symmetric G)"
  using assms
  by (simp add: subgraph_iff Digraph_Component.subgraph_mk_symmetric mk_symmetric_eq)

subsection \<open>Induced subgraphs\<close>
lemma digraph_of_induce_arcs: "arcs (ddfs.digraph_of (G \<restriction> vs)) = arcs (ddfs.digraph_of G) \<restriction> vs"
  unfolding induce_subgraph_def Digraph_Component.induce_subgraph_def
  by auto

lemma digraph_of_induce_verts:
  "verts (ddfs.digraph_of (G \<restriction> vs)) = verts ((ddfs.digraph_of G) \<restriction> vs) \<inter> dVs (G \<restriction> vs)"
  oops

lemma "ddfs.digraph_of (G \<restriction> vs) = (ddfs.digraph_of G) \<restriction> vs"
  oops

lemma induce_dVs_subset:
  "u \<in> dVs (G \<restriction> S) \<Longrightarrow> u \<in> S"
  unfolding induce_subgraph_def dVs_def by blast

lemma in_induce_subgraph_dVsI:
  assumes "u \<in> vs"
    and  "\<exists>v \<in> vs. (u, v) \<in> G \<or> (v, u) \<in> G"
  shows "u \<in> dVs (G \<restriction> vs)"
  using assms
  unfolding induce_subgraph_def
  by (auto intro: dVsI)

lemma in_induce_subgraph_dVsI_reachable:
  fixes G :: "'a dgraph"
  assumes "u \<in> S"
    and "v \<in> S"
    and "S \<in> sccs_dVs G"
    and "S \<noteq> {u}"
    and "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  shows "u \<in> dVs (G \<restriction> S)" "v \<in> dVs (G \<restriction> S)"
  using assms
  by (auto intro!: in_induce_subgraph_dVsI simp: sccs_dVs_def)
     (metis (no_types, lifting) converse_tranclE reachable1_reachable reachable_neq_reachable1 trancl.intros(1) trancl_trans)+

lemma induce_sccs_dVs:
  assumes "S \<in> sccs_dVs G"
  assumes "u \<in> S" "S \<noteq> {u}"
  shows "dVs (G \<restriction> S) = S"
proof
  show "dVs (G \<restriction> S) \<subseteq> S" by (auto dest: induce_dVs_subset)
  show "S \<subseteq> dVs (G \<restriction> S)"
    by (meson assms in_induce_subgraph_dVsI_reachable in_sccs_dVsD subset_eq)
qed

lemma induce_sccs_dVs_digraph_of_eq:
  assumes "S \<in> sccs_dVs G"
  assumes "u \<in> S" "S \<noteq> {u}"
  shows "ddfs.digraph_of (G \<restriction> S) = ddfs.digraph_of G \<restriction> S"
  using assms
  by (metis (no_types, lifting) induced_subgraphI ddfs.verts_eq ddfs.wf_digraph_digraph_of in_induce_subgraphI induce_sccs_dVs induced_subgraph_iff subgraph_induce_subgraph wf_digraph.induce_eq_iff_induced)

lemma induced_induce:
  shows "induced_subgraph (G \<restriction> vs) G"
  by (auto simp: induced_subgraph_def dVs_def induce_subgraph_def)

lemma induced_graph_imp_symmetric:
  assumes "sym G"
  assumes "induced_subgraph H G"
  shows "sym H"
  using assms
  by (simp flip: ddfs.symmetric_iff add: induced_subgraph_iff induced_graph_imp_symmetric)

lemma induce_reachable_preserves_paths:
  fixes G :: "'a dgraph"
  assumes "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  assumes "u \<noteq> v"
  shows "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> {w. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w}\<^esub> v"
  using assms
proof induct
  case base
  then show ?case by blast
next
  case (step x y)
  then show ?case
    apply (auto simp flip: ddfs.reachable_iff)
    sorry
qed

lemma induced_subgraphI':
  assumes "subgraph_ddfs H G"
  assumes "\<And>H'. subgraph_ddfs H' G \<Longrightarrow> (dVs H' \<noteq> dVs H \<or> subgraph_ddfs H' H)"
  shows "induced_subgraph H G"
  using assms
  apply (auto simp: subgraph_iff induced_subgraph_iff intro!: induced_subgraphI')
  oops

subsection \<open>Maximal Subgraphs\<close>

lemma max_subgraph_mp:
  assumes "max_subgraph G Q x" "\<And>x. P x \<Longrightarrow> Q x" "P x" shows "max_subgraph G P x"
  using assms
  by (auto simp: max_subgraph_def)

lemma max_subgraph_prop: "max_subgraph G P x \<Longrightarrow> P x"
  by (auto dest: max_subgraphD)

lemma max_subgraph_subg_eq:
  assumes "max_subgraph G P H1" "max_subgraph G P H2" "subgraph H1 H2"
  shows "H1 = H2"
  using assms
  by (auto elim: max_subgraphE)

definition arc_mono :: "('a dgraph \<Rightarrow> bool) \<Rightarrow> bool" where
  "arc_mono P \<equiv> (\<forall>H1 H2. P H1 \<and> subgraph H1 H2 \<and> dVs H1 = dVs H2 \<longrightarrow> P H2)"

abbreviation "arc_mono_digraph \<equiv> Digraph_Component.arc_mono"

lemma arc_mono_iff:
  "arc_mono P \<longleftrightarrow> arc_mono_digraph (P \<circ> arcs)"
  oops

subsection \<open>Connected and Strongly Connected Graphs\<close>
lemma sccs_dVs_disjoint:
  assumes "S \<in> sccs_dVs G" "T \<in> sccs_dVs G" "S \<noteq> T" shows "S \<inter> T = {}"
  using assms ddfs.wf_digraph_digraph_of sccs_dVs_eq wf_digraph.sccs_verts_disjoint
  by blast

lemma strongly_connected_spanning_imp_strongly_connected:
  assumes "spanning H G"
  assumes "strongly_connected H"
  shows "strongly_connected G"
  using assms
  by (simp add: spanning_iff strongly_connected_iff wf_digraph.strongly_connected_spanning_imp_strongly_connected)

lemma strongly_connected_imp_induce_subgraph_strongly_connected:
  assumes "subgraph H G"
  assumes "strongly_connected H"
  shows "strongly_connected (G \<restriction> (dVs H))"
  oops

lemma in_sccs_dVsI_sccs:
  assumes "S \<in> dVs ` sccs G" shows "S \<in> sccs_dVs G"
  using assms
  by (force simp: sccs_dVs_eq in_sccs_iff wf_digraph.sccs_verts_conv image_iff)

lemma sccs_altdef:
  "sccs G = {H. max_subgraph G strongly_connected H}"
  apply (auto simp: in_sccs_iff pre_digraph.sccs_altdef2 strongly_connected_iff max_subgraph_def)
     apply (simp add: pre_digraph.subgraphI_max_subgraph subgraph_iff)
    apply (simp add: pre_digraph.max_subgraph_def)
   apply (metis ddfs.arcs_ends_eq pre_digraph.max_subgraph_def subgraph_iff)
  unfolding pre_digraph.max_subgraph_def
  apply (auto simp: subgraph_iff)
  oops

lemma in_sccs_dVsD_sccs:
  assumes "S \<in> sccs_dVs G"
  assumes "u \<in> S" "S \<noteq> {u}"
  shows "G \<restriction> S \<in> sccs G"
  using assms wf_digraph.in_verts_sccsD_sccs ddfs.wf_digraph_digraph_of
  unfolding in_sccs_iff sccs_dVs_eq induce_sccs_dVs_digraph_of_eq[OF assms]
  by blast

lemma in_sccs_subset_imp_eq:
  assumes "c \<in> sccs G"
  assumes "d \<in> sccs G"
  assumes "dVs c \<subseteq> dVs d"
  shows "c = d"
  using assms
  by (simp add: in_sccs_iff pre_digraph.in_sccs_subset_imp_eq flip: ddfs.verts_eq eq_iff_digraph_of_eq)

lemma inj_on_dVs_sccs: "inj_on dVs (sccs G)"
  by (rule inj_onI)
     (simp add: in_sccs_subset_imp_eq)

lemma scc_disj:
  assumes "c \<in> sccs G" "d \<in> sccs G"
  assumes "c \<noteq> d"
  shows "dVs c \<inter> dVs d = {}"
  using assms wf_digraph.scc_disj
  by (force simp add: in_sccs_iff simp flip: ddfs.verts_eq eq_iff_digraph_of_eq)

lemma in_scc_of_self: "u \<in> dVs G \<Longrightarrow> u \<in> scc_of G u"
  by (simp add: scc_of_eq' wf_digraph.in_scc_of_self flip: ddfs.verts_eq)

lemma scc_of_empty_conv: "scc_of G u = {} \<longleftrightarrow> u \<notin> dVs G"
  by (simp add: scc_of_eq' wf_digraph.scc_of_empty_conv flip: ddfs.verts_eq)

lemma scc_of_in_sccs_dVs:
  "u \<in> dVs G \<Longrightarrow> scc_of G u \<in> sccs_dVs G"
  by (simp add: scc_of_eq' sccs_dVs_eq wf_digraph.scc_of_in_sccs_verts flip: ddfs.verts_eq)

lemma sccs_dVs_subsets: "S \<in> sccs_dVs G \<Longrightarrow> S \<subseteq> dVs G"
  by (simp add: sccs_dVs_eq wf_digraph.sccs_verts_subsets flip: ddfs.verts_eq)

lemma scc_of_eq: "u \<in> scc_of G v \<Longrightarrow> scc_of G u = scc_of G v"
  by (simp add: scc_of_eq' wf_digraph.scc_of_eq)

lemma strongly_connected_eq_iff:
  "strongly_connected G \<longleftrightarrow> sccs G = {G}"
  apply (auto simp add: strongly_connected_iff in_sccs_iff wf_digraph.strongly_connected_eq_iff)
    apply (metis ddfs.arcs_ends_eq)+
  by (metis Digraph_Component.subgraph_def ddfs.digraph_of_pair_conv empty_iff in_sccsE insert_iff pre_digraph.in_sccsE pre_digraph.induced_subgraph_altdef strongly_connected_iff wf_digraph.strongly_connected_eq_iff)


lemma union_sccs_subset: "\<Union>(sccs G) \<subseteq> G"
  by  (auto elim!: in_sccsE induced_subgraphE)

lemma union_sccs_dVs_subset: "dVs (\<Union>(sccs G)) \<subseteq> dVs G"
  by (simp add: dVs_subset union_sccs_subset)


lemma not_in_dVs_sccs_not_reachable_and_reach:
  fixes G :: "'a dgraph"
  assumes "u \<notin> dVs (\<Union>(sccs G))"
  shows "\<nexists>v. u \<noteq> v \<and> (v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u) \<and> (u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v)"
proof (cases "u \<in> dVs G")
  case True
  { fix v assume "u \<noteq> v" and reach_vu: "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u" and reach_uv:"u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
    then have "v \<in> dVs G" by (auto dest: reachable_in_dVs)

    then have "u \<in> scc_of G v" "v \<in> scc_of G v" 
      using reach_vu reach_uv by (auto simp: in_scc_of_self)

    then have "scc_of G v \<in> sccs_dVs G" "scc_of G v \<noteq> {u}"
      using \<open>u \<noteq> v\<close>
      by (auto simp add:  \<open>v \<in> dVs G\<close> scc_of_in_sccs_dVs)
  
    have "G \<restriction> scc_of G v \<in> sccs G"
      using \<open>u \<in> scc_of G v\<close> \<open>u \<noteq> v\<close> \<open>v \<in> dVs G\<close> in_sccs_dVsD_sccs scc_of_in_sccs_dVs by fastforce

    then have False
      by (smt Sup_upper \<open>scc_of G v \<in> sccs_dVs G\<close> \<open>u \<in> scc_of G v\<close> \<open>u \<noteq> v\<close> \<open>v \<in> scc_of G v\<close> assms dVs_subset empty_iff induce_sccs_dVs insert_Diff insert_iff insert_subset)
  }
  then show ?thesis
    by blast
next
  case False
  then show ?thesis
    by (auto dest: reachable_in_dVs)
qed

lemma
  fixes G :: "'a dgraph"
  assumes "u \<in> dVs G"
  assumes "u \<notin> dVs (\<Union>(sccs G))"
  assumes "connected G" "sccs G \<noteq> {}"
  obtains v C c where 
    "C \<in> sccs G"
    "c \<in> dVs C"
    "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
    "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> c \<or> c \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  oops \<comment> \<open>u --> v <-- w --> C\<close>

lemma not_in_dVs_sccs_singleton_scc:
  fixes G :: "'a dgraph"
  assumes "u \<in> dVs G"
  assumes "u \<notin> dVs (\<Union>(sccs G))"
  shows "scc_of G u = {u}"
  using assms in_scc_ofD not_in_dVs_sccs_not_reachable_and_reach
  by fastforce

declare ddfs_library_adaptor_simps[simp del]

end