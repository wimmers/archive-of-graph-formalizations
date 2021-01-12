theory DDFS_Library_Component_Adaptor
  imports
    DDFS_Library_Adaptor
    DDFS_Library_Awalk_Adaptor
    AGF.DDFS_Component_Defs
    Digraph_Component_More
begin

abbreviation "subgraph_digraph \<equiv> Digraph_Component.subgraph"
abbreviation "induced_subgraph_digraph \<equiv> Digraph_Component.induced_subgraph"
abbreviation "spanning_digraph \<equiv> Digraph_Component.spanning"
abbreviation "strongly_connected_digraph \<equiv> Digraph_Component.strongly_connected"
abbreviation "mk_symmetric_digraph \<equiv> Digraph_Component.mk_symmetric"
abbreviation "connected_digraph \<equiv> Digraph_Component.connected"

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

lemma compatible_digraph_of_arcs_ends:
  "compatible H (ddfs.digraph_of G) \<Longrightarrow> arcs_ends H = arcs H"
  by (auto simp: compatible_def arcs_ends_def arc_to_ends_def)

lemma subgraph_digraph_of_dVs_arcs_subset:
  assumes "subgraph_digraph H (ddfs.digraph_of G)"
  shows "dVs (arcs H) \<subseteq> verts H"
  using assms
  unfolding Digraph_Component.subgraph_def dVs_def compatible_def
  by (auto dest: wf_digraph.wellformed)

lemma subgraph_digraph_of_dVs_arcs_subset':
  "subgraph_digraph H (ddfs.digraph_of G) \<Longrightarrow> x \<in> dVs (arcs H) \<Longrightarrow> x \<in> verts H"
  using subgraph_digraph_of_dVs_arcs_subset by blast

definition digraph_of_all_verts where
  "digraph_of_all_verts H G \<equiv> pre_digraph.add_verts (ddfs.digraph_of H) (dVs G)"

lemma "dVs G \<subseteq> verts (digraph_of_all_verts H G)"
  by (auto simp: digraph_of_all_verts_def pre_digraph.add_verts_simps)

lemma subgraph_iff:
  "subgraph H G \<longleftrightarrow> subgraph_digraph (ddfs.digraph_of H) (ddfs.digraph_of G)"
  by (auto simp: Digraph_Component.subgraph_def)

lemma subgraph_digraph_ofE[elim]:
  assumes "subgraph_digraph H (ddfs.digraph_of G)"
  obtains H' where "H' = arcs H" "subgraph H' G"
  using assms
  by (simp add: DDFS_Component_Defs.subgraph_def Digraph_Component.subgraph_def)

lemma subgraph_digraph_ofD:
  assumes "subgraph_digraph H (ddfs.digraph_of G)"
  shows "subgraph_digraph (ddfs.digraph_of (arcs H)) (ddfs.digraph_of G)"
  using assms by (auto simp: subgraph_iff)

lemma subgraph_digraph_of_arcs:
  "subgraph_digraph H (ddfs.digraph_of G) \<Longrightarrow> subgraph_digraph (ddfs.digraph_of (arcs H)) H"
  by (auto intro!: Digraph_Component.subgraphI compatible_digraph_of_compatible_digraph_of_arcs 
      simp: subgraph_digraph_of_dVs_arcs_subset' 
      dest: compatible_digraph_of_compatible_digraph_of_arcs compatible_sym)

lemma induced_imp_induced:
  "induced_subgraph H G \<Longrightarrow> induced_subgraph_digraph (ddfs.digraph_of H) (ddfs.digraph_of G)"
  unfolding Digraph_Component.induced_subgraph_def
  by (auto dest: induced_subgraphD simp flip: subgraph_iff simp: dVsI)

lemma induced_imp_induced':
  "induced_subgraph_digraph (ddfs.digraph_of H) (ddfs.digraph_of G) \<Longrightarrow> induced_subgraph H G"
  by (auto intro!: induced_subgraphI elim!: Digraph_Component.induced_subgraphE simp: subgraph_iff)

lemma induced_subgraph_iff:
  "induced_subgraph H G \<longleftrightarrow> induced_subgraph_digraph (ddfs.digraph_of H) (ddfs.digraph_of G)"
  using induced_imp_induced induced_imp_induced' by blast

lemma induced_subgraph_digraph_of_arcs:
  assumes "induced_subgraph_digraph H (ddfs.digraph_of G)"
  shows "induced_subgraph (arcs H) G"
  using assms
  by (auto dest: subgraph_digraph_of_dVs_arcs_subset' intro!: subgraph_digraph_of_dVs_arcs_subset' 
      induced_subgraphI elim!: Digraph_Component.induced_subgraphE)

lemma induced_subgraph_digraph_ofE:
  assumes "induced_subgraph_digraph H (ddfs.digraph_of G)"
  obtains H' where "H' = arcs H" "induced_subgraph H' G"
  using assms induced_subgraph_digraph_of_arcs by auto

lemma spanning_iff:
  "spanning H G \<longleftrightarrow> spanning_digraph (ddfs.digraph_of H) (ddfs.digraph_of G)"
  by (auto elim!: spanningE simp: subgraph_iff Digraph_Component.spanning_def)

lemma strongly_connected_iff:
  "strongly_connected G \<longleftrightarrow> strongly_connected_digraph (ddfs.digraph_of G)"
  unfolding Digraph_Component.strongly_connected_def
  by (auto simp: ddfs.reachable_iff elim!: strongly_connectedE dest: dVsI)


lemma mk_symmetric_eq: "ddfs.digraph_of (mk_symmetric G) \<equiv> mk_symmetric_digraph (ddfs.digraph_of G)"
  unfolding Digraph_Component.mk_symmetric_def with_proj_def
  by (auto simp: ddfs.digraph_of_def dVs_mk_symmetric)
     (simp add: mk_symmetric_conv case_prod_beta)

lemma connected_iff: "connected G \<longleftrightarrow> connected_digraph (ddfs.digraph_of G)"
  by (auto elim: connectedE simp: Digraph_Component.connected_def strongly_connected_iff mk_symmetric_eq)

  
lemma max_subgraph_imp_max_subgraph:
  assumes "pre_digraph.max_subgraph (ddfs.digraph_of G) (P \<circ> arcs) (ddfs.digraph_of H)"
  shows "max_subgraph G P H"
  using assms
  unfolding max_subgraph_def pre_digraph.max_subgraph_def
  by (metis comp_apply ddfs.arcs_eq subgraph_iff)


lemma max_subgraph_imp_max_subgraph_all_verts:
  assumes "max_subgraph G P H"
  shows "pre_digraph.max_subgraph (ddfs.digraph_of G) (P \<circ> arcs) (digraph_of_all_verts H G)"
  using assms
  unfolding max_subgraph_def pre_digraph.max_subgraph_def digraph_of_all_verts_def
  apply (auto simp add: Digraph_Component.subgraph_def compatible_def pre_digraph.add_verts_simps subgraph_iff wf_digraph.wf_digraph_add_verts)
  by (smt Digraph_Component.subgraphE Digraph_Component.subgraphI compatible_def dVs_subset ddfs.arcs_eq ddfs.head_eq ddfs.tail_eq ddfs.verts_eq ddfs.wf_digraph_digraph_of le_sup_iff pre_digraph.arcs_add_verts pre_digraph.head_add_verts pre_digraph.induced_subgraph_altdef pre_digraph.tail_add_verts pre_digraph.verts_add_verts subset_antisym wf_digraph.induce_eq_iff_induced wf_digraph.induced_subgraph_refl wf_digraph.wf_digraph_add_verts)

lemma max_subgraph_arcs_eq:
  assumes "max_subgraph G P H"
  assumes "H \<subseteq> arcs H'"
  assumes max_digraph_of: "pre_digraph.max_subgraph (ddfs.digraph_of G) (P \<circ> arcs) H'"
  shows "arcs H' = H"
  using assms pre_digraph.subgraphI_max_subgraph[OF max_digraph_of] pre_digraph.max_subgraph_prop[OF max_digraph_of]
  by (auto dest: max_subgraphD)

lemma max_subgraph_arcs_eq':
  assumes "max_subgraph G P H"
  assumes "arcs H' \<subseteq> H"
  assumes "pre_digraph.max_subgraph (ddfs.digraph_of G) (P \<circ> arcs) H'"
  shows "arcs H' = H"
  using assms pre_digraph.subgraphI_max_subgraph[OF assms(3)] pre_digraph.max_subgraph_prop[OF assms(3)]
  by (metis (no_types, lifting) Digraph_Component.subgraphE Digraph_Component.subgraphI compatible_def ddfs.arcs_eq digraph_of_all_verts_def max_subgraph_P_arcs_verts max_subgraph_imp_max_subgraph_all_verts pre_digraph.arcs_add_verts pre_digraph.max_subgraph_subg_eq pre_digraph.subgraphI_max_subgraph)

lemma max_subgraph_digraph_of_additional_verts_disconnected:
  fixes H' :: "('a, 'a \<times> 'a) pre_digraph"
  assumes "max_subgraph G P H"
  assumes "pre_digraph.max_subgraph (ddfs.digraph_of G) (P \<circ> arcs) H'"
  assumes "u \<in> verts H'" "u \<notin> dVs H"
  assumes "H \<subseteq> arcs H'" \<comment> \<open>a max subgraph is not unique, therefore we have to enforce that we are talking about the "same" max subgraph in both worlds\<close>
  shows "\<nexists>v. (u \<rightarrow>\<^bsub>H'\<^esub> v \<or> v \<rightarrow>\<^bsub>H'\<^esub> u)"
  using assms
  by (auto dest!: max_subgraph_arcs_eq;
      metis Digraph_Component.subgraphE compatible_digraph_of_arcs_ends dVsI pre_digraph.subgraphI_max_subgraph subgraph_digraph_of_arcs)+


text \<open>
  The assumption in this lemma is pretty strong, however, it is necessary due to 
  @{thm max_subgraph_P_arcs_verts}.\<close>
lemma max_subgraph_iff:
  assumes "ddfs.digraph_of H = digraph_of_all_verts H G"
  shows "max_subgraph G P H \<longleftrightarrow> pre_digraph.max_subgraph (ddfs.digraph_of G) (P \<circ> arcs) (ddfs.digraph_of H)"
  using assms max_subgraph_imp_max_subgraph max_subgraph_imp_max_subgraph_all_verts
  by metis

lemma dVs_arcs_subset_verts: 
  "wf_digraph H \<Longrightarrow> compatible H (ddfs.digraph_of G)\<Longrightarrow> dVs (arcs H) \<subseteq> verts H"
  by (auto simp: dVs_def wf_digraph_def compatible_head compatible_tail)


lemma strongly_connected_induced_is_digraph_of_verts:
  assumes "strongly_connected_digraph H"
  assumes "induced_subgraph_digraph H (ddfs.digraph_of G)"
  assumes "u \<in> verts H" "verts H \<noteq> {u}"
  shows "verts H = dVs (arcs H)"
  using assms
  unfolding dVs_def
  apply (auto elim!: Digraph_Component.induced_subgraphE Digraph_Component.strongly_connectedE)
  by (metis (no_types, lifting) Digraph_Component.subgraph_def compatible_digraph_of_arcs_ends insertI1 mem_Collect_eq pre_digraph.converse_reachable_cases snd_conv subgraph_digraph_of_arcs)

lemma strongly_connected_induced_is_digraph_of:
  assumes "strongly_connected_digraph H"
  assumes "induced_subgraph_digraph H (ddfs.digraph_of G)"
  assumes "u \<in> verts H" "verts H \<noteq> {u}"
  shows "H = ddfs.digraph_of (arcs H)"
  using assms
  by (metis ddfs.verts_eq induced_eq_verts_imp_eq induced_subgraph_digraph_ofE induced_subgraph_iff strongly_connected_induced_is_digraph_of_verts)

lemma in_digraph_of_sccs_imp_in_sccs_image:
  assumes "c \<in> pre_digraph.sccs (ddfs.digraph_of G)"
  assumes "u \<in> verts c" "verts c \<noteq> {u}"
  shows "c \<in> ddfs.digraph_of ` sccs G"
  using assms
  by (auto elim!: pre_digraph.in_sccsE)
     (smt assms(3) ddfs.verts_eq image_iff in_sccsI induced_imp_induced induced_subgraph_dVs_subset_iff induced_subgraph_digraph_of_arcs strongly_connected_iff strongly_connected_induced_is_digraph_of)

lemma in_sccs_imp_in_sccs_digraph_of: 
  "c \<in> sccs G \<Longrightarrow> ddfs.digraph_of c \<in> pre_digraph.sccs (ddfs.digraph_of G)"
  by (smt Digraph_Component.strongly_connected_def ddfs.verts_eq in_sccsD induced_subgraph_dVs_subset_iff induced_imp_induced induced_subgraph_digraph_of_arcs pre_digraph.in_sccsI psubsetE strongly_connected_iff strongly_connected_induced_is_digraph_of subsetI subset_empty subset_insert)

lemma in_sccs_digraph_of_imp_in_sccs:
  "(ddfs.digraph_of c) \<in> pre_digraph.sccs (ddfs.digraph_of G) \<Longrightarrow> c \<in> sccs G"
  unfolding sccs_def pre_digraph.sccs_def
  by (simp add: induced_subgraph_iff strongly_connected_iff)
     (metis ddfs.verts_eq induced_imp_induced' induced_subgraph_dVs_subset_iff)

lemma in_sccs_iff:
  shows "c \<in> sccs G \<longleftrightarrow> ddfs.digraph_of c \<in> pre_digraph.sccs (ddfs.digraph_of G)"
  using in_sccs_digraph_of_imp_in_sccs in_sccs_imp_in_sccs_digraph_of by metis


lemma sccs_dVs_eq: "sccs_dVs G = pre_digraph.sccs_verts (ddfs.digraph_of G)"
  by (auto simp: sccs_dVs_def pre_digraph.sccs_verts_def ddfs.reachable_iff)

lemma scc_of_eq: "scc_of G u = pre_digraph.scc_of (ddfs.digraph_of G) u"
  by (auto simp: scc_of_def pre_digraph.scc_of_def ddfs.reachable_iff)

lemma union_eq: "ddfs.digraph_of (G \<union> H) = union (ddfs.digraph_of G) (ddfs.digraph_of H)"
  unfolding ddfs.digraph_of_def
  by (auto simp: dVs_union_distr)

end
