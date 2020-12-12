theory DDFS_Library_Component_Adaptor
  imports
    DDFS_Library_Adaptor
    Digraph_Component_More
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

lemma compatible_digraph_of_arcs_ends:
  "compatible H (ddfs.digraph_of G) \<Longrightarrow> arcs_ends H = arcs H"
  by (auto simp: compatible_def arcs_ends_def arc_to_ends_def)

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

definition digraph_of_all_verts where
  "digraph_of_all_verts H G \<equiv> pre_digraph.add_verts (ddfs.digraph_of H) (dVs G)"

lemma "dVs G \<subseteq> verts (digraph_of_all_verts H G)"
  by (auto simp: digraph_of_all_verts_def pre_digraph.add_verts_simps)

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

definition sccs_dVs :: "'a dgraph \<Rightarrow> 'a set set" where
  "sccs_dVs G \<equiv> {S. S \<noteq> {} \<and> (\<forall>u \<in> S. \<forall>v \<in> S. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v) \<and> (\<forall>u \<in> S. \<forall>v. v \<notin> S \<longrightarrow> \<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)}"

definition scc_of :: "'a dgraph \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "scc_of G u \<equiv> {v. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<and> v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u}"

abbreviation "induced_subgraph_digraph \<equiv> Digraph_Component.induced_subgraph"
abbreviation "spanning_digraph \<equiv> Digraph_Component.spanning"
abbreviation "strongly_connected_digraph \<equiv> Digraph_Component.strongly_connected"
abbreviation "mk_symmetric_digraph \<equiv> Digraph_Component.mk_symmetric"
abbreviation "connected_digraph \<equiv> Digraph_Component.connected"

lemma in_induce_subgraphI[intro]:
  assumes "(u,v) \<in> G" "u \<in> vs" "v \<in> vs"
  shows "(u,v) \<in> G \<restriction> vs"
  using assms
  unfolding induce_subgraph_def
  by simp

lemma in_induce_subgraphD:
  assumes "(u,v) \<in> G \<restriction> vs"
  shows "(u,v) \<in> G" "u \<in> vs" "v \<in> vs"
  using assms unfolding induce_subgraph_def
  by auto

lemma in_induce_subgraphE[elim?]:
  assumes "(u,v) \<in> G \<restriction> vs"
  obtains "(u,v) \<in> G" "u \<in> vs" "v \<in> vs"
  using assms
  by (auto dest: in_induce_subgraphD)

lemma subgraph_induce_subgraph:
  "subgraph_ddfs (G \<restriction> vs) G"
  by (auto  dest: in_induce_subgraphD)

lemma subgraph_induce_subgraph':
  "H = (G \<restriction> vs) \<Longrightarrow> subgraph_ddfs H G"
  by (simp add: subgraph_induce_subgraph)

lemma subgraph_induced_subgraph:
  "induced_subgraph H G \<Longrightarrow> subgraph_ddfs H G"
  unfolding induced_subgraph_def
  by (auto simp: subgraph_induce_subgraph')

lemma induced_subgraphI[intro]:
  assumes "subgraph_ddfs H G"
  assumes "\<And>u v. \<lbrakk>(u,v) \<in> G; u \<in> dVs H; v \<in> dVs H\<rbrakk> \<Longrightarrow> (u,v) \<in> H"
    shows "induced_subgraph H G"
  using assms unfolding induced_subgraph_def induce_subgraph_def
  by (auto simp: dVsI)

lemma induced_subgraphD:
  assumes "induced_subgraph H G"
  shows "subgraph_ddfs H G"
  and "\<And>u v. \<lbrakk>(u,v) \<in> G; u \<in> dVs H; v \<in> dVs H\<rbrakk> \<Longrightarrow> (u,v) \<in> H"
  using assms unfolding induced_subgraph_def
  by (auto dest: subgraph_induce_subgraph')

lemma induced_subgraphE[elim?]:
  assumes "induced_subgraph H G"
  obtains "subgraph_ddfs H G"
  and "\<And>u v. \<lbrakk>(u,v) \<in> G; u \<in> dVs H; v \<in> dVs H\<rbrakk> \<Longrightarrow> (u,v) \<in> H"
  using assms
  by (auto dest: induced_subgraphD)

lemma spanningI[intro]:
  assumes "subgraph_ddfs H G"
  assumes "dVs G = dVs H"
  shows "spanning H G"
  using assms unfolding spanning_def
  by simp

lemma spanningD:
  assumes "spanning H G"
  shows "subgraph_ddfs H G" "dVs G = dVs H"
  using assms unfolding spanning_def
  by simp_all

lemma spanningE[elim?]:
  assumes "spanning H G"
  obtains "subgraph_ddfs H G" "dVs G = dVs H"
  using assms
  by (auto dest: spanningD)

lemma strongly_connectedI[intro]:
  assumes "G \<noteq> {}"
  assumes "\<And>u v. \<lbrakk>u \<in> dVs G; v \<in> dVs G\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  shows "strongly_connected G"
  using assms unfolding strongly_connected_def
  by auto

lemma strongly_connectedD:
  assumes "strongly_connected G"
  shows "G \<noteq> {}" "\<And>u v. \<lbrakk>u \<in> dVs G; v \<in> dVs G\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using assms unfolding strongly_connected_def
  by auto

lemma strongly_connectedE[elim?]:
  assumes "strongly_connected G"
  obtains "G \<noteq> {}" "\<And>u v. \<lbrakk>u \<in> dVs G; v \<in> dVs G\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using assms
  by (auto dest: strongly_connectedD)

lemma connectedI[intro]:
  assumes "strongly_connected (mk_symmetric G)"
  shows "connected G"
  using assms unfolding connected_def
  by simp

lemma connectedD:
  assumes "connected G"
  shows "strongly_connected (mk_symmetric G)"
  using assms unfolding connected_def
  by simp

lemma connectedE[elim?]:
  assumes "connected G"
  obtains "strongly_connected (mk_symmetric G)"
  using assms
  by (auto dest: connectedD)

lemma max_subgraphI[intro]:
  assumes "subgraph_ddfs H G"
  assumes "P H"
  assumes "\<And>H'. \<lbrakk>H'\<noteq>H; subgraph_ddfs H H'; subgraph_ddfs H' G\<rbrakk> \<Longrightarrow> \<not>P H"
  shows "max_subgraph G P H"
  using assms unfolding max_subgraph_def
  by auto

lemma max_subgraphD:
  assumes "max_subgraph G P H"
  shows "subgraph_ddfs H G" "P H"
  and "\<And>H'. \<lbrakk>H'\<noteq>H; subgraph_ddfs H H'; subgraph_ddfs H' G\<rbrakk> \<Longrightarrow> \<not>P H'"
  using assms unfolding max_subgraph_def
  by auto

lemma max_subgraphE[elim?]:
  assumes "max_subgraph G P H"
  obtains "subgraph_ddfs H G" "P H"
  and "\<And>H'. \<lbrakk>H'\<noteq>H; subgraph_ddfs H H'; subgraph_ddfs H' G\<rbrakk> \<Longrightarrow> \<not>P H'"
  using assms
  by (auto dest: max_subgraphD)

lemma in_sccsI[intro]:
  assumes "induced_subgraph H G"
  assumes "strongly_connected H"
  assumes "\<And>H'. \<lbrakk>induced_subgraph H' G; strongly_connected H'; dVs H \<subset> dVs H'\<rbrakk> \<Longrightarrow> False"
  shows "H \<in> sccs G"
  using assms unfolding sccs_def
  by auto

lemma in_sccsD:
  assumes "H \<in> sccs G"
  shows "induced_subgraph H G" "strongly_connected H"
  and "\<And>H'. \<lbrakk>induced_subgraph H' G; strongly_connected H'; dVs H \<subset> dVs H'\<rbrakk> \<Longrightarrow> False"
  using assms unfolding sccs_def
  by auto

lemma in_sccsE[elim?]:
  assumes "H \<in> sccs G"
  obtains "induced_subgraph H G" "strongly_connected H"
  and "\<And>H'. \<lbrakk>induced_subgraph H' G; strongly_connected H'; dVs H \<subset> dVs H'\<rbrakk> \<Longrightarrow> False"
  using assms
  by (auto dest: in_sccsD)

lemma in_sccs_dVsI[intro]:
  fixes G :: "'a dgraph"
  assumes "S \<noteq> {}"
  assumes "\<And>u v. \<lbrakk>u \<in> S; v \<in> S\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  assumes "\<And>u v. \<lbrakk>u \<in> S; v \<notin> S\<rbrakk> \<Longrightarrow> \<not> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not> v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
  shows "S \<in> sccs_dVs G"
  using assms unfolding sccs_dVs_def
  by auto

lemma in_sccs_dVsD:
  fixes G :: "'a dgraph"
  assumes "S \<in> sccs_dVs G"
  shows "S \<noteq> {}"
  and "\<And>u v. \<lbrakk>u \<in> S; v \<in> S\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  and "\<And>u v. \<lbrakk>u \<in> S; v \<notin> S\<rbrakk> \<Longrightarrow> \<not> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not> v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
  using assms unfolding sccs_dVs_def
  by auto

lemma in_sccs_dVsE[elim?]:
  fixes G :: "'a dgraph"
  assumes "S \<in> sccs_dVs G"
  obtains "S \<noteq> {}"
  and "\<And>u v. \<lbrakk>u \<in> S; v \<in> S\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  and "\<And>u v. \<lbrakk>u \<in> S; v \<notin> S\<rbrakk> \<Longrightarrow> \<not> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not> v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
  using assms
  by (auto dest: in_sccs_dVsD)

lemma in_scc_ofI[intro]:
  fixes G :: "'a dgraph"
  assumes "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u" "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  shows "v \<in> scc_of G u"
  using assms unfolding scc_of_def
  by simp

lemma in_scc_ofD:
  fixes G :: "'a dgraph"
  assumes "v \<in> scc_of G u"
  shows "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
  using assms unfolding scc_of_def
  by simp_all

lemma in_scc_ofE[elim?]:
  fixes G :: "'a dgraph"
  assumes "v \<in> scc_of G u"
  obtains "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
  using assms
  by (auto dest: in_scc_ofD)

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

lemma induced_imp_induced:
  "induced_subgraph H G \<Longrightarrow> induced_subgraph_digraph (ddfs.digraph_of H) (ddfs.digraph_of G)"
  unfolding Digraph_Component.induced_subgraph_def
  by (auto dest: induced_subgraphD simp flip: subgraph_iff simp: adj_in_dVs)

lemma induced_subgraph_sets_conv: 
  "{e \<in> G. fst e \<in> dVs H \<and> snd e \<in> dVs H} = {(u,v). (u,v) \<in> G \<and> u \<in> dVs H \<and> v \<in> dVs H}"
  by auto

lemma dVs_sym: "dVs {(v,u). (u,v) \<in> G} = dVs G"
  unfolding dVs_def by blast

lemma dVs_mk_symmetric: "dVs (mk_symmetric G) = dVs G"
  unfolding mk_symmetric_def by (simp add: dVs_union_distr dVs_sym)

lemma mk_symmetric_conv: "mk_symmetric G = (\<Union>x\<in>G. {x, (snd x, fst x)})"
  by (auto simp: mk_symmetric_def)


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
     (simp add: mk_symmetric_conv)

lemma connected_iff: "connected G \<longleftrightarrow> connected_digraph (ddfs.digraph_of G)"
  by (auto elim: connectedE simp: Digraph_Component.connected_def strongly_connected_iff mk_symmetric_eq)

lemma P_arcsI_subgraph:
  assumes "\<And>H'. subgraph (ddfs.digraph_of H') (ddfs.digraph_of G) \<Longrightarrow> P H'"
  assumes "subgraph H (ddfs.digraph_of G)"
  shows "(P \<circ> arcs) H"
  using assms
  by (auto dest!: subgraph_digraph_ofD[of H G])

lemma P_arcsD_subgraph:
  assumes "(P \<circ> arcs) H"
  assumes "subgraph H (ddfs.digraph_of G)"
  shows "(P \<circ> arcs) (ddfs.digraph_of (arcs H))"
  using assms
  by simp

  
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


lemma reachable_arcs_imp_reachable:
  assumes "Noschinski_to_DDFS.reachable (arcs H) u v"
  assumes "wf_digraph H"
  assumes "compatible H (ddfs.digraph_of G)"
  shows "Digraph.reachable H u v"
  using assms
  unfolding Digraph.reachable_def Noschinski_to_DDFS.reachable_def
  apply (auto simp: compatible_digraph_of_arcs_ends)
  by (meson dVs_arcs_subset_verts rtrancl_on_mono subset_refl)

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
  apply (auto elim!: pre_digraph.in_sccsE)
  by (smt assms(3) ddfs.verts_eq image_iff in_sccsI induced_imp_induced induced_subgraph_digraph_of_arcs strongly_connected_iff strongly_connected_induced_is_digraph_of)

lemma in_sccs_imp_in_sccs_digraph_of: "c \<in> sccs G \<Longrightarrow> ddfs.digraph_of c \<in> pre_digraph.sccs (ddfs.digraph_of G)"
  by (smt Digraph_Component.strongly_connected_def ddfs.verts_eq in_sccsD(1) in_sccsD(2) in_sccsD(3) induced_imp_induced induced_subgraph_digraph_of_arcs pre_digraph.in_sccsI psubsetE strongly_connected_iff strongly_connected_induced_is_digraph_of subsetI subset_empty subset_insert)

lemma in_sccs_digraph_of_imp_in_sccs:
  "(ddfs.digraph_of c) \<in> pre_digraph.sccs (ddfs.digraph_of G) \<Longrightarrow> c \<in> sccs G"
  unfolding sccs_def pre_digraph.sccs_def
  apply (simp add: induced_subgraph_iff strongly_connected_iff)
  by (metis ddfs.verts_eq)

lemma in_sccs_iff:
  shows "c \<in> sccs G \<longleftrightarrow> ddfs.digraph_of c \<in> pre_digraph.sccs (ddfs.digraph_of G)"
  using in_sccs_digraph_of_imp_in_sccs in_sccs_imp_in_sccs_digraph_of by metis


lemma sccs_dVs_eq: "sccs_dVs G = pre_digraph.sccs_verts (ddfs.digraph_of G)"
  by (auto simp: sccs_dVs_def pre_digraph.sccs_verts_def ddfs.reachable_iff)

lemma scc_of_eq': "scc_of G u = pre_digraph.scc_of (ddfs.digraph_of G) u"
  by (auto simp: scc_of_def pre_digraph.scc_of_def ddfs.reachable_iff)

subsection \<open>Basic lemmas\<close>
lemma subgraph_imp_subverts:
  assumes "subgraph_ddfs H G"
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
  by (auto simp flip: ddfs.awalk_iff ddfs.symmetric_iff simp: mk_symmetric_eq)
     (meson ddfs.wf_digraph_digraph_of wf_digraph.mk_symmetric_awalk_imp_awalk)

subsection \<open>Subgraphs and Induced Subgraphs\<close>
lemma subgraph_trans:
  assumes "subgraph_ddfs G H" "subgraph_ddfs H I" shows "subgraph_ddfs G I"
  using assms
  by (auto simp: subgraph_iff intro: subgraph_trans)

lemma adj_mono:
  fixes H G :: "'a dgraph"
  assumes "u \<rightarrow>\<^bsub>H\<^esub> v" "subgraph_ddfs H G"
  shows "u \<rightarrow>\<^bsub>G\<^esub> v"
  using assms
  by auto

lemma reachable_mono:
  fixes H G :: "'a dgraph"
  assumes "u \<rightarrow>\<^sup>*\<^bsub>H\<^esub> v" "subgraph_ddfs H G"
  shows "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using assms
  by (auto simp flip: ddfs.reachable_iff simp: subgraph_iff intro: pre_digraph.reachable_mono)

lemma subgraph_awalk_imp_awalk:
  assumes "awalk H u p v"
  assumes "subgraph_ddfs H G"
  shows "awalk G u p v"
  using assms
  by (auto simp flip: ddfs.awalk_iff simp: subgraph_iff intro: wf_digraph.subgraph_awalk_imp_awalk)

lemma subgraph_apath_imp_apath:
  assumes "apath H u p v"
  assumes "subgraph_ddfs H G"
  shows "apath G u p v"
  using assms
  by (simp flip: ddfs.apath_iff add: subgraph_iff wf_digraph.subgraph_apath_imp_apath)

lemma subgraph_mk_symmetric:
  assumes "subgraph_ddfs H G"
  shows "subgraph_ddfs (mk_symmetric H) (mk_symmetric G)"
  using assms
  by (simp add: subgraph_iff Digraph_Component.subgraph_mk_symmetric mk_symmetric_eq)

subsection \<open>Induced subgraphs\<close>
lemma digraph_of_induce_arcs: "arcs (ddfs.digraph_of (G \<restriction> vs)) = arcs (ddfs.digraph_of G) \<restriction> vs"
  unfolding induce_subgraph_def Digraph_Component.induce_subgraph_def
  by auto

lemma digraph_of_induce_verts:
  "verts (ddfs.digraph_of (G \<restriction> vs)) = verts ((ddfs.digraph_of G) \<restriction> vs)"
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
  by (metis (no_types, lifting) DDFS_Library_Component_Adaptor.induced_subgraphI ddfs.verts_eq ddfs.wf_digraph_digraph_of in_induce_subgraphI induce_sccs_dVs induced_subgraph_iff subgraph_induce_subgraph wf_digraph.induce_eq_iff_induced)

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
  assumes "max_subgraph G P H1" "max_subgraph G P H2" "subgraph_ddfs H1 H2"
  shows "H1 = H2"
  using assms
  by (auto elim: max_subgraphE)

definition arc_mono :: "('a dgraph \<Rightarrow> bool) \<Rightarrow> bool" where
  "arc_mono P \<equiv> (\<forall>H1 H2. P H1 \<and> subgraph_ddfs H1 H2 \<and> dVs H1 = dVs H2 \<longrightarrow> P H2)"

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
  assumes "subgraph_ddfs H G"
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


lemma
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
  shows "\<exists>C \<in> sccs G. \<exists>v \<in> dVs C. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
  oops
  text \<open>
    - sccs G = {}?
    - sccs G ~= {}, disconnected part with only singleton sccs?
    - connected G /\ sccs G ~= {}
  \<close>


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
  apply standard
  using assms by (auto simp: ddfs.reachable1_iff assms)

interpretation ddfs_scc_graph_dag: ddfs_dag "scc_graph E"
  by (intro ddfs_dagI_digraph_of)
     (meson arcs_ends_mono dag.acyclic ddfs.wf_digraph_digraph_of scc_graph_subset trancl_mono wf_digraph.scc_digraphI)
end
