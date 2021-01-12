theory DDFS_Component
  imports
    DDFS_Component_Defs
    Adaptors.DDFS_Library_Component_Adaptor
    DDFS_Awalk
    DDFS_Vwalk
begin

subsection \<open>Basic lemmas\<close>
lemma subgraph_refl: "subgraph G G"
  by auto

lemma induced_subgraph_refl: "induced_subgraph G G"
  by (simp add: induced_subgraph_iff wf_digraph.induced_subgraph_refl)


subsection \<open>The underlying symmetric graph of a digraph\<close>
lemma reachable_mk_symmetricI:
  fixes G :: "'a dgraph"
  assumes "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" shows "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> v"
  using assms
  by (auto simp: ddfs.reachable_iff mk_symmetric_eq intro: wf_digraph.reachable_mk_symmetricI)

lemma reachable_mk_symmetric_eq:
  assumes "sym G"
  shows "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using assms
  by (auto simp: ddfs.reachable_iff ddfs.symmetric_iff mk_symmetric_eq 
      intro!: wf_digraph.reachable_mk_symmetric_eq)

lemma mk_symmetric_awalk_imp_awalk:
  assumes "sym G"
  assumes "awalk (mk_symmetric G) u p v"
  obtains q where "awalk G u q v"
  using assms
  by (auto simp: ddfs.symmetric_iff ddfs.awalk_iff_awalk mk_symmetric_eq)
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
  by (auto simp: ddfs.reachable_iff subgraph_iff intro: pre_digraph.reachable_mono)

lemma reachable1_mono:
  fixes H G :: "'a dgraph"
  assumes "u \<rightarrow>\<^sup>+\<^bsub>H\<^esub> v" "subgraph H G"
  shows "u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v"
  using assms
  by (auto intro: trancl_mono)


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

lemma subgraph_cycle:
  assumes "subgraph H G" "cycle H p"
  shows "cycle G p"
  using assms
  by (simp add: subgraph_iff ddfs.cycle_iff_cycle wf_digraph.subgraph_cycle)


subsection \<open>Induced subgraphs\<close>

lemma digraph_of_induce_eq:
  "ddfs.digraph_of (G \<restriction> vs) = \<lparr>verts = dVs (G \<restriction> vs), arcs = arcs ((ddfs.digraph_of G) \<restriction> vs), tail = fst, head = snd\<rparr>"
  unfolding induce_subgraph_def Digraph_Component.induce_subgraph_def ddfs.digraph_of_def
  by auto

lemma digraph_of_induce_arcs_eq:
  "arcs (ddfs.digraph_of (G \<restriction> vs)) = arcs ((ddfs.digraph_of G) \<restriction> vs)"
  by (simp add: digraph_of_induce_eq)

lemma digraph_of_induce_arcs_ends_eq:
  "arcs_ends (ddfs.digraph_of (G \<restriction> vs)) = arcs_ends ((ddfs.digraph_of G) \<restriction> vs)"
  unfolding arcs_ends_def
  by (auto simp add: digraph_of_induce_arcs_eq induce_subgraph_def)


lemma induce_dVs_subset:
  "u \<in> dVs (G \<restriction> S) \<Longrightarrow> u \<in> S"
  unfolding induce_subgraph_def dVs_def by blast

lemma induced_induce:
  shows "induced_subgraph (G \<restriction> vs) G"
  by (auto simp: induced_subgraph_def dVs_def induce_subgraph_def)

lemma induced_graph_imp_symmetric:
  assumes "sym G"
  assumes "induced_subgraph H G"
  shows "sym H"
  using assms
  by (simp add: ddfs.symmetric_iff induced_subgraph_iff induced_graph_imp_symmetric)

lemma induce_reachable_preserves_paths:
  fixes G :: "'a dgraph"
  assumes "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  assumes "{w. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w} \<noteq> {u}"
  shows "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> {w. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w}\<^esub> v"
  using assms
proof (induction)
  case base
  then show ?case sorry
next
  case (step x y)
  then show ?case sorry
qed

lemma dominates_induce_subgraphD:
  fixes G :: "'a dgraph"
  assumes "u \<rightarrow>\<^bsub>G \<restriction> S\<^esub> v"
  shows "u \<rightarrow>\<^bsub>G\<^esub> v"
  using assms subgraph_def subgraph_induce_subgraph by auto

lemma induce_subgraph_mono:
  "S \<subseteq> T \<Longrightarrow> subgraph (G \<restriction> S) (G \<restriction> T)"
  by (auto simp: induce_subgraph_def)
  
lemma reachable_induce_subgraphD:
  fixes G :: "'a dgraph"
  assumes "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> S\<^esub> v"
  shows "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using assms
  by (auto simp add: subgraph_induce_subgraph intro: reachable_mono)

lemma dominates_induce_ss:
  fixes G :: "'a dgraph"
  assumes "u \<rightarrow>\<^bsub>G \<restriction> S\<^esub> v" "S \<subseteq> T"
  shows "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v"
  using assms
  by (auto simp: induce_subgraph_def)

lemma reachable_induce_ss:
  fixes G :: "'a dgraph"
  assumes "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> S\<^esub> v" "S \<subseteq> T"
  shows "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v"
  using assms
  by (auto intro: reachable_mono dest: induce_subgraph_mono)

lemma in_induce_subgraph_dVsI:
  assumes "u \<in> vs"
    and  "\<exists>v \<in> vs. (u, v) \<in> G \<or> (v, u) \<in> G"
  shows "u \<in> dVs (G \<restriction> vs)"
  using assms
  unfolding induce_subgraph_def
  by (auto intro: dVsI)

lemma awalk_induce:
  assumes "awalk G u p v" "set (awalk_verts u p) \<subseteq> S" "p \<noteq> []"
  shows "awalk (G \<restriction> S) u p v"
  unfolding awalk_def
  using assms
  apply (auto simp: hd_in_awalk_verts set_awalk_verts image_subset_iff intro!: in_induce_subgraph_dVsI)
   apply (metis (mono_tags, lifting) awalkE' cas_simp list.set_sel(1) prod.collapse subsetD)
  by (metis (no_types, lifting) CollectI awalkE' case_prodI fst_conv induce_subgraph_def snd_conv subsetD)

lemma induce_subgraph_of_subgraph_verts[simp]:
  "subgraph H G \<Longrightarrow> dVs (G \<restriction> dVs H) = dVs H"
  unfolding subgraph_def induce_subgraph_def dVs_def
  by blast

lemma induced_subgraphI':
  assumes subg: "subgraph H G"
    and max: "\<And>H'. subgraph H' G \<Longrightarrow> (dVs H' \<noteq> dVs H \<or> subgraph H' H)"
  shows "induced_subgraph H G"
  by (meson DDFS_Component_Defs.induced_subgraphI adj_mono in_induce_subgraphI induce_subgraph_of_subgraph_verts max subg subgraph_induce_subgraph)

lemma induced_subgraph_altdef:
  "induced_subgraph H G \<longleftrightarrow> subgraph H G \<and> (\<forall>H'. subgraph H' G \<longrightarrow> dVs H' \<noteq> dVs H \<or> subgraph H' H)"
  by (metis DDFS_Component.induced_subgraphI' ddfs.verts_eq ddfs.wf_digraph_digraph_of induced_subgraph_iff subgraph_iff subgraph_induce_subgraphI2 induced_subgraphD wf_digraph.induce_eq_iff_induced)

lemma in_induce_subgraph_dVsI_reachable:
  fixes G :: "'a dgraph"
  assumes "u \<in> S"
    and "v \<in> S"
    and "S \<in> sccs_dVs G"
    and "S \<noteq> {u} \<or> (u,v) \<in> G"
    and "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  shows "u \<in> dVs (G \<restriction> S)" "v \<in> dVs (G \<restriction> S)"
  using assms
  by (auto intro!: in_induce_subgraph_dVsI simp: sccs_dVs_def)
     (metis (no_types, lifting) converse_tranclE reachable1_reachable reachable_neq_reachable1 trancl.intros(1) trancl_trans)+

lemma induce_sccs_dVs:
  assumes "S \<in> sccs_dVs G"
  assumes "u \<in> S" "S \<noteq> {u} \<or> (u,u) \<in> G"
  shows "dVs (G \<restriction> S) = S"
proof
  show "dVs (G \<restriction> S) \<subseteq> S" by (auto dest: induce_dVs_subset)
  then show "S \<subseteq> dVs (G \<restriction> S)"
    by (smt Diff_eq_empty_iff assms in_induce_subgraph_dVsI_reachable(2) in_sccs_dVsD(2) insert_Diff subsetI)
qed

lemma induce_sccs_dVs_digraph_of_eq:
  assumes "S \<in> sccs_dVs G"
  assumes "u \<in> S" "S \<noteq> {u} \<or> (u,u) \<in> G"
  shows "ddfs.digraph_of (G \<restriction> S) = ddfs.digraph_of G \<restriction> S"
  using assms
  by (metis (no_types, lifting) induced_subgraphI ddfs.verts_eq ddfs.wf_digraph_digraph_of in_induce_subgraphI induce_sccs_dVs induced_subgraph_iff subgraph_induce_subgraph wf_digraph.induce_eq_iff_induced)

lemma induce_subgraph_singleton_conv:
  "v \<in> dVs (G \<restriction> {u}) \<longleftrightarrow> v = u \<and> (u,u) \<in> G"
  unfolding induce_subgraph_def dVs_def
  by auto


subsection \<open>Unions of Graphs\<close>

lemma subgraph_union_iff:
  "subgraph (H1 \<union> H2) G \<longleftrightarrow> subgraph H1 G \<and> subgraph H2 G"
  by (simp add: subgraph_iff union_eq subgraph_union_iff)

lemma subgraph_union[intro]:
  assumes "subgraph H1 G"
  assumes "subgraph H2 G"
  shows "subgraph (H1 \<union> H2) G"
  using assms
  by (simp add: subgraph_iff union_eq subgraph_union)

lemma subgraphs_of_union:
  shows "subgraph G (G \<union> G')"
    and "subgraph G' (G \<union> G')"
  unfolding subgraph_def by auto

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

lemma subgraph_induce_subgraphI2:
  "subgraph H G \<Longrightarrow> subgraph H (G \<restriction> dVs H)"
  by (auto simp: subgraph_def induce_subgraph_def dVsI)

definition arc_mono :: "('a dgraph \<Rightarrow> bool) \<Rightarrow> bool" where
  "arc_mono P \<equiv> (\<forall>H1 H2. P H1 \<and> subgraph H1 H2 \<and> dVs H1 = dVs H2 \<longrightarrow> P H2)"

lemma induced_subgraphI_arc_mono:
  assumes "max_subgraph G P H"
  assumes "arc_mono P"
  shows "induced_subgraph H G"
  using assms
  unfolding induced_subgraph_def arc_mono_def max_subgraph_def
  by (metis induce_subgraph_of_subgraph_verts subgraph_induce_subgraph subgraph_induce_subgraphI2)

lemma subgraph_induced_subgraph_neq:
  assumes "induced_subgraph H G" "subgraph H H'" "H \<noteq> H'"
  shows "\<not>subgraph H' G \<or> dVs H' \<noteq> dVs H"
  using assms
  by (auto simp: induced_subgraph_altdef subgraph_def)


lemma induced_subgraph_altdef2:
  "induced_subgraph H G \<longleftrightarrow> max_subgraph G (\<lambda>H'. dVs H' = dVs H) H"
  by (auto intro!: induced_subgraphI_arc_mono simp: arc_mono_def max_subgraph_def induced_subgraphD
        dest: subgraph_induced_subgraph_neq)

lemma max_subgraphI:
  assumes "P x" "subgraph x G" "\<And>y. \<lbrakk>x \<noteq> y; subgraph x y; subgraph y G\<rbrakk> \<Longrightarrow> \<not>P y"
  shows "max_subgraph G P x"
  using assms by (auto simp: max_subgraph_def)

lemma subgraphI_max_subgraph: "max_subgraph G P x \<Longrightarrow> subgraph x G"
  by (simp add: max_subgraph_def)

subsection \<open>Connected and Strongly Connected Graphs\<close>

lemma in_sccs_dVs_conv_reachable:
  "S \<in> sccs_dVs G \<longleftrightarrow> S \<noteq> {} \<and> (\<forall>u \<in> S. \<forall>v \<in> S. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v) \<and> (\<forall>u \<in> S. \<forall>v. v \<notin> S \<longrightarrow> \<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)"
  by (simp add: sccs_dVs_def)

lemma sccs_dVs_disjoint:
  assumes "S \<in> sccs_dVs G" "T \<in> sccs_dVs G" "S \<noteq> T" shows "S \<inter> T = {}"
  using assms
  by (intro wf_digraph.sccs_verts_disjoint[of "ddfs.digraph_of G"])
     (simp_all add: sccs_dVs_eq)

lemma strongly_connected_spanning_imp_strongly_connected:
  assumes "spanning H G"
  assumes "strongly_connected H"
  shows "strongly_connected G"
  using assms
  by (simp add: spanning_iff strongly_connected_iff wf_digraph.strongly_connected_spanning_imp_strongly_connected)

lemma strongly_connected_imp_induce_subgraph_strongly_connected:
  assumes subg: "subgraph H G"
    and sc: "strongly_connected H"
  shows "strongly_connected (G \<restriction> dVs H)"
  by (auto intro: strongly_connected_spanning_imp_strongly_connected[of H "G \<restriction> dVs H"] 
           simp: sc spanning_def subg subgraph_induce_subgraphI2)

lemma sccs_dVs_restrict_eq:
  "S \<in> dVs ` sccs G \<Longrightarrow> dVs (G \<restriction> S) = S"
  by (auto dest: induce_dVs_subset induced_subgraphD elim!: in_sccsE)


lemma in_sccs_dVsI_sccs:
  assumes "S \<in> dVs ` sccs G" shows "S \<in> sccs_dVs G"
  using assms
  by (force simp: sccs_dVs_eq in_sccs_iff wf_digraph.sccs_verts_conv image_iff)


lemma arc_mono_strongly_connected[intro,simp]: "arc_mono strongly_connected"
  by (auto simp: arc_mono_def strongly_connected_def dest: reachable_mono)

lemma sccs_altdef:
  "sccs G = {H. max_subgraph G strongly_connected H}" (is "?L = ?R")
proof -
  { fix H H' :: "'a dgraph"
    assume a1: "strongly_connected H'"
    assume a2: "induced_subgraph H' G"
    assume a3: "max_subgraph G strongly_connected H"
    assume a4: "H \<subseteq> H'"
    have sg: "subgraph H G" using a3 by (auto simp: max_subgraph_def)
    then have "H = H'"
      using a1 a2 a3 a4
      by (metis induced_subgraphD max_subgraph_def subgraphI)
  } note X = this

  { fix H
    assume a1: "induced_subgraph H G"
    assume a2: "strongly_connected H"
    assume a3: "\<forall>H'. strongly_connected H' \<longrightarrow> induced_subgraph H' G \<longrightarrow> \<not> H \<subset> H'"
    { fix y assume "H \<noteq> y" and subg: "subgraph H y" "subgraph y G"
      then have "H \<subset> y"
        using a1 by (auto simp: induced_subgraph_altdef2 subgraph_dVs' subgraph_def)
      then have "\<not>strongly_connected y"
        by (meson a3 induced_induce less_le_trans strongly_connected_imp_induce_subgraph_strongly_connected subg(2) subgraphD subgraph_induce_subgraphI2)
    }
    then have "max_subgraph G strongly_connected H"
      using a1 a2 by (auto intro: max_subgraphI dest: induced_subgraphD)
  } note Y = this
  show ?thesis unfolding sccs_def
    by (auto dest: max_subgraph_prop X intro: induced_subgraphI_arc_mono Y)
qed

locale max_reachable_set = ddfs + 
  fixes S assumes S_in_sv: "S \<in> sccs_dVs E"
begin

  interpretation digraph_max_r_set: Digraph_Component.max_reachable_set digraph_of S
    using S_in_sv
    by (unfold_locales)
       (simp add: sccs_dVs_eq)
  
  lemma reach_in: "\<And>u v. \<lbrakk>u \<in> S; v \<in> S\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
    and not_reach_out: "\<And>u v. \<lbrakk>u \<in> S; v \<notin> S\<rbrakk> \<Longrightarrow> \<not>u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> u"
    and not_empty: "S \<noteq> {}"
    using S_in_sv by (auto simp: sccs_dVs_def)
  
  lemma reachable_induced:
    assumes conn: "u \<in> S" "v \<in> S" "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
    assumes "S \<noteq> {u} \<or> (u,u) \<in> E"
    shows "u \<rightarrow>\<^sup>*\<^bsub>E \<restriction> S\<^esub> v"
    using assms S_in_sv
    by (simp add: sccs_dVs_eq induce_sccs_dVs_digraph_of_eq ddfs.reachable_iff digraph_max_r_set.reachable_induced)
  
  lemma strongly_connected:
    assumes "u \<in> S" "S \<noteq> {u} \<or> (u,u) \<in> E"
    shows "strongly_connected (E \<restriction> S)"
    using assms S_in_sv
    by (simp add: induce_sccs_dVs_digraph_of_eq strongly_connected_iff digraph_max_r_set.strongly_connected)

end

lemma in_sccs_dVsD_sccs:
  assumes "S \<in> sccs_dVs G"
  assumes "u \<in> S" "S \<noteq> {u} \<or> (u,u) \<in> G"
  shows "G \<restriction> S \<in> sccs G"
  using assms wf_digraph.in_verts_sccsD_sccs ddfs.wf_digraph_digraph_of
  unfolding in_sccs_iff sccs_dVs_eq induce_sccs_dVs_digraph_of_eq[OF assms]
  by blast

text \<open>
  This lemma (and those above used to prove it) highlights an inherent restriction of the chosen 
  graph representation with an implicit vertex set. Obviously an SCC might consist of a single
  vertex. When representing the SCCs as sets of vertices this does not pose a problem. On the other
  hand, when considering SCCs as subgraphs the only way a single-vertex SCC is captured is when
  a self-loop exists, i.e.\ as \<^term>\<open>{(u,u)}\<close>.
\<close>
lemma sccs_dVs_image_sccs_conv: "sccs_dVs G - {{u} |u. (u,u) \<notin> G} = dVs ` sccs G" (is "?L = ?R")
proof
  { fix S assume "S \<in> ?L"
    then have scc: "S \<in> sccs_dVs G" and "((\<forall>u. S \<noteq> {u}) \<or> (\<exists>u. S = {u} \<and> (u,u) \<in> G))"
      by (auto simp: in_sccs_dVs_conv_reachable reachable_in_dVs)
    then have not_singleton: "\<And>u. S \<noteq> {u} \<or> (u,u) \<in> G" by blast

    interpret ms: max_reachable_set G S using scc
      by (rule max_reachable_set.intro)

    have "S \<in> ?R" using scc not_singleton ms.not_empty
      by auto
         (metis image_eqI in_sccs_dVsD_sccs induce_sccs_dVs)
  }
  then show "?L \<subseteq> ?R" by blast
next
  { fix S assume "S \<in> ?R"
    then have "S \<in> ?L"
      by (auto simp add: in_sccs_dVsI_sccs induce_subgraph_singleton_conv dest!: sccs_dVs_restrict_eq)
  }
  then show "?R \<subseteq> ?L" by blast
qed

text \<open>
  \<^term>\<open>G \<restriction> {u} = {}\<close> if \<^term>\<open>(u,u) \<notin> G\<close>.
\<close>
lemma sccs_conv_sccs_dVs: 
  "sccs G = induce_subgraph G ` sccs_dVs G - {{}}" (is "?L = ?R")
proof
  { fix S assume "S \<in> sccs G"
    then have "S \<in> ?R" 
      by (auto elim!: in_sccsE dest: strongly_connectedD simp: induced_subgraph_def)
         (simp add: induced_subgraph_def \<open>S \<in> sccs G\<close> in_sccs_dVsI_sccs)
  }
  then show "?L \<subseteq> ?R" by blast
next
  { fix S assume "S \<in> ?R"
    then have "S \<in> ?L"
      by (auto)
         (metis dVsI(1) in_induce_subgraphD(3) in_sccs_dVsD_sccs induce_subgraph_singleton_conv)
  }
  then show "?R \<subseteq> ?L" by blast
qed

lemma connected_conv:
  "connected G \<longleftrightarrow> dVs G \<noteq> {} \<and> (\<forall>u \<in> dVs G. \<forall>v \<in> dVs G. (u,v) \<in> rtrancl_on (dVs G) (G\<^sup>s))"
  by (simp add: connected_iff connected_conv)

lemma symmetric_connected_imp_strongly_connected:
  assumes "sym G" "connected G"
  shows "strongly_connected G"
  using assms
  by (simp add: ddfs.symmetric_iff connected_iff strongly_connected_iff wf_digraph.symmetric_connected_imp_strongly_connected)

lemma connected_spanning_imp_connected:
  assumes "spanning H G" "connected H"
  shows "connected G"
  using assms
  by (simp add: connected_iff spanning_iff wf_digraph.connected_spanning_imp_connected)

lemma induced_eq_dVs_imp_eq:
  assumes "induced_subgraph G H"
  assumes "induced_subgraph G' H"
  assumes "dVs G = dVs G'"
  shows "G = G'"
  using assms by (auto intro!: induced_eq_verts_imp_eq digraph_of_eq_imp_eq simp: induced_subgraph_iff)

declare connectedI[rule del]
lemma connectedI':
  assumes "G \<noteq> {}" "\<And>u v. u \<in> dVs G \<Longrightarrow> v \<in> dVs G \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> v"
  shows "connected G"
  using assms
  by (auto intro: wf_digraph.connectedI simp: connected_iff ddfs.reachable_iff mk_symmetric_eq)

lemma connected_awalkE:
  assumes "connected G" "u \<in> dVs G" "v \<in> dVs G"
  obtains p where "awalk (mk_symmetric G) u p v"
  using assms
  by (auto simp add: connected_iff ddfs.awalk_iff_awalk mk_symmetric_eq simp flip: ddfs.verts_eq)
     (meson ddfs.wf_digraph_digraph_of wf_digraph.connected_awalkE)

lemma in_sccs_subset_imp_eq:
  assumes "c \<in> sccs G"
  assumes "d \<in> sccs G"
  assumes "dVs c \<subseteq> dVs d"
  shows "c = d"
  using assms
  by (simp add: in_sccs_iff pre_digraph.in_sccs_subset_imp_eq flip: ddfs.verts_eq eq_iff_digraph_of_eq)

lemma inj_on_dVs_sccs: "inj_on dVs (sccs G)"
  by (auto intro: inj_onI elim!: in_sccsE dest: induced_eq_dVs_imp_eq)

lemma card_sccs: "card (sccs_dVs G - {{u} |u. (u,u) \<notin> G}) = card (sccs G)"
  by (auto simp: sccs_dVs_image_sccs_conv intro: inj_on_dVs_sccs card_image)

lemma strongly_connected_non_disj:
  assumes "strongly_connected G" "strongly_connected H"
  assumes "dVs G \<inter> dVs H \<noteq> {}"
  shows "strongly_connected (G \<union> H)"
  using assms
  by (simp add: strongly_connected_iff union_eq strongly_connected_non_disj flip: ddfs.verts_eq)

lemma scc_disj:
  assumes "c \<in> sccs G" "d \<in> sccs G"
  assumes "c \<noteq> d"
  shows "dVs c \<inter> dVs d = {}"
  using assms wf_digraph.scc_disj
  by (force simp add: in_sccs_iff simp flip: ddfs.verts_eq eq_iff_digraph_of_eq)

lemma induce_in_sccs_imp_in_sccs_dVs:
  assumes "S \<subseteq> dVs G"
  assumes "G \<restriction> S \<in> sccs G"
  shows "S \<in> sccs_dVs G"
  using assms
  apply (simp add: sccs_dVs_eq in_sccs_iff)
  oops


lemma in_scc_of_self: "u \<in> dVs G \<Longrightarrow> u \<in> scc_of G u"
  by (simp add: scc_of_eq wf_digraph.in_scc_of_self flip: ddfs.verts_eq)

lemma scc_of_empty_conv: "scc_of G u = {} \<longleftrightarrow> u \<notin> dVs G"
  by (simp add: scc_of_eq wf_digraph.scc_of_empty_conv flip: ddfs.verts_eq)

lemma scc_of_in_sccs_dVs:
  "u \<in> dVs G \<Longrightarrow> scc_of G u \<in> sccs_dVs G"
  by (simp add: scc_of_eq sccs_dVs_eq wf_digraph.scc_of_in_sccs_verts flip: ddfs.verts_eq)

lemma sccs_dVs_subsets: "S \<in> sccs_dVs G \<Longrightarrow> S \<subseteq> dVs G"
  by (simp add: sccs_dVs_eq wf_digraph.sccs_verts_subsets flip: ddfs.verts_eq)

lemma sccs_dVs_conv_scc_of:
  "sccs_dVs G = scc_of G ` dVs G"
  by (simp add: sccs_dVs_eq scc_of_eq wf_digraph.sccs_verts_conv_scc_of flip: ddfs.verts_eq)

lemma scc_of_eq': "u \<in> scc_of G v \<Longrightarrow> scc_of G u = scc_of G v"
  by (simp add: scc_of_eq wf_digraph.scc_of_eq)

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

subsection \<open>Vertex walks\<close>
lemma vwalk_subgraph:
  assumes "vwalk E p" "subgraph E E'"
  shows "vwalk E' p"
  using assms dVs_subset
  by (induction, auto)

lemma vwalk_edges_of_vwalk_refl: "length p \<ge> 2 \<Longrightarrow> vwalk (set (edges_of_vwalk p)) p"
proof (induction p rule: edges_of_vwalk.induct)
  case (3 v v' l)
  thus ?case
    by (cases l) (auto intro: vwalk_subgraph simp add: vwalk2 dVs_def)
qed simp_all

lemma vwalk_edges_subset:
  assumes "vwalk E p"
  shows "subgraph (set (edges_of_vwalk p)) E"
  using assms
  by (induction, auto)

lemma vwalk_bet_subgraph:
  assumes "subgraph E E'"
  assumes "vwalk_bet E p u v"
  shows "vwalk_bet E' p u v"
  using assms vwalk_subgraph
  unfolding vwalk_bet_def by blast

subsection \<open>Vertex induced subgraphs\<close>
definition vertex_induced_subgraph :: "('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where
  "vertex_induced_subgraph H V G \<equiv> H = {(u, v) \<in> G. {u, v} \<subseteq> V}"

lemma vertex_induced_subgraphI[intro]:
  "H = {(u, v) \<in> G. {u, v} \<subseteq> V} \<Longrightarrow> vertex_induced_subgraph H V G" by (simp add: vertex_induced_subgraph_def)

lemma vertex_induced_subgraphE[elim]:
  assumes "vertex_induced_subgraph H V G"
  obtains "H = {(u, v) \<in> G. {u, v} \<subseteq> V}"
  using assms by (simp add: vertex_induced_subgraph_def)

lemma vertex_induced_subgraph_subgraph:
  "vertex_induced_subgraph H V G \<Longrightarrow> subgraph H G"
  by auto

lemma vertex_induced_subgraph_dVs_subset_V:
  "vertex_induced_subgraph H V G \<Longrightarrow> dVs H \<subseteq> V"
  unfolding vertex_induced_subgraph_def dVs_def
  by auto

lemma vertex_induced_subgraph_dVs_subset_Int:
  "vertex_induced_subgraph H V G \<Longrightarrow> dVs H \<subseteq> dVs G \<inter> V" \<comment> \<open>vertices might become disconnected\<close>
  by (simp add: vertex_induced_subgraph_dVs_subset_V vertex_induced_subgraph_subgraph subgraph_dVs)

lemma vwalk_vertex_induced_subgraph_vwalk:
  assumes "vwalk G (u # p @ [v])" \<comment> \<open>vertices are only in the induced subgraph when they don't get disconnected\<close>
  assumes "vertex_induced_subgraph H V G"
  assumes "set (u # p @ [v]) \<subseteq> V"
  shows "vwalk H (u # p @ [v])"
  using assms
  by (induction p arbitrary: u)
     (auto simp: dVsI)

lemma vwalk_bet_vertex_induced_subgraph:
  assumes "vwalk_bet G (u # p @ [v]) u v"
  assumes "vertex_induced_subgraph H V G"
  assumes "set (u # p @ [v]) \<subseteq> V"
  shows "vwalk_bet H (u # p @ [v]) u v"
  using assms
  by (auto intro!: nonempty_vwalk_vwalk_bet simp: vwalk_bet_def vwalk_vertex_induced_subgraph_vwalk)


end