theory DDFS_SCC
  imports Ports.Mitja_to_DDFS
begin


definition induce_subgraph :: "'a dgraph \<Rightarrow> 'a set \<Rightarrow> 'a dgraph" (infix "\<restriction>" 67) where
  "G \<restriction> vs \<equiv> {(u,v) \<in> G. u \<in> vs \<and> v \<in> vs}"

definition induced_subgraph :: "'a dgraph \<Rightarrow> 'a dgraph \<Rightarrow> bool" where
  "induced_subgraph H G \<equiv> H = G \<restriction> dVs H" \<comment> \<open>not sure if this definition is "nice"\<close>

definition spanning :: "'a dgraph \<Rightarrow> 'a dgraph \<Rightarrow> bool" where
  "spanning H G \<equiv> subgraph H G \<and> dVs G = dVs H"

definition strongly_connected :: "'a dgraph \<Rightarrow> bool" where
  "strongly_connected G \<equiv> G \<noteq> {} \<and> (\<forall>u \<in> dVs G. \<forall>v \<in> dVs G. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v)"

definition max_subgraph :: "'a dgraph \<Rightarrow> ('a dgraph \<Rightarrow> bool) \<Rightarrow> 'a dgraph \<Rightarrow> bool" where
  "max_subgraph G P H \<equiv> subgraph H G \<and> P H \<and> (\<forall>H'. H' \<noteq> H \<and> subgraph H H' \<longrightarrow> \<not>(subgraph H' G \<and> P H'))"

lemma "induced_subgraph H G \<Longrightarrow> induced_subgraph H' G \<Longrightarrow> dVs H \<subset> dVs H' \<longleftrightarrow> H \<subset> H'"
  unfolding induced_subgraph_def induce_subgraph_def subset_eq
  by (auto dest: dVs_subset) blast

definition sccs :: "'a dgraph \<Rightarrow> 'a dgraph set" where
  "sccs G \<equiv> {H. induced_subgraph H G \<and> strongly_connected H \<and> \<not>(\<exists>H'. induced_subgraph H' G
      \<and> strongly_connected H' \<and> H \<subset> H')}" \<comment> \<open>can we replace \<^term>\<open>dVs H \<subset> dVs H'\<close> with
                                                              \<^term>\<open>H \<subset> H'\<close>? yes - see lemma above\<close>

definition sccs_dVs :: "'a dgraph \<Rightarrow> 'a set set" where
  "sccs_dVs G \<equiv> {S. S \<noteq> {} \<and> (\<forall>u \<in> S. \<forall>v \<in> S. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v) \<and> (\<forall>u \<in> S. \<forall>v. v \<notin> S \<longrightarrow> \<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)}"

definition scc_of :: "'a dgraph \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "scc_of G u \<equiv> {v. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<and> v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u}"


lemma induce_subgraph_dVs:
  "dVs (G \<restriction> vs) \<subseteq> vs"
  by (auto simp: induce_subgraph_def dVs_def)

lemma induce_subgraph_dVsD:
  "u \<in> dVs (G \<restriction> vs) \<Longrightarrow> u \<in> vs"
  using induce_subgraph_dVs by fast

lemma induce_subgraph_verts':
  "dVs (G \<restriction> vs) = vs - {v \<in> vs. \<not>(\<exists>u \<in> vs. (u,v) \<in> G \<or> (v,u) \<in> G)}"
  unfolding dVs_def induce_subgraph_def
  by auto

lemma in_induce_subgraph_dVsI:
  assumes "u \<in> vs"
    and  "\<exists>v \<in> vs. (u, v) \<in> G \<or> (v, u) \<in> G"
  shows "u \<in> dVs (G \<restriction> vs)"
  using assms
  unfolding induce_subgraph_def
  by (auto intro: dVsI)

lemma in_induce_subgraph_dVsI_reachable:
  assumes "u \<in> S"
    and "v \<in> S"
    and "S \<in> sccs_dVs G"
    and "S \<noteq> {u}"
    and "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  shows "u \<in> dVs (G \<restriction> S)" "v \<in> dVs (G \<restriction> S)"
  using assms
  by (auto intro!: in_induce_subgraph_dVsI simp: sccs_dVs_def)
     (metis (no_types, lifting) converse_tranclE reachable1_reachable reachable_neq_reachable1 trancl.intros(1) trancl_trans)+

lemma induce_subgraph_of_subgraph_verts[simp]:
  "subgraph H G \<Longrightarrow> dVs (G \<restriction> dVs H) = dVs H"
  unfolding subgraph_def induce_subgraph_def dVs_def
  by blast

lemma subgraph_induce_subgraph:
  "subgraph (G \<restriction> vs) G"
  by (auto simp: induce_subgraph_def)

lemma induced_induce: "induced_subgraph (G \<restriction> vs) G"
  unfolding induced_subgraph_def induce_subgraph_def
  by (auto simp: adj_in_dVs dVs_def)

lemma induced_subgraphD:
  "induced_subgraph H G \<Longrightarrow> H = G \<restriction> dVs H"
  unfolding induced_subgraph_def by simp

lemma induce_subgraph_singleton_conv:
  "v \<in> dVs (G \<restriction> {u}) \<longleftrightarrow> v = u \<and> (u,u) \<in> G"
  unfolding induce_subgraph_def dVs_def
  by auto

lemma induce_subgraph_not_empty:
  "u \<in> S \<Longrightarrow> v \<in> S \<Longrightarrow> (u,v) \<in> G \<Longrightarrow> G \<restriction> S \<noteq> {}"
  unfolding induce_subgraph_def by blast


subsection \<open>Basic lemmas\<close>
lemma strongly_connectedI[intro]:
  assumes "G \<noteq> {}" "\<And>u v. u \<in> dVs G \<Longrightarrow> v \<in> dVs G \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  shows "strongly_connected G"
  using assms by (simp add: strongly_connected_def)

lemma strongly_connectedE[elim]:
  assumes "strongly_connected G"
  obtains u v where "u \<in> dVs G" "v \<in> dVs G" "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using assms by (auto simp add: strongly_connected_def dest!: dVsI)

lemma induced_imp_subgraph:
  "induced_subgraph H G \<Longrightarrow> subgraph H G"
  using subgraph_induce_subgraph[of G "dVs H"]
  by (auto dest: induced_subgraphD)

lemma in_sccs_imp_induced:
  "c \<in> sccs G \<Longrightarrow> induced_subgraph c G"
  by (auto simp: sccs_def)

lemma spanningE[elim]:
  assumes "spanning H G"
  assumes "\<lbrakk>subgraph H G; dVs G = dVs H\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms by (simp add: spanning_def)

lemma in_sccsI[intro]:
  assumes "induced_subgraph c G"
    and "strongly_connected c"
    and "\<not>(\<exists>c'. induced_subgraph c' G \<and> strongly_connected c' \<and> c \<subset> c')"
  shows "c \<in> sccs G"
  using assms by (auto simp add: sccs_def)

lemma in_sccsE[elim]:
  assumes "c \<in> sccs G"
    and "induced_subgraph c G \<Longrightarrow> strongly_connected c \<Longrightarrow> \<not>(\<exists>c'.
      induced_subgraph c' G \<and> strongly_connected c' \<and> c \<subset> c') \<Longrightarrow> P"
  shows "P"
  using assms by (simp add: sccs_def)

lemma sccs_dVs_subset_dVs:
  "S \<in> sccs_dVs G \<Longrightarrow> S \<subseteq> dVs G"
  unfolding sccs_dVs_def 
  by (auto dest: reachable_in_dVs)

subsection \<open>Induced subgraphs\<close>
lemma induced_subgraphI[intro]:
  assumes "H = {(u,v) \<in> G. u \<in> dVs H \<and> v \<in> dVs H}"
  shows "induced_subgraph H G"
  using assms
  by (simp add: induced_subgraph_def induce_subgraph_def)

lemma induced_subgraphE[elim]:
  assumes "induced_subgraph H G"
    and "H = {(u,v) \<in> G. u \<in> dVs H \<and> v \<in> dVs H} \<Longrightarrow> P"
  shows "P"
  using assms by (simp add: induced_subgraph_def induce_subgraph_def)

lemma induced_subgraph_refl:
  "induced_subgraph G G"
  by (auto intro: induced_subgraphI simp: adj_in_dVs)

lemma induced_subgraph_symmetric:
  assumes "sym G"
    and "induced_subgraph H G"
  shows "sym H"
  using assms
  by (auto simp add: induced_subgraph_def induce_subgraph_def dVs_def sym_def) blast

lemma induce_subgraph_mono:
  "S \<subseteq> T \<Longrightarrow> subgraph (G \<restriction> S) (G \<restriction> T)"
  by (auto simp: induce_subgraph_def)

lemmas induce_subgraph_mono' = induce_subgraph_mono[simplified subgraph_def]

lemma dominates_induce_subgraphD:
  "u \<rightarrow>\<^bsub>G \<restriction> S\<^esub> v \<Longrightarrow> u \<rightarrow>\<^bsub>G\<^esub> v"
  using subgraph_def subgraph_induce_subgraph by auto

lemma reachable_induce_subgraphD:
  "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> S\<^esub> v \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  by (simp add: subgraph_induce_subgraph subgraph_reachable)

lemma dominates_induce_ss:
  "u \<rightarrow>\<^bsub>G \<restriction> S\<^esub> v \<Longrightarrow> S \<subseteq> T \<Longrightarrow> u \<rightarrow>\<^bsub>G \<restriction> T\<^esub> v"
  by (auto simp: induce_subgraph_def)

lemma reachable_induce_ss:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> S\<^esub> v" "S \<subseteq> T" shows "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v"
  using assms
  by (auto intro: reachable_mono dest: induce_subgraph_mono)

lemma awalk_induce:
  assumes "awalk G u p v" "set (awalk_verts u p) \<subseteq> S" "p \<noteq> []"
  shows "awalk (G \<restriction> S) u p v"
  unfolding awalk_def
  using assms
  apply (auto simp: hd_in_awalk_verts set_awalk_verts image_subset_iff intro!: in_induce_subgraph_dVsI)
   apply (metis (mono_tags, lifting) awalkE' cas_simp list.set_sel(1) prod.collapse subsetD)
  by (metis (no_types, lifting) CollectI awalkE' case_prodI fst_conv induce_subgraph_def snd_conv subsetD)


lemma induced_subgraphI':
  assumes subg: "subgraph H G"
    and max: "\<And>H'. subgraph H' G \<Longrightarrow> (dVs H' \<noteq> dVs H \<or> subgraph H' H)"
  shows "induced_subgraph H G"
proof -
  define H' where "H' = G \<restriction> dVs H"
  then have H'_props: "subgraph H' G" "dVs H' = dVs H"
    using subg by(auto intro: subgraph_induce_subgraph)
  moreover
  have "H' = H"
  proof
    show "H' \<subseteq> H" using max H'_props by (auto simp: subgraph_def)
    show "H \<subseteq> H'" using subg by (auto simp: H'_def subgraph_def induce_subgraph_def dVsI)
  qed
  then show "induced_subgraph H G" by (simp add: induced_subgraph_def H'_def)
qed

lemma induced_subgraph_altdef:
  "induced_subgraph H G \<longleftrightarrow> subgraph H G \<and> (\<forall>H'. subgraph H' G \<longrightarrow> dVs H' \<noteq> dVs H \<or> subgraph H' H)"
proof -
  { fix H' :: "'a dgraph"
    assume A: "dVs H' = dVs H" "subgraph H' G"
    then have "H' \<subseteq> {(u,v) \<in> G. u \<in> dVs H \<and> v \<in> dVs H}"  
      unfolding subgraph_def by (auto simp: dVsI)
  }
  then show ?thesis using induced_subgraphI'[of H G]
    by (auto simp: induced_imp_subgraph induced_subgraph_def induce_subgraph_def simp: subgraphI)
qed

subsection \<open>Maximal subgraphs\<close>

lemma max_subgraph_mp:
  assumes "max_subgraph G Q x" "\<And>x. P x \<Longrightarrow> Q x" "P x" shows "max_subgraph G P x"
  using assms by (auto simp: max_subgraph_def)

lemma max_subgraph_prop: "max_subgraph G P x \<Longrightarrow> P x"
  by (simp add: max_subgraph_def)

lemma max_subgraph_subg_eq:
  assumes "max_subgraph G P H1" "max_subgraph G P H2" "subgraph H1 H2"
  shows "H1 = H2"
  using assms by (auto simp: max_subgraph_def)

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
  "induced_subgraph H G \<longleftrightarrow> max_subgraph G (\<lambda>H'. dVs H' = dVs H) H" (is "?L \<longleftrightarrow> ?R")
  by (auto intro!: induced_subgraphI_arc_mono simp: arc_mono_def max_subgraph_def induced_imp_subgraph
        dest: subgraph_induced_subgraph_neq)

lemma max_subgraphI:
  assumes "P x" "subgraph x G" "\<And>y. \<lbrakk>x \<noteq> y; subgraph x y; subgraph y G\<rbrakk> \<Longrightarrow> \<not>P y"
  shows "max_subgraph G P x"
  using assms by (auto simp: max_subgraph_def)

lemma subgraphI_max_subgraph: "max_subgraph G P x \<Longrightarrow> subgraph x G"
  by (simp add: max_subgraph_def)

subsection \<open>Connected and strongly connected components\<close>

lemma in_sccs_dVs_conv_reachable:
  "S \<in> sccs_dVs G \<longleftrightarrow> S \<noteq> {} \<and> (\<forall>u \<in> S. \<forall>v \<in> S. u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v) \<and> (\<forall>u \<in> S. \<forall>v. v \<notin> S \<longrightarrow> \<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)"
  by (simp add: sccs_dVs_def)


lemma sccs_dVs_disjoint:
  assumes "S \<in> sccs_dVs G" "T \<in> sccs_dVs G" "S \<noteq> T" shows "S \<inter> T = {}"
  using assms unfolding in_sccs_dVs_conv_reachable by blast

lemma strongly_connected_spanning_imp_strongly_connected:
  assumes "spanning H G"
    and "strongly_connected H"
  shows "strongly_connected G"
  using assms
  unfolding strongly_connected_def
  by (auto elim!: spanningE dest: subgraph_reachable simp: subgraph_def)

lemma strongly_connected_imp_induce_subgraph_strongly_connected:
  assumes subg: "subgraph H G"
    and sc: "strongly_connected H"
  shows "strongly_connected (G \<restriction> dVs H)"
  by (auto intro: strongly_connected_spanning_imp_strongly_connected[of H "G \<restriction> dVs H"] 
           simp: sc spanning_def subg subgraph_induce_subgraphI2)

lemma strongly_connected_reachable:
  assumes "subgraph sc G"
    and "strongly_connected sc"
    and "u \<in> dVs sc" "v \<in> dVs sc"
  shows "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using assms
  unfolding strongly_connected_def
  by (auto dest: subgraph_reachable)

lemma sccs_dVs_restrict_eq: "S \<in> dVs ` sccs G \<Longrightarrow> dVs (G \<restriction> S) = S"
  by (auto dest: induce_subgraph_dVsD induced_subgraphD elim!: in_sccsE)


lemma in_sccs_dVsI_sccs:
  assumes "S \<in> dVs ` sccs G" shows "S \<in> sccs_dVs G"
  unfolding sccs_dVs_def
proof (intro CollectI conjI allI ballI impI)
  show "S \<noteq> {}"
    using assms by fastforce

  from assms have sc: "strongly_connected (G \<restriction> S)"
    by (auto simp: sccs_def induced_subgraph_def subgraph_induce_subgraph)

  {
    fix u v
    assume "u \<in> S" "v \<in> S"
    with assms show "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
      by (auto dest!: induced_imp_subgraph strongly_connected_reachable[of _ _ u v])
  next
    fix u v assume A: "u \<in> S" "v \<notin> S"
    then have uneq: "u \<noteq> v" by blast
    { assume "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
      then have "u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v" "v \<rightarrow>\<^sup>+\<^bsub>G\<^esub> u" using uneq by blast+
      then obtain p_uv p_vu where p_uv: "awalk G u p_uv v" "p_uv \<noteq> []" and p_vu: "awalk G v p_vu u" "p_vu \<noteq> []"
        by (auto simp: reachable1_awalk)
      define T where "T = S \<union> set (awalk_verts u p_uv) \<union> set (awalk_verts v p_vu)"
      then have "S \<subseteq> T" by blast
      have "v \<in> T" using p_vu by (auto simp: T_def set_awalk_verts)
      then have "T \<noteq> S" using \<open>v \<notin> S\<close> by auto

      from p_uv p_vu have T_p_uv: "awalk (G \<restriction> T) u p_uv v" and T_p_vu: "awalk (G \<restriction> T) v p_vu u"
        by (auto intro: awalk_induce simp: T_def)

      then have uv_reach: "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> u"
        by (auto simp: reachable_awalk)

      { fix x y assume "x \<in> S" "y \<in> S"
        then have "x \<rightarrow>\<^sup>*\<^bsub>G \<restriction> S\<^esub> y" "y \<rightarrow>\<^sup>*\<^bsub>G \<restriction> S\<^esub> x"
          using assms sc
          by (simp_all add: sccs_dVs_restrict_eq strongly_connected_def)
        then have "x \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> y" "y \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> x"
          using \<open>S \<subseteq> T\<close> by (auto intro: reachable_induce_ss)
      } note A1 = this

      { fix x assume "x \<in> T"
        moreover
        { assume "x \<in> S" then have "x \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v"
            using uv_reach A1 A by (auto intro: reachable_trans)
        } moreover
        { assume "x \<in> set (awalk_verts u p_uv)" then have "x \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v"
            using T_p_uv by (auto intro: awalk_verts_reachable_to)
        } moreover
        { assume "x \<in> set (awalk_verts v p_vu)" then have "x \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v"
            using T_p_vu by (rule_tac reachable_trans)
              (auto simp: uv_reach dest!: awalk_verts_reachable_to)
        } ultimately
        have "x \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v" by (auto simp: T_def)
      } note xv_reach = this

      { fix x assume "x \<in> T"
        moreover
        { assume "x \<in> S" then have "v \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> x"
            using uv_reach A1 A by (auto intro: reachable_trans)
        } moreover
        { assume "x \<in> set (awalk_verts v p_vu)" then have "v \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> x"
            using T_p_vu by (auto intro: awalk_verts_reachable_from)
        } moreover
        { assume "x \<in> set (awalk_verts u p_uv)" then have "v \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> x"
            using T_p_uv uv_reach by (rule_tac reachable_trans[rotated])
              (auto dest!: awalk_verts_reachable_from)
        } ultimately
        have "v \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> x" by (auto simp: T_def)
      } note vx_reach = this

      { fix x y assume "x \<in> T" "y \<in> T" then have "x \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> y"
          using xv_reach vx_reach by (blast intro: reachable_trans)
      }
      then have "strongly_connected (G \<restriction> T)"
        using \<open>S \<noteq> {}\<close> \<open>S \<subseteq> T\<close> T_p_uv uneq 
        by (auto intro!: strongly_connectedI dest: induce_subgraph_dVsD)
      moreover have "induced_subgraph (G \<restriction> T) G"
        by (simp add: induced_induce)
      ultimately
      have "\<exists>T. induced_subgraph (G \<restriction> T) G \<and> strongly_connected (G \<restriction> T) \<and> (G \<restriction> S) \<subset> (G \<restriction> T)"
        using \<open>S \<subseteq> T\<close> \<open>T \<noteq> S\<close> assms A
        by (metis induce_subgraph_mono' psubsetI reachable_in_dVs(2) sccs_dVs_restrict_eq uv_reach(1))
      then have "G \<restriction> S \<notin> sccs G" unfolding sccs_def by blast
      then have "S \<notin> dVs ` sccs G"
        by (metis imageE in_sccs_imp_induced induced_subgraphD)
      then have False using assms by blast
    }
    then show "\<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u" by blast
  }
qed

lemma arc_mono_strongly_connected[intro,simp]: "arc_mono strongly_connected"
  by (auto simp: arc_mono_def strongly_connected_def subgraph_def dest: subgraph_reachable)

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
      by (metis induced_imp_subgraph max_subgraph_def subgraphI)
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
      using a1 a2 by (auto intro: max_subgraphI dest: induced_imp_subgraph)
  } note Y = this
  show ?thesis unfolding sccs_def
    by (auto dest: max_subgraph_prop X intro: induced_subgraphI_arc_mono Y)
qed

locale max_reachable_set =
  fixes S G 
  assumes S_in_sv: "S \<in> sccs_dVs G"
begin

lemma reach_in: "\<And>u v. \<lbrakk>u \<in> S; v \<in> S\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  and not_reach_out: "\<And>u v. \<lbrakk>u \<in> S; v \<notin> S\<rbrakk> \<Longrightarrow> \<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
  and not_empty: "S \<noteq> {}"
  using S_in_sv by (auto simp: sccs_dVs_def)

lemma awalk_induce_subgraph_scc:
  assumes conn: "u \<in> S" "v \<in> S" "awalk G u p v"
  assumes not_singleton: "S \<noteq> {u} \<or> (u,v) \<in> G"
  shows "awalk (G \<restriction> S) u p v"
proof -
  let ?H = "G \<restriction> S"
  have reach:"u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" using conn by (auto simp: reachable_awalk)
  show ?thesis
  proof (cases "set p \<subseteq> G \<restriction> S")
    case True
    with conn reach not_singleton show ?thesis
      unfolding awalk_def
      by (auto intro: in_induce_subgraph_dVsI_reachable in_induce_subgraph_dVsI simp: S_in_sv not_singleton)
  next
    case False
    then obtain a b where "(a,b) \<in> set p" "(a,b) \<notin> (G \<restriction> S)" by auto
    moreover
    then have "a \<notin> S \<or> b \<notin> S" using conn by (auto simp: induce_subgraph_def)
    ultimately
    obtain w where "w \<in> set (awalk_verts u p)" "w \<notin> S" using conn
      by (metis (no_types, lifting) Un_iff awalkE' empty_iff empty_set fst_conv image_eqI prod.sel(2) set_awalk_verts_not_Nil_cas set_map)
    then have "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w" "w \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" using conn
      by (auto intro: awalk_verts_reachable_from awalk_verts_reachable_to)
    moreover
    have "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u" using conn reach_in by blast
    ultimately have "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w" "w \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u" by (auto intro: reachable_trans)
    with \<open>w \<notin> S\<close> conn not_reach_out have False by blast

    then show ?thesis ..
  qed
qed

lemma reachable_induced:
  assumes conn: "u \<in> S" "v \<in> S" "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  assumes not_singleton: "S \<noteq> {u} \<or> (u,v) \<in> G"
  shows "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> S\<^esub> v"
  using assms
  by (auto simp: reachable_awalk dest: awalk_induce_subgraph_scc)

lemma not_singleton_scc_has_edge:
  assumes "u \<in> S"
  assumes not_singleton: "S \<noteq> {u} \<or> (u,u) \<in> G"
  shows "\<exists>v \<in> S. (u,v) \<in> G"
proof (cases "S \<noteq> {u}")
  case True
  then obtain w where "w \<in> S" "w \<noteq> u" using \<open>u \<in> S\<close> by blast
  then have "u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> w"
    using \<open>u \<in> S\<close> reach_in by blast
  then obtain p where "awalk G u p w" "p \<noteq> []" by (auto simp: reachable1_awalk)
  then have "awalk (G \<restriction> S) u p w"
    using \<open>u \<in> S\<close> \<open>w \<in> S\<close> \<open>w \<noteq> u\<close> 
    by (auto intro: awalk_induce_subgraph_scc)
  with \<open>p \<noteq> []\<close> obtain v ps where "p = (u,v)#ps"
    unfolding awalk_def
    by (auto elim: cas.elims)
  then have "(u,v) \<in> G" "v \<in> dVs (G \<restriction> S)"
    using \<open>awalk G u p w\<close> \<open>awalk (G \<restriction> S) u p w\<close>
    by (auto simp: awalk_Cons_iff)
  then show ?thesis by (auto dest: induce_subgraph_dVsD)
next
  case False
  then show ?thesis
    using not_singleton by blast
qed

lemma no_edge_scc_is_singleton: "G \<restriction> S = {} \<Longrightarrow> (\<exists>u. S = {u})"
  unfolding induce_subgraph_def
  using not_empty not_singleton_scc_has_edge
  by blast

lemma strongly_connected:
  assumes "u \<in> S" "S \<noteq> {u} \<or> (u,u) \<in> G"
  shows "strongly_connected (G \<restriction> S)"
  using not_empty assms
  by (auto intro!: strongly_connectedI reach_in reachable_induced 
      dest: no_edge_scc_is_singleton induce_subgraph_dVsD simp: induce_subgraph_not_empty)


lemma dVs_GS_is_S:
  assumes not_singleton: "u \<in> S" "S \<noteq> {u} \<or> (u,u) \<in> G"
  shows "dVs (G \<restriction> S) = S"
  using assms S_in_sv
  by (auto simp: in_sccs_dVs_conv_reachable 
      dest: induce_subgraph_dVsD intro!: reachable_induced reachable_in_dVs)


lemma induced_in_sccs: 
  assumes "u \<in> S" "S \<noteq> {u} \<or> (u,u) \<in> G"
  shows "G \<restriction> S \<in> sccs G"
proof -
  let ?H = "G \<restriction> S"
  have "induced_subgraph ?H G" using induced_induce by blast

  { fix T assume "G \<restriction> S \<subset> G \<restriction> T" "strongly_connected (G \<restriction> T)"
    from \<open>G \<restriction> S \<subset> G \<restriction> T\<close> obtain v where "v \<in> dVs (G \<restriction> T)" "v \<notin> dVs (G \<restriction> S)"
      by (metis induce_subgraph_mono induced_induce induced_subgraphD psubsetE subgraph_def subsetI)
    from not_empty obtain u where "u \<in> dVs (G \<restriction> S)"
      using assms strongly_connected by blast
    then have "u \<in> dVs (G \<restriction> T)" using \<open>G \<restriction> S \<subset> G \<restriction> T\<close>
      using dVs_subset by blast

    from \<open>u \<in> dVs (G \<restriction> S)\<close> \<open>v \<notin> dVs (G \<restriction> S)\<close> assms have "\<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<or> \<not>v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
      by (intro not_reach_out)
         (auto simp: dVs_GS_is_S)
    moreover
    from \<open>strongly_connected _\<close> have "u \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>G \<restriction> T\<^esub> u"
      using \<open>v \<in> dVs (G \<restriction> T)\<close> \<open>u \<in> dVs (G \<restriction> T)\<close> 
      by (auto simp: strongly_connected_def)
    then have "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u"
      by (auto dest: reachable_induce_subgraphD)
    ultimately have False by blast
  } note psuper_not_sc = this

  have "\<not>(\<exists>c'. induced_subgraph c' G \<and> strongly_connected c' \<and> (G \<restriction> S) \<subset> c')"
    by (metis induced_subgraphD psuper_not_sc)
  with not_empty assms show "?H \<in> sccs G" 
    by (auto simp add: assms(2) in_sccsI induced_induce strongly_connected)
qed
end

lemma in_sccs_dVsD_sccs:
  assumes "S \<in> sccs_dVs G"
  assumes "u \<in> S" "S \<noteq> {u} \<or> (u,u) \<in> G"
  shows "G \<restriction> S \<in> sccs G"
proof -
  from assms interpret max_reachable_set by unfold_locales
  show ?thesis using assms by (auto intro: induced_in_sccs)
qed

text \<open>
  This lemma (and those above used to prove it) highlights an inherent restriction of the chosen 
  graph representation with an implicit vertex set. Obviously an SCC might consist of a single
  vertex. When representing the SCCs as sets of vertices this does not pose a problem. On the other
  hand, when considering SCCs as subgraphs the only way a single-vertex SCC is captured is when
  a self-loop exists, i.e.\ as \<^term>\<open>{(u,u)}\<close>.
\<close>
lemma "sccs_dVs G - {{u} |u. (u,u) \<notin> G} = dVs ` sccs G" (is "?L = ?R")
proof
  { fix S assume "S \<in> ?L"
    then have scc: "S \<in> sccs_dVs G" and "((\<forall>u. S \<noteq> {u}) \<or> (\<exists>u. S = {u} \<and> (u,u) \<in> G))"
      by (auto simp: in_sccs_dVs_conv_reachable reachable_in_dVs)
    then have not_singleton: "\<And>u. S \<noteq> {u} \<or> (u,u) \<in> G" by blast

    interpret ms: max_reachable_set S using scc
      by (rule max_reachable_set.intro)

    have "S \<in> ?R" using scc not_singleton ms.not_empty
      by (auto dest!: in_sccs_dVsD_sccs dest: ms.dVs_GS_is_S)
  }
  then show "?L \<subseteq> ?R" by blast
next
  { fix S assume "S \<in> ?R"
    then have "S \<in> ?L"
      by (auto simp add: in_sccs_dVsI_sccs induce_subgraph_singleton_conv dest!: sccs_dVs_restrict_eq)
  }
  then show "?R \<subseteq> ?L" by blast
qed

lemma induced_eq_dVs_imp_eq:
  assumes "induced_subgraph G H"
  assumes "induced_subgraph G' H"
  assumes "dVs G = dVs G'"
  shows "G = G'"
  using assms by (auto simp: induced_subgraph_def)

lemma in_sccs_subset_imp_eq:
  assumes "c \<in> sccs G"
  assumes "d \<in> sccs G"
  assumes "c \<subseteq> d"
  shows "c = d"
  using assms
  by (metis in_sccsE psubsetI)

lemma dVs_union[simp]: "dVs (G \<union> H) = dVs G \<union> dVs H"
  unfolding dVs_def
  by blast

lemma strongly_connected_non_disj:
  assumes sc: "strongly_connected G" "strongly_connected H"
  assumes not_disj: "dVs G \<inter> dVs H \<noteq> {}"
  shows "strongly_connected (G \<union> H)"
proof
  from sc show "G \<union> H \<noteq> {}"
    unfolding strongly_connected_def by simp
next
  let ?x = "G \<union> H"
  fix u v w assume "u \<in> dVs ?x" and "v \<in> dVs ?x"
  obtain w where w_in_both: "w \<in> dVs G" "w \<in> dVs H"
    using not_disj by blast

  have subg: "subgraph G ?x" "subgraph H ?x"
    by auto
  have reach_uw: "u \<rightarrow>\<^sup>*\<^bsub>?x\<^esub> w"
    using \<open>u \<in> dVs ?x\<close> subg w_in_both sc
    by (auto intro: strongly_connected_reachable)
  also have reach_wv: "w \<rightarrow>\<^sup>*\<^bsub>?x\<^esub> v"
    using \<open>v \<in> dVs ?x\<close> subg w_in_both sc
    by (auto intro: strongly_connected_reachable)
  finally show "u \<rightarrow>\<^sup>*\<^bsub>?x\<^esub> v" .
qed

lemma scc_disj:
  assumes scc: "c \<in> sccs G" "d \<in> sccs G"
  assumes "c \<noteq> d"
  shows "dVs c \<inter> dVs d = {}"
proof (rule ccontr)
  assume contr: "\<not>?thesis"

  let ?x = "c \<union> d"

  have sc: "strongly_connected c" "strongly_connected d"
    using scc by auto

  have union_conn: "strongly_connected ?x"
    using sc contr by (rule strongly_connected_non_disj)

  have sg: "subgraph ?x G"
    using scc by (auto dest!: in_sccs_imp_induced induced_imp_subgraph simp: subgraph_def)
  then have v_cd: "dVs c \<subseteq> dVs G" "dVs d \<subseteq> dVs G" by (auto dest!: subgraph_dVs)

  with v_cd sg union_conn
  have induce_subgraph_conn: "strongly_connected (G \<restriction> dVs ?x)"
    "induced_subgraph (G \<restriction> dVs ?x) G"
    by (intro strongly_connected_imp_induce_subgraph_strongly_connected)
      (auto simp: induced_induce)

  from assms in_sccs_subset_imp_eq have "\<not>c \<subseteq> d" and "\<not>d \<subseteq>  c"
    by auto
  then have psub: "c \<subset> ?x"
    by auto
  then show False using induce_subgraph_conn scc sg
    by (metis \<open>\<not> c \<subseteq> d\<close> in_sccsE le_sup_iff psubsetI subgraphD subgraph_induce_subgraphI2)
qed


lemma in_scc_of_self: "u \<in> dVs G \<Longrightarrow> u \<in> scc_of G u"
  by (auto simp: scc_of_def)

lemma scc_of_empty_conv: "scc_of G u = {} \<longleftrightarrow> u \<notin> dVs G"
  by (auto simp: scc_of_def reachable_in_dVs)

lemma scc_of_in_sccs_dVs:
  assumes "u \<in> dVs G" shows "scc_of G u \<in> sccs_dVs G"
  using assms by (auto simp: in_sccs_dVs_conv_reachable scc_of_def intro: reachable_trans)

lemma sccs_dVs_conv_scc_of:
  "sccs_dVs G = scc_of G ` dVs G" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix S assume "S \<in> ?R" then show "S \<in> ?L"
    by (auto dest: scc_of_in_sccs_dVs)
next
  fix S assume "S \<in> ?L"
  moreover
  then obtain u where "u \<in> S" by (auto simp: in_sccs_dVs_conv_reachable)
  moreover
  then have "u \<in> dVs G" using \<open>S \<in> ?L\<close>
    using sccs_dVs_subset_dVs by blast
  then have "scc_of G u \<in> sccs_dVs G" "u \<in> scc_of G u"
    by (auto intro: scc_of_in_sccs_dVs in_scc_of_self)
  ultimately
  have "scc_of G u = S" using sccs_dVs_disjoint by blast
  then show "S \<in> ?R" using \<open>scc_of G u \<in> _\<close> \<open>u \<in> dVs G\<close> by auto
qed

lemma scc_of_eq: "u \<in> scc_of G v \<Longrightarrow> scc_of G u = scc_of G v"
  by (auto simp: scc_of_def intro: reachable_trans)

lemma strongly_connected_eq_iff:
  "strongly_connected G \<longleftrightarrow> sccs G = {G}" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then have "G \<in> sccs G" 
    by (auto simp: sccs_def induced_subgraph_refl subgraph_dVs' dest: induced_imp_subgraph)
  moreover
  { fix H assume "H \<in> sccs G" "G \<noteq> H"
    with \<open>G \<in> sccs G\<close> have "dVs G \<inter> dVs H = {}" by (rule scc_disj)
    moreover
    from \<open>H \<in> sccs G\<close> have "dVs H \<subseteq> dVs G" by (auto simp: sccs_def dest: induced_imp_subgraph)
    ultimately
    have "dVs H = {}" by auto
    with \<open>H \<in> sccs G\<close> have False by (auto simp: sccs_def)
  } ultimately
  show ?R by auto
qed (auto simp: sccs_def)

end