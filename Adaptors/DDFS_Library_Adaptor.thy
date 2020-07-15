theory DDFS_Library_Adaptor
  imports
    AGF.DDFS
    Ports.Noschinski_to_DDFS
    Graph_Theory.Graph_Theory
begin

subsection \<open>Digraph to DDFS\<close>
text \<open>lemmas from DDFS to Noschinski\<close>
context pre_digraph
begin

definition "E \<equiv> arcs_ends G"

lemma dominates_iff:
  "u \<rightarrow>\<^bsub>G\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^bsub>E\<^esub> v"
  unfolding E_def by simp

lemma reachable1_iff:
  "u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v"
  unfolding E_def by simp

lemma arc_iff: "u \<rightarrow>\<^bsub>E\<^esub> v \<longleftrightarrow> (\<exists>b \<in> arcs G. tail G b = u \<and> head G b = v)"
  unfolding E_def arcs_ends_def arc_to_ends_def by blast

fun is_arc_for_pair where
  "is_arc_for_pair a (u,v) = (a \<in> arcs G \<and> tail G a = u \<and> head G a = v)"

definition arc_from_ends :: "('a \<times> 'a) \<Rightarrow> 'b" where
  "arc_from_ends uv \<equiv> (SOME a. is_arc_for_pair a uv)"

lemma pair_has_arc: 
  assumes "(u,v) \<in> E"
    shows "is_arc_for_pair (arc_from_ends (u,v)) (u, v)"
proof -
  obtain a where "a \<in> arcs G \<and> tail G a = u \<and> head G a = v" 
    using arc_iff assms by blast
  hence "\<exists>a. is_arc_for_pair a (u, v)" by fastforce
  thus ?thesis unfolding arc_from_ends_def ..
qed

end

context wf_digraph
begin

lemma dVs_subset_verts:
  "v \<in> dVs E \<Longrightarrow> v \<in> verts G"
  unfolding E_def arcs_ends_def dVs_def arc_to_ends_def 
  by auto

text \<open>
  Vertices without an edge are not in \<^term>\<open>dVs E\<close> - hence also not in \<^term>\<open>rtrancl_on (dVs E) E\<close>
  Thus we can only prove the converse direction with an additional assumption.
\<close>
lemma reachable_imp:
  "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  unfolding reachable_def Noschinski_to_DDFS.reachable_def
  by (rule rtrancl_on_mono[of E])
     (auto simp add: dVs_subset_verts dominates_iff)

lemma reachable_imp':
  "u \<in> dVs E \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  unfolding E_def by (cases "u = v"; auto)

lemma reachable_iff:
  "u \<in> dVs E \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using reachable_imp reachable_imp' by blast

lemma cas_imp_map_arc_to_ends_cas: 
  "cas u p v \<Longrightarrow> Noschinski_to_DDFS.cas u (map (arc_to_ends G) p) v"
  by (induction p arbitrary: u)
     (auto simp: arc_to_ends_def)

lemma cas_map_arc_to_ends_imp_cas: 
  "Noschinski_to_DDFS.cas u (map (arc_to_ends G) p) v \<Longrightarrow> cas u p v"
  by (induction p arbitrary: u)
     (auto simp: arc_to_ends_def)

lemma cas_iff_cas: "Noschinski_to_DDFS.cas u (map (arc_to_ends G) p) v \<longleftrightarrow> cas u p v"
  using cas_imp_map_arc_to_ends_cas cas_map_arc_to_ends_imp_cas by blast

lemma awalk_imp_awalk_map_arc_to_ends:
  assumes "u \<in> dVs E"
  assumes "awalk u p v"
  shows "Noschinski_to_DDFS.awalk E u (map (arc_to_ends G) p) v"
  using assms
  unfolding awalk_def Noschinski_to_DDFS.awalk_def E_def
  by (auto intro: dominatesI cas_imp_map_arc_to_ends_cas)

lemma cas_imp_map_arc_from_ends_cas:
  assumes "set p \<subseteq> E"
  shows "Noschinski_to_DDFS.cas u p v \<Longrightarrow> cas u (map arc_from_ends p) v"
  using assms arc_from_ends_def pair_has_arc
  by (induction p arbitrary: u) auto

lemma cas_map_arc_from_ends_imp_cas:
  assumes "set p \<subseteq> E"
  shows "cas u (map arc_from_ends p) v \<Longrightarrow> Noschinski_to_DDFS.cas u p v"
  using assms arc_from_ends_def pair_has_arc
  by (induction p arbitrary: u) auto

lemma cas_iff_cas':
  assumes "set p \<subseteq> E"
  shows "Noschinski_to_DDFS.cas u p v \<longleftrightarrow> cas u (map arc_from_ends p) v"
  using assms cas_imp_map_arc_from_ends_cas cas_map_arc_from_ends_imp_cas by blast

lemma awalk_imp_awalk_map_arc_from_ends:
  assumes "Noschinski_to_DDFS.awalk E u p v"
  shows "awalk u (map arc_from_ends p) v"
  using assms pair_has_arc cas_imp_map_arc_from_ends_cas
  unfolding Noschinski_to_DDFS.awalk_def awalk_def
  by (auto simp: dVs_subset_verts)

lemma awalk_map_arc_from_ends_imp_awalk:
  assumes "u \<in> dVs E"
  assumes "set p \<subseteq> E"
  assumes "awalk u (map arc_from_ends p) v"
  shows "Noschinski_to_DDFS.awalk E u p v"
  using assms
  unfolding Noschinski_to_DDFS.awalk_def awalk_def
  by (auto simp add: cas_iff_cas')

lemma awalk_iff_awalk:
  assumes "u \<in> dVs E"
  assumes "set p \<subseteq> E"
  shows "awalk u (map arc_from_ends p) v \<longleftrightarrow> Noschinski_to_DDFS.awalk E u p v"
  using assms awalk_imp_awalk_map_arc_from_ends awalk_map_arc_from_ends_imp_awalk by blast


text \<open>
  For this direction, we have to make sure the walk is not empty.
\<close>
lemma dpath_imp_vwalk:
  "dpath E (u # xs) \<Longrightarrow> vwalk (u # xs) G"
  by (induction xs arbitrary: u)
     (auto simp: dVs_subset_verts dominates_iff)

text \<open>
  For this direction, we have to make sure there is at least an arc in the walk.
  Or we could add an assumption \<^term>\<open>u \<in> dVs E\<close>.
\<close>
lemma vwalk_imp_dpath:
  "vwalk (u # v # xs) G \<Longrightarrow> dpath E (u # v # xs)"
  by (induction xs arbitrary: u v)
     (auto simp: dominates_iff dVsI)

lemma vwalk_iff:
  "vwalk (u # v # xs) G \<longleftrightarrow> dpath E (u # v # xs)"
  using vwalk_imp_dpath dpath_imp_vwalk by blast

\<comment> \<open>With no disconnected vertices, a stronger version is possible.\<close>
lemma vwalk_iff':
  assumes "verts G = dVs E"
  shows "vwalk (u # xs) G \<longleftrightarrow> dpath E (u # xs)"
  by (auto simp: dpath_imp_vwalk)
     (induction xs arbitrary: u; auto simp: assms dominates_iff)
  
end

context nomulti_digraph
begin

lemma arc_from_ends_arc_to_ends_eq:
  assumes "a \<in> arcs G"
  shows "arc_from_ends (arc_to_ends G a) = a"
  using assms
  by (intro no_multi_arcs)
     (auto simp: arc_to_ends_def dominates_iff dest!: in_arcs_imp_in_arcs_ends pair_has_arc)

lemma arc_to_ends_arc_from_ends_eq:
  assumes "(u,v) \<in> E"
  shows "arc_to_ends G (arc_from_ends (u,v)) = (u,v)"
  using assms
  by (auto dest!: pair_has_arc simp: arc_to_ends_def)

end


subsection \<open>From DDFS to Digraph\<close>
locale ddfs =
  fixes E :: "('a \<times> 'a) set"
begin

definition "G \<equiv> \<lparr>verts = dVs E, arcs = E, tail = fst, head = snd\<rparr>"
definition "G\<^sub>p = \<lparr>pverts = dVs E, arcs = E\<rparr>"

lemma G_pair_conv:
  "with_proj G\<^sub>p = G"
  unfolding G\<^sub>p_def G_def with_proj_def by simp

sublocale ddfs_digraph: nomulti_digraph G
  by standard (auto simp: G_def arc_to_ends_def dVsI)

sublocale ddfs_pdigraph: pair_wf_digraph G\<^sub>p
  using G_pair_conv ddfs_digraph.wf_digraph_axioms wf_digraph_wp_iff by fastforce

lemma arc_to_ends_eq[simp]:
  "arc_to_ends G = id"
  by (auto simp add: G_def arc_to_ends_def)

lemma arcs_ends_eq[simp]:
  "arcs_ends G = E"
  unfolding arcs_ends_def arc_to_ends_eq by (simp add: G_def)

lemma dominates_iff[simp]:
  "u \<rightarrow>\<^bsub>G\<^esub> v \<longleftrightarrow> (u, v) \<in> E"
  by simp

lemma verts_eq[simp]:
  "verts G = dVs E"
  unfolding G_def by simp

lemma arcs_eq[simp]:
  "arcs G = E"
  unfolding G_def by simp

lemma tail_eq[simp]:
  "tail G = fst"
  unfolding G_def by simp

lemma head_eq[simp]:
  "head G = snd"
  unfolding G_def by simp

lemma reachable_iff:
  "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  unfolding reachable_def Noschinski_to_DDFS.reachable_def
  by simp

lemma reachable1_iff:
  "u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v"
  by simp

lemma cas_conv:
  "cas u (e # es) v = (fst e = u \<and> cas (snd e) es v)"
  by (simp add: cas_simp)

lemma cas_iff:
  "ddfs_digraph.cas u p v \<longleftrightarrow> cas u p v"
  by (induction p arbitrary: u)
     (auto simp add: cas_conv)


lemma awalk_iff:
  "ddfs_digraph.awalk u p v \<longleftrightarrow> awalk E u p v"
  unfolding ddfs_digraph.awalk_def awalk_def
  by (auto simp: cas_iff)

lemma vwalk_iff:
  "vwalk p G \<longleftrightarrow> p \<noteq> [] \<and> dpath E p"
  by (induction p rule: induct_list012) auto

  

end
end