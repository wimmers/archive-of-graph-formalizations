theory DDFS
  imports 
    Main
    Graph_Theory.Rtrancl_On
begin

text \<open>Theory about digraphs\<close>

type_synonym 'a dgraph = "('a \<times> 'a) set"

definition "dVs dG \<equiv> \<Union> {{v1,v2} | v1 v2. (v1, v2) \<in> dG}"

context fixes dG :: "'a dgraph" begin
inductive dpath where
  dpath0: "dpath []" |
  dpath1: "v \<in> dVs dG \<Longrightarrow> dpath [v]" |
  dpath2: "(v,v') \<in> dG \<Longrightarrow> dpath (v'#vs) \<Longrightarrow> dpath (v#v'#vs)"
end

declare dpath0[simp]

inductive_simps dpath_1[simp]: "dpath E [v]"

inductive_simps dpath_2[simp]: "dpath E (v # v' # vs)"

definition "dpath_bet dG p v v' \<equiv> dpath dG p \<and> p \<noteq> [] \<and> hd p = v \<and> last p = v'"

lemma path_then_edge: "dpath_bet dG p v v' \<Longrightarrow> v \<noteq> v' \<Longrightarrow> (\<exists>v''. (v, v'') \<in> dG)"
  by(cases p; auto split: if_splits simp: neq_Nil_conv dpath_bet_def)

lemma path_then_in_Vs: "dpath dG p \<Longrightarrow> v \<in> set p \<Longrightarrow> v \<in> dVs dG"
  by(induction rule: dpath.induct) (auto simp: dVs_def)

lemma dpath_cons: "dpath dG (v1#v2#p) \<Longrightarrow> (v1,v2) \<in> dG"
  by simp

lemma hd_of_dpath_bet:
  "dpath_bet dG p v v' \<Longrightarrow> \<exists>p'. p = v # p'"
  by(auto simp: neq_Nil_conv dpath_bet_def)

lemma hd_of_dpath_bet': 
  "dpath_bet dG p v v' \<Longrightarrow> v = hd p"
  by(auto simp: neq_Nil_conv dpath_bet_def)

lemma last_of_dpath_bet: 
  "dpath_bet dG p v v' \<Longrightarrow> v' = last p"
  by(auto simp: neq_Nil_conv dpath_bet_def)

lemma induct_pcpl:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y zs. P zs \<Longrightarrow> P (x # y # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma induct_pcpl_2:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y. P [x,y]; \<And>x y z. P [x,y,z]; \<And>w x y z zs. P zs \<Longrightarrow> P (w # x # y # z # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma dVs_empty[simp]: "dVs {} = {}"
  by (simp add: dVs_def)

lemma dVs_empty_iff[simp]: "dVs E = {} \<longleftrightarrow> E = {}"
  unfolding dVs_def by auto

lemma dVsI:
  assumes "(a, v) \<in> dG" shows "a \<in> dVs dG" and "v \<in> dVs dG"
  using assms unfolding dVs_def by auto

lemma dVsI':
  assumes "e \<in> dG" shows "fst e \<in> dVs dG" and "snd e \<in> dVs dG"
  using assms
  by (auto intro: dVsI[of "fst e" "snd e"])

lemma dVs_union_distr: "dVs (G \<union> H) = dVs G \<union> dVs H"
  unfolding dVs_def by blast

lemma dVs_union_big_distr: "dVs (\<Union>G) = \<Union>(dVs ` G)"
  apply (induction G rule: infinite_finite_induct)
    apply (auto simp: dVs_union_distr)
   apply (smt dVs_def mem_Collect_eq mem_simps(9))
  by (metis Sup_insert UnCI dVs_union_distr mk_disjoint_insert)

lemma append_dpath_1: "dpath dG (p1 @ p2) \<Longrightarrow> dpath dG p1"
  by (induction p1) (fastforce intro: dpath.intros elim: dpath.cases simp: dVsI)+

lemma append_dpath_pref: "dpath dG (p1 @ p2) \<Longrightarrow> dpath dG p1"
  by (induction p1) (fastforce intro: dpath.intros elim: dpath.cases simp: dVsI)+

lemma append_dpath_suff: "dpath dG (p1 @ p2) \<Longrightarrow> dpath dG p2"
  by (induction p1) (fastforce intro: dpath.intros elim: dpath.cases simp:)+

lemma append_dpath: "dpath dG p1 \<Longrightarrow> dpath dG p2 \<Longrightarrow> (p1 \<noteq> [] \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> (last p1, hd p2) \<in> dG) \<Longrightarrow> dpath dG (p1 @ p2)"
  by (induction p1) (fastforce intro: dpath.intros elim: dpath.cases simp: dVsI)+

lemma split_dpath:
  "dpath_bet dG (p1 @ v2 # p2) v1 v3 \<Longrightarrow> dpath_bet dG (v2 # p2) v2 v3"
  unfolding dpath_bet_def
proof (induction p1)
  case (Cons v p1)
  then show ?case 
    by (auto intro: append_dpath_suff[where ?p1.0 = "v1 # p1"] simp add: path_then_in_Vs dpath_bet_def)
qed auto

lemma dpath_bet_cons:
  "dpath_bet dG (v # p) v u \<Longrightarrow> p \<noteq> [] \<Longrightarrow> dpath_bet dG p (hd p) u"
  by(auto simp: neq_Nil_conv dpath_bet_def)

lemma dpath_bet_cons_2: 
  "dpath_bet dG p v v' \<Longrightarrow> p \<noteq> [] \<Longrightarrow> dpath_bet dG (v # tl p) v v'"
  by(auto simp: neq_Nil_conv dpath_bet_def)

lemma dpath_bet_snoc: 
  "dpath_bet dG (p @ [v]) v' v'' \<Longrightarrow> v = v''"
  by(auto simp: neq_Nil_conv dpath_bet_def)

lemma dpath_bet_dpath:
  "p \<noteq> [] \<Longrightarrow> dpath_bet dG p (hd p) (last p) \<longleftrightarrow> dpath dG p"
  by(auto simp: neq_Nil_conv dpath_bet_def)

lemma dpath_snoc_edge': "dpath dG (p @ [v]) \<Longrightarrow> (v, v') \<in> dG \<Longrightarrow> dpath dG ((p @ [v]) @ [v'])"
  by (rule append_dpath) (auto simp add: dVs_def)

lemma dpath_snoc_edge: "dpath dG (p @ [v]) \<Longrightarrow> (v, v') \<in> dG \<Longrightarrow> dpath dG (p @ [v, v'])"
  using dpath_snoc_edge'
  by simp

lemma dpath_snoc_edge_2: "dpath dG (p @ [v, v']) \<Longrightarrow> (v, v') \<in> dG"
  using append_dpath_suff[where ?p2.0 = "[v, v']"]
  by auto

lemma dpath_append_edge: "dpath dG (p1 @ p2) \<Longrightarrow> p1 \<noteq> [] \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> (last p1, hd p2) \<in> dG"
  by (induction p1) (auto simp: path_then_in_Vs neq_Nil_conv)

lemma dpath_transitive_rel:
  assumes "(\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z)" "(\<And>v1 v2. (v1, v2) \<in> dG \<Longrightarrow> R v1 v2)"
  shows "dpath dG (v#vs) \<Longrightarrow> v' \<in> set vs \<Longrightarrow> R v v'"
proof(induction vs arbitrary: v v')
  case (Cons v'' vs)
  hence "R v v''"
    using assms(2)
    by simp
  thus ?case
  proof(cases "v' = v''")
    case False
    thus ?thesis
      apply(intro assms(1)[OF \<open>R v v''\<close>] Cons)
      using Cons.prems
      by auto
  qed simp
qed auto

lemma dpath_transitive_rel': 
  assumes "(\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z)" "(\<And>v1 v2. (v1, v2) \<in> dG \<Longrightarrow> R v1 v2)"
  shows "dpath dG (vs @ [v]) \<Longrightarrow> v' \<in> set vs \<Longrightarrow> R v' v"
proof(induction vs arbitrary: v v' rule: rev_induct)
  case (snoc v'' vs)
  hence "R v'' v"
    by(auto intro: assms dpath_snoc_edge_2)    
  thus ?case
  proof(cases "v' = v''")
    case True
    then show ?thesis 
      by (simp add: \<open>R v'' v\<close>)
  next
    case False
    thus ?thesis
      apply(intro assms(1)[OF _ \<open>R v'' v\<close>] snoc append_dpath_pref[where ?p1.0 = "vs @ [v'']"])
      using snoc(2,3)
      by auto
  qed
qed auto

abbreviation dominates :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<index>_" [100,100] 40) where
  "dominates E u v \<equiv> (u,v) \<in> E"

abbreviation reachable1 :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>+\<index> _" [100,100] 40) where
  "reachable1 E u v \<equiv> (u,v) \<in> E\<^sup>+"

definition reachable :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>*\<index> _" [100,100] 40) where
  "reachable E u v \<equiv> (u,v) \<in> rtrancl_on (dVs E) E"

lemma reachableE[elim]:
  assumes "u \<rightarrow>\<^bsub>E\<^esub> v"
  obtains e where "e \<in> E" "e = (u, v)"
  using assms by auto

lemma reachable_refl[intro!, Pure.intro!, simp]: "v \<in> dVs E \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  unfolding reachable_def by auto

lemma reachable_trans[trans]:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w" shows "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w"
  using assms unfolding reachable_def by (rule rtrancl_on_trans)

lemma reachable_induct[consumes 1, case_names base step]:
  assumes major: "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
    and cases: "u \<in> dVs E \<Longrightarrow> P u"
      "\<And>x y. \<lbrakk>u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> x; x \<rightarrow>\<^bsub>E\<^esub> y; P x\<rbrakk> \<Longrightarrow> P y"
  shows "P v"
  using assms unfolding reachable_def by (rule rtrancl_on_induct)

lemma converse_reachable_induct[consumes 1, case_names base step, induct pred: reachable]:
  assumes major: "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
    and cases: "v \<in> dVs E \<Longrightarrow> P v"
      "\<And>x y. \<lbrakk>x \<rightarrow>\<^bsub>E\<^esub> y; y \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v; P y\<rbrakk> \<Longrightarrow> P x"
    shows "P u"
  using assms unfolding reachable_def by (rule converse_rtrancl_on_induct)

lemma reachable_in_dVs:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  shows "u \<in> dVs E" "v \<in> dVs E"
  using assms by (induct) (simp_all add: dVsI)

lemma reachable1_in_dVs:
  assumes "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v"
  shows "u \<in> dVs E" "v \<in> dVs E"
  using assms by (induct) (simp_all add: dVsI)


lemma reachable1_reachable[intro]:
  "v \<rightarrow>\<^sup>+\<^bsub>E\<^esub> w \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w"
  unfolding reachable_def
  by (auto intro: rtrancl_consistent_rtrancl_on simp: dVsI reachable1_in_dVs)

lemmas reachable1_reachableE[elim] = reachable1_reachable[elim_format]

lemma reachable_neq_reachable1[intro]:
  assumes reach: "v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w"
    and neq: "v \<noteq> w"
  shows "v \<rightarrow>\<^sup>+\<^bsub>E\<^esub> w" 
  using assms
  unfolding reachable_def
  by (auto dest: rtrancl_on_rtranclI rtranclD)

lemmas reachable_neq_reachable1E[elim] = reachable_neq_reachable1[elim_format]

lemma arc_implies_dominates: "e \<in> E \<Longrightarrow> fst e \<rightarrow>\<^bsub>E\<^esub> snd e" by auto

end
