theory DDFS
  imports Main
begin

text \<open>Theory about digraphs\<close>

definition "dVs dG \<equiv> \<Union> {{v1,v2} | v1 v2. (v1, v2) \<in> dG}"

inductive dpath where
  dpath0: "dpath dG []" |
  dpath1: "v \<in> dVs dG \<Longrightarrow> dpath dG [v]" |
  dpath2: "(v,v') \<in> dG \<Longrightarrow> dpath dG (v'#vs) \<Longrightarrow> dpath dG (v#v'#vs)"

declare dpath0[simp]

inductive_simps dpath_1[simp]: "dpath E [v]"

inductive_simps dpath_2[simp]: "dpath E (v # v' # vs)"

abbreviation "dpath_bet dG p \<equiv> \<lambda>v v'. dpath dG p \<and> p \<noteq> [] \<and> hd p = v \<and> last p = v'"

lemma path_then_edge: "dpath_bet dG p v v' \<Longrightarrow> p \<noteq> [] \<Longrightarrow> v \<noteq> v' \<Longrightarrow> (\<exists>v''. (v, v'') \<in> dG)"
  by(cases p; auto split: if_splits simp: neq_Nil_conv)

lemma path_then_in_Vs: "dpath dG p \<Longrightarrow> v \<in> set p \<Longrightarrow> v \<in> dVs dG"
  by(induction rule: dpath.induct) (auto simp: dVs_def)

lemma dpath_cons: "dpath dG (v1#v2#p) \<Longrightarrow> (v1,v2) \<in> dG"
  by simp

lemma hd_of_dpath_bet:
  "dpath_bet dG p v v' \<Longrightarrow> p \<noteq> [] \<Longrightarrow> \<exists>p'. p = v # p'"
  by(auto simp: neq_Nil_conv)

lemma hd_of_dpath_bet': 
  "dpath_bet dG p v v' \<Longrightarrow> p \<noteq> [] \<Longrightarrow> v = hd p"
  by(auto simp: neq_Nil_conv)

lemma last_of_dpath_bet: 
  "dpath_bet dG p v v' \<Longrightarrow> p \<noteq> [] \<Longrightarrow> v' = last p"
  by(auto simp: neq_Nil_conv)

lemma induct_pcpl:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y zs. P zs \<Longrightarrow> P (x # y # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma induct_pcpl_2:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y. P [x,y]; \<And>x y z. P [x,y,z]; \<And>w x y z zs. P zs \<Longrightarrow> P (w # x # y # z # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma dVsI1:
assumes "(a, v) \<in> dG" shows "a \<in> dVs dG"
using assms unfolding dVs_def by auto

lemma append_dpath_1: "dpath dG (p1 @ p2) \<Longrightarrow> dpath dG p1"
  by (induction p1) (fastforce intro: dpath.intros elim: dpath.cases simp: dVsI1)+

lemma append_dpath_pref: "dpath dG (p1 @ p2) \<Longrightarrow> dpath dG p1"
  by (induction p1) (fastforce intro: dpath.intros elim: dpath.cases simp: dVsI1)+

lemma append_dpath_suff: "dpath dG (p1 @ p2) \<Longrightarrow> dpath dG p2"
  by (induction p1) (fastforce intro: dpath.intros elim: dpath.cases simp:)+

lemma append_dpath: "dpath dG p1 \<Longrightarrow> dpath dG p2 \<Longrightarrow> (last p1, hd p2) \<in> dG \<Longrightarrow> dpath dG (p1 @ p2)"
  by (induction p1) (fastforce intro: dpath.intros elim: dpath.cases simp: dVsI1)+

lemma split_dpath:
  "dpath_bet dG (p1 @ v2 # p2) v1 v3 \<Longrightarrow> dpath_bet dG (v2 # p2) v2 v3"
proof (induction p1)
  case (Cons v p1)
  then show ?case 
    by (auto intro: append_dpath_suff[where ?p1.0 = "v1 # p1"] simp add: path_then_in_Vs)
qed auto

lemma dpath_bet_cons:
  "dpath_bet dG (v # p) v u \<Longrightarrow> p \<noteq> [] \<Longrightarrow> dpath_bet dG p (hd p) u"
  by(auto simp: neq_Nil_conv)

lemma dpath_bet_cons_2: 
  "dpath_bet dG p v v' \<Longrightarrow> p \<noteq> [] \<Longrightarrow> dpath_bet dG (v # tl p) v v'"
  by(auto simp: neq_Nil_conv)

lemma dpath_bet_snoc: 
  "dpath_bet dG (p @ [v]) v' v'' \<Longrightarrow> v = v''"
  by(auto simp: neq_Nil_conv)

lemma dpath_bet_dpath:
  "p \<noteq> [] \<Longrightarrow> dpath_bet dG p (hd p) (last p) \<longleftrightarrow> dpath dG p"
  by(auto simp: neq_Nil_conv)

lemma dpath_snoc_edge': "dpath dG (p @ [v]) \<Longrightarrow> (v, v') \<in> dG \<Longrightarrow> dpath dG ((p @ [v]) @ [v'])"
  apply (rule append_dpath)  
  by (auto simp add: dVs_def)

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

end
