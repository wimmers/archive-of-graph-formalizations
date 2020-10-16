theory Berge_UGraph_Adaptor
  imports
    AGF.Berge
    Kruskal.UGraph
begin

fun epath :: "'a set set \<Rightarrow> 'a \<Rightarrow> ('a set) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "epath E u [] v = (u = v)"
| "epath E u (x#xs) v \<longleftrightarrow> (\<exists>w. u \<noteq> w \<and> {u, w} = x \<and> epath E w xs v) \<and> x \<in> E"

lemma epath_empty:
  assumes "epath {} u p v"
  shows "u = v" and "p = []"
  using assms
  by (auto elim: epath.elims)

definition depath :: "'a set set \<Rightarrow> 'a \<Rightarrow> ('a set) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "depath E u p v \<equiv> epath E u p v \<and> distinct p"

definition decycle :: "'a set set \<Rightarrow> 'a \<Rightarrow> ('a set) list \<Rightarrow> bool" where
  "decycle E u p \<equiv> epath E u p u \<and> length p > 2 \<and> distinct p"

lemma set_uprod_eq_iff: "set_uprod (Upair a b) = set_uprod (Upair c d) \<longleftrightarrow> Upair a b = Upair c d"
  by fastforce

lemma set_uprod_eq_iff': "set_uprod a = set_uprod b \<longleftrightarrow> a = b"
  by (metis set_uprod_eq_iff uprod_exhaust)

lemma distinct_map_set_uprod_iff[simp]: "distinct (map set_uprod p) \<longleftrightarrow> distinct p"
  by (induction p)
     (auto simp: set_uprod_eq_iff')

lemma set_uprod_eqD: "{u, v} = set_uprod a \<Longrightarrow> a = Upair u v"
  using set_uprod_eq_iff' by fastforce


definition ugraph_of :: "'a set set \<Rightarrow> 'a uprod set" where
  "ugraph_of E \<equiv> {Upair u v | u v. {u, v} \<in> E}"

lemma ugraph_of_mono[intro]: "X \<subseteq> Y \<Longrightarrow> ugraph_of X \<subseteq> ugraph_of Y"
  unfolding ugraph_of_def by fast

lemma ugraph_of_insert[simp]: "ugraph_of (insert {u,v} E) = insert (Upair u v) (ugraph_of E)"
  unfolding ugraph_of_def
  by (auto simp: doubleton_eq_iff)

lemma edge_iff_edge[simp]:
  "{u,v} \<in> E \<longleftrightarrow> Upair u v \<in> ugraph_of E"
  unfolding ugraph_of_def by (auto simp: insert_commute)

lemma edge_ugraph_ofD:
  "Upair u v \<in> ugraph_of E \<Longrightarrow> {u,v} \<in> E"
  by simp

lemma edge_iff_edge':
  "set_uprod e \<in> E \<longleftrightarrow> e \<in> ugraph_of E"
  unfolding ugraph_of_def
  by auto (metis edge_iff_edge set_uprod_simps uprod_exhaust)


lemma epath_ugraph_of_epath: "UGraph.epath (ugraph_of E) u p v \<Longrightarrow> epath E u (map set_uprod p) v"
  by (induction p arbitrary: u) auto

lemma epath_epath_ugraph_of: "epath E u (map set_uprod p) v \<Longrightarrow> UGraph.epath (ugraph_of E) u p v"
  by (induction p arbitrary: u)
     (auto simp: edge_iff_edge' dest: set_uprod_eqD)

lemma epathE[elim]:
  assumes "epath E u p v"
  obtains up where "UGraph.epath (ugraph_of E) u up v" "p = map set_uprod up"
  using assms
  apply (induction p arbitrary: u)
  apply auto
  by (metis (no_types, hide_lams) UGraph.epath.simps(2) list.simps(9) set_uprod_simps)

lemma epath_ugraph_ofE[elim]:
  assumes "UGraph.epath (ugraph_of E) u up v"
  obtains p where "epath E u p v" "p = map set_uprod up"
  using assms epath_ugraph_of_epath
  by fast

lemma epath_iff_epath[simp]: "epath E u (map set_uprod p) v \<longleftrightarrow> UGraph.epath (ugraph_of E) u p v"
  by (auto dest: epath_epath_ugraph_of)

lemma no_epath_iff_no_epath: "(\<nexists>p. epath E u p v) \<longleftrightarrow> (\<nexists>p. UGraph.epath (ugraph_of E) u p v)"
  by auto

declare no_epath_iff_no_epath[simplified, simp]


lemma depath_iff_depath[simp]: "depath E u (map set_uprod p) v \<longleftrightarrow> UGraph.depath (ugraph_of E) u p v"
  unfolding depath_def UGraph.depath_def
  by auto

lemma decycle_iff_decycle[simp]: "decycle E u (map set_uprod p) \<longleftrightarrow> UGraph.decycle (ugraph_of E) u p"
  unfolding decycle_def UGraph.decycle_def
  by auto

lemma decycle_UGraph_E[elim]:
  assumes "UGraph.decycle (ugraph_of E) u up"
  obtains p where "decycle E u p" "p = map set_uprod up"
  using assms decycle_iff_decycle by auto

lemma decycleE[elim]:
  assumes "decycle E u p"
  obtains up where "UGraph.decycle (ugraph_of E) u up" "p = map set_uprod up"
  using assms
  unfolding decycle_def UGraph.decycle_def
  by auto

end