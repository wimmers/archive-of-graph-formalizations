theory Berge_Kruskal_Arc_Walk
  imports
    AGF.Berge
    Kruskal.Kruskal
    Adaptors.DDFS_Berge_Adaptor
    Adaptors.Berge_UGraph_Adaptor
begin


definition connected :: "'a set set \<Rightarrow> ('a \<times> 'a) set" where
  "connected F \<equiv> {(u,v). \<exists>p. epath F u p v}"

definition forest :: "'a set set \<Rightarrow> bool" where
  "forest F \<equiv> (\<nexists>u p. decycle F u p)"

lemma connected_eq[simp]: "connected E = uconnected (ugraph_of E)"
  unfolding connected_def uconnected_def
  by auto

lemma connectedempty: "connected {} = {(a,a)|a. True}"
  by (simp add: uconnectedempty ugraph_of_def)

lemma forest_eq[simp]: "forest E = UGraph.forest (ugraph_of E)"
  unfolding forest_def UGraph.forest_def
  by auto

lemma findaugmenting_edge:
  assumes "epath E1 u p v"
    and "\<nexists>p. epath E2 u p v"
shows "\<exists>a b. (a,b) \<notin> connected E2 \<and> {a,b} \<notin> E2 \<and> {a,b} \<in> E1"
  using assms
  by (auto simp: findaugmenting_edge)

lemma forest_mono: "Y \<subseteq> X \<Longrightarrow> forest X \<Longrightarrow> forest Y"
  using forest_mono by auto

lemma forest2_E:
  assumes "(u,v) \<in> connected E"
    and "{u,v} \<notin> E"
    and "u \<noteq> v"
shows "\<not> forest (insert {u,v} E)"
  using assms
  by (auto simp: forrest2_E)

lemma insert_stays_forest_means_not_connected:
  assumes "forest (insert {u,v} E)"
    and "{u,v} \<notin> E"
    and "u \<noteq> v"
shows "\<not> (u,v) \<in> connected E"
  using assms forest2_E by metis

lemma augment_forest_overedges:
  assumes "F \<subseteq> E" "forest F" "{u,v} \<in> E" "(u,v) \<notin> connected F"
    and notsame: "u \<noteq> v"
  shows "forest (insert {u,v} F)"
  using assms
  by (auto simp: augment_forest_overedges dest: ugraph_of_mono)

abbreviation "connected_on E' V \<equiv> connected E' \<inter> (V \<times> V)"

lemma connected_on_eq: "connected_on E' V = uGraph.uconnected_on (ugraph_of E') V"
  by auto

context graph_abs
begin

lemma ugraph_of_uGraph[simp]: "uGraph (ugraph_of E)"
proof (unfold_locales, goal_cases)
  case (1 e)
  then show ?case sorry
next
  case 2
  then show ?case sorry
qed
(* interpretation ugraph_of: uGraph "ugraph_of E"
proof (unfold_locales, goal_cases)
  case (1 e)
  then show ?case 
    unfolding ugraph_of_def 
    using graph 
    by (force dest!: edge_ugraph_ofD)
next
  case 2
  then show ?case
    unfolding ugraph_of_def
    using finite_E
    sorry    
qed *)

lemma vertices_eq: "Vs E = \<Union>(set_uprod ` (ugraph_of E))"
  unfolding ugraph_of_def Vs_def
  using graph
  by (auto dest: edge_ugraph_ofD) fastforce

abbreviation "verts \<equiv> Vs E"
abbreviation "connectedV E' \<equiv> Restr (connected E') verts"

lemma connectedV_eq: "(connectedV E') = (uGraph.uconnectedV (ugraph_of E) (ugraph_of E'))"
  by (simp add: vertices_eq)

lemma connectedV_refl: "E'\<subseteq>E \<Longrightarrow> refl_on verts (connectedV E')"
  by (auto simp: vertices_eq dest: ugraph_of_mono intro!: uGraph.uconnectedV_refl)

lemma connectedV_trans: "trans (connectedV E')"
  by (auto simp: vertices_eq uGraph.uconnectedV_trans)

lemma connectedV_sym: "sym (connectedV E')"
  by (auto simp: vertices_eq uGraph.uconnectedV_sym)

lemma equiv_verts_connected: "equiv verts (connectedV E')"
  by (auto simp: vertices_eq uGraph.equiv_vert_uconnected)

lemma insert_connectedV_per:
  assumes "x \<noteq> y" and inV: "x \<in> verts" "y \<in> verts" and subE: "F\<subseteq>E"
  shows "connectedV (insert {x,y} F) = per_union (connectedV F) x y"
  apply (simp add: vertices_eq)
  apply (rule uGraph.insert_uconnectedV_per)
  using assms apply (auto dest: ugraph_of_mono simp: vertices_eq)
  done

lemma insert_connectedV_per':
  assumes inV: "x \<in> verts" "y \<in> verts" and subE: "F\<subseteq>E"
  shows "connectedV (insert {x,y} F) = per_union (connectedV F) x y"
  apply (simp add: vertices_eq)
  apply (rule uGraph.insert_uconnectedV_per')
  using assms by (auto dest: ugraph_of_mono simp: vertices_eq)

definition subforest :: "'a set set \<Rightarrow> bool" where
  "subforest F \<equiv> forest F \<and> F \<subseteq> E"

sublocale Kruskal_interface E "Vs E" id "\<lambda>a b e. e = {a,b}" subforest connectedV
  unfolding subforest_def
proof (unfold_locales, goal_cases)
  case 1
then show ?case using finite_E
  by simp
next
  case (2 E')
  then show ?case by simp
next
  case 3
  then show ?case apply (auto simp: UGraph.forest_def ugraph_of_def UGraph.decycle_def)
    using UGraph.epath.elims(2) by fastforce
next
  case (4 X Y)
  then show ?case by (auto simp only: forest_mono)
next
  case (5 u v)
  then show ?case by (auto simp: UGraph.uconnected_def ugraph_of_def elim: UGraph.epath.elims)
next
  case (6 E1 E2 u v)
  then have "(u,v) \<in> (connected E1)" and uv: "u \<in> verts" "v \<in> verts"
    by auto
  then obtain p where 1: "epath E1 u p v" unfolding connected_def by auto
  from 6 uv have 2: "\<nexists>p. epath E2 u p v" unfolding connected_def by auto
  from 1 2 have "\<exists>a b. (a, b) \<notin> connected E2 \<and> {a, b} \<notin> E2 \<and> {a, b} \<in> E1" by (rule findaugmenting_edge)
  then show ?case by auto
next
  case (7 F e u v)
  note f = \<open>forest F \<and> F \<subseteq> E\<close>
  note notin = \<open>e \<in> E - F\<close> \<open>e = {u,v}\<close>
  from notin graph have unv: "u \<noteq> v" by fastforce
  show ?case
  proof
    assume a: "forest (insert e F) \<and> insert e F \<subseteq> E"
    have "(u, v) \<notin> connected F" apply (rule insert_stays_forest_means_not_connected)
      using a unv notin by auto
    then show "(u, v) \<notin> connected_on F verts" by auto
  next
    assume a: "(u, v) \<notin> connected_on F verts"
    have "forest (insert {u, v} F)" apply (rule augment_forest_overedges[where E=E])
      using notin a unv f by blast+
    moreover have "insert e F \<subseteq> E"
      using notin f by auto
    ultimately show "forest (insert e F) \<and> insert e F \<subseteq> E" using notin by auto
  qed
next
  case (8 F)
  show ?case by (rule equiv_verts_connected)
next
  case (9 F)
  show ?case by auto
next
  case (10 x y F e)
  then show ?case using insert_connectedV_per' by auto
next
  case (11 x)
  then show ?case using graph by fast
next
  case (12 a b e)
  then show ?case by simp
next
  case (13 a b e)
  then show ?case by (simp add: insert_commute)
next
  case (14 a F e)
  then show ?case using graph by auto
next
  case (15 e)
  then show ?case using graph by auto
next
  case 16
  then show ?case by auto
next
  case 17
  then show ?case using graph by auto
next
  case (18 a b e T)
  then show ?case 
    unfolding connected_def
    apply (auto simp del: edge_iff_edge intro!: exI[where x="[e]"])
    using graph by blast
qed

end

end