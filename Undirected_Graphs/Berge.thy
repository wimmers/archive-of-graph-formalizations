(*
  Author: Mohammad Abdulaziz, TUM
*)

theory Berge
imports Main "HOL-Library.Extended_Nat" "HOL-Eisbach.Eisbach_Tools"
begin

subsection\<open>Paths, connected components, and symmetric differences\<close>

text\<open>Some basic definitions about the above concepts. One interesting point is the use of the
     concepts of connected components, which partition the set of vertices, and the analogous
     partition of edges. Juggling around between the two partitions, we get a much shorter proof for
     the first direction of Berge's lemma, which is the harder one.\<close>

definition Vs where "Vs E \<equiv> \<Union> E"

lemma vs_member[iff?]: "v \<in> Vs E \<longleftrightarrow> (\<exists>e \<in> E. v \<in> e)"
  unfolding Vs_def by simp

lemma vs_member_elim[elim?]:
  assumes "v \<in> Vs E"
  obtains e where "v \<in> e" "e \<in> E"
  using assms
  by(auto simp: vs_member)

lemma vs_member_intro[intro]:
  "\<lbrakk>v \<in> e; e \<in> E\<rbrakk> \<Longrightarrow> v \<in> Vs E"
  using vs_member
  by force

lemma vs_transport:
  "\<lbrakk>u \<in> Vs E; \<And>e. \<lbrakk>u \<in> e; e \<in> E\<rbrakk> \<Longrightarrow> \<exists>g \<in> F. u \<in> g\<rbrakk> \<Longrightarrow>u \<in> Vs F"
  by (auto simp: vs_member)

lemma edges_are_Vs:
  assumes "{v, v'} \<in> E"
  shows "v \<in> Vs E"
  using assms by blast

locale graph_defs =
  fixes E :: "'a set set"

abbreviation "graph_invar E \<equiv> (\<forall>e\<in>E. \<exists>u v. e = {u, v} \<and> u \<noteq> v) \<and> finite (Vs E)"

locale graph_abs =
  graph_defs +
  assumes graph: "graph_invar E"
begin

lemma finite_E: "finite E"
  using finite_UnionD graph
  unfolding Vs_def
  by blast

end

context fixes X :: "'a set set" begin
inductive path where
  path0: "path []" |
  path1: "v \<in> Vs X \<Longrightarrow> path [v]" |
  path2: "{v,v'} \<in> X \<Longrightarrow> path (v'#vs) \<Longrightarrow> path (v#v'#vs)"
end

declare path0

inductive_simps path_1: "path X [v]"

inductive_simps path_2: "path X (v # v' # vs)"

lemmas path_simps[simp] = path0 path_1 path_2


text\<open>
  If a set of edges cannot be partitioned in paths, then it has a junction of 3 or more edges.
  In particular, an edge from one of the two matchings belongs to the path
  equivalent to one connected component. Otherwise, there will be a vertex whose degree is
  more than 2.
\<close>


text\<open>
  Every edge lies completely in a connected component.
\<close>

fun edges_of_path where
"edges_of_path [] = []" |
"edges_of_path [v] = []" |
"edges_of_path (v#v'#l) = {v,v'} # (edges_of_path (v'#l))"

lemma path_ball_edges: "path E p \<Longrightarrow> b \<in> set (edges_of_path p) \<Longrightarrow> b \<in> E"
  by (induction p rule: edges_of_path.induct, auto)

lemma edges_of_path_index:
  "Suc i < length p \<Longrightarrow> edges_of_path p ! i = {p ! i, p ! Suc i}"
proof(induction i arbitrary: p)
  case 0
  then obtain u v ps where "p = u#v#ps" 
    by (auto simp: less_eq_Suc_le Suc_le_length_iff)
  thus ?case by simp
next
  case (Suc i)
  then obtain u v ps where "p = u#v#ps"
    by (auto simp: less_eq_Suc_le Suc_le_length_iff)
  hence "edges_of_path (v#ps) ! i = {(v#ps) ! i, (v#ps) ! Suc i}"
    using Suc.IH Suc.prems
    by simp
  thus ?case using \<open>p = u#v#ps\<close>
    by simp
qed

lemma edges_of_path_length: "length (edges_of_path p) = length p - 1"
  by (induction p rule: edges_of_path.induct, auto)

lemma edges_of_path_length': "p \<noteq> [] \<Longrightarrow> length p = length (edges_of_path p) + 1"
  by (induction p rule: edges_of_path.induct, auto)

lemma edges_of_path_for_inner:
  assumes "v = p ! i" "Suc i < length p"
  obtains u w where "{u, v} = edges_of_path p ! (i - 1)" "{v, w} = edges_of_path p ! i"
proof(cases "i = 0")
  case True thus ?thesis 
    using assms(1) edges_of_path_index[OF assms(2)] that
    by auto
next
  case False thus ?thesis
    by (auto simp add: Suc_lessD assms edges_of_path_index that)
qed

lemma path_vertex_has_edge:
  assumes "length p \<ge> 2" "v \<in> set p"
  obtains e where "e \<in> set (edges_of_path p)" "v \<in> e"
proof-
  have "\<exists>e \<in> set (edges_of_path p). v \<in> e"
    using assms Suc_le_eq 
    by (induction p rule: edges_of_path.induct) fastforce+
  thus ?thesis
    using that
    by rule
qed

lemma v_in_edge_in_path:
  assumes "{u, v} \<in> set (edges_of_path p)"
  shows "u \<in> set p"
  using assms
  by (induction p rule: edges_of_path.induct) auto

lemma v_in_edge_in_path_inj:
  assumes "e \<in> set (edges_of_path p)"
  obtains u v where "e = {u, v}"
  using assms
  by (induction p rule: edges_of_path.induct) auto

lemma v_in_edge_in_path_gen:
  assumes "e \<in> set (edges_of_path p)" "u \<in> e"
  shows "u \<in> set p"
proof-
  obtain u v where "e = {u, v}"
    using assms(1) v_in_edge_in_path_inj
    by blast
  thus ?thesis
    using assms
    by (force simp add: insert_commute intro: v_in_edge_in_path)
qed

lemma distinct_edges_of_vpath:
  "distinct p \<Longrightarrow> distinct (edges_of_path p)"
  using v_in_edge_in_path
  by (induction p rule: edges_of_path.induct) fastforce+

lemma distinct_edges_of_paths_cons:
  assumes "distinct (edges_of_path (v # p))"
  shows "distinct (edges_of_path p)"
  using assms
  by(cases "p"; simp)

lemma hd_edges_neq_last:
  assumes "{hd p, last p} \<notin> set (edges_of_path p)" "hd p \<noteq> last p" "p \<noteq> []"
  shows "hd (edges_of_path (last p # p)) \<noteq> last (edges_of_path (last p # p))"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons)
  then show ?case
    apply (auto split: if_splits)
    using edges_of_path.elims apply blast
    by (simp add: insert_commute)
qed

lemma edges_of_path_append_2:
  assumes "p' \<noteq> []"
  shows "edges_of_path (p @ p') = edges_of_path (p @ [hd p']) @ edges_of_path p'"
  using assms
proof(induction p rule: induct_list012)
  case 2
  obtain a p's where "p' = a # p's" using assms list.exhaust_sel by blast
  thus ?case by simp
qed simp_all

lemma edges_of_path_append_3:
  assumes "p \<noteq> []"
  shows "edges_of_path (p @ p') = edges_of_path p @ edges_of_path (last p # p')"
proof-
  have "edges_of_path (p @ p') = edges_of_path (butlast p @ last p # p')"
    by (subst append_butlast_last_id[symmetric, OF assms], subst append.assoc, simp)
  also have "... = edges_of_path (butlast p @ [last p]) @ edges_of_path (last p # p')"
    using edges_of_path_append_2
    by fastforce
  also have "... = edges_of_path p @ edges_of_path (last p # p')"
    by (simp add: assms)
  finally show ?thesis .
qed

lemma edges_of_path_rev:
  shows "rev (edges_of_path p) = edges_of_path (rev p)"
proof(induction p rule: edges_of_path.induct)
  case (3 v v' l)
  moreover have "edges_of_path (rev l @ [v', v]) = 
                   edges_of_path (rev l @ [v']) @ edges_of_path [v', v]"
    apply(subst edges_of_path_append_2)
    by auto
  ultimately show ?case
    by auto
qed auto

lemma edges_of_path_append: "\<exists>ep. edges_of_path (p @ p') = ep @ edges_of_path p'"
proof(cases p')
  case Nil thus ?thesis by simp
next
  case Cons thus ?thesis using edges_of_path_append_2 by blast
qed

lemma last_v_in_last_e: 
  "length p \<ge> 2 \<Longrightarrow> last p \<in> last (edges_of_path p)"
  by (induction "p" rule: induct_list012) (auto elim: edges_of_path.elims simp add: Suc_leI)

lemma hd_v_in_hd_e: 
  "length p \<ge> 2 \<Longrightarrow> hd p \<in> hd (edges_of_path p)"
  by (auto simp: Suc_le_length_iff numeral_2_eq_2)

lemma last_in_edge:
  assumes "p \<noteq> []"
  shows "\<exists>u. {u, last p} \<in> set (edges_of_path (v # p)) \<and> u \<in> set (v # p)"
  using assms
proof(induction "length p" arbitrary: v p)
  case (Suc x)
  thus ?case
  proof(cases p)
    case p: (Cons _ p')
    thus ?thesis
    proof(cases "p' = []")
      case False
      then show ?thesis
        using Suc
        by(auto simp add: p)
    qed auto
  qed auto
qed simp

find_theorems edges_of_path "(@)"

lemma edges_of_path_append_subset:
  "set (edges_of_path p') \<subseteq> set (edges_of_path (p @ p'))"
proof(cases p')
  case (Cons a list)
  then show ?thesis
    apply(subst edges_of_path_append_2)
    by auto
qed auto

lemma path_edges_subset:
  assumes "path E p"
  shows "set (edges_of_path p) \<subseteq> E"
  using assms
  by (induction, simp_all)

lemma induct_list012[case_names nil single sucsuc]:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y zs. \<lbrakk> P zs; P (y # zs) \<rbrakk> \<Longrightarrow> P (x # y # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma induct_list0123[consumes 0, case_names nil list1 list2 list3]:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y. P [x, y]; 
    \<And>x y z zs. \<lbrakk> P zs; P (z # zs); P (y # z # zs) \<rbrakk> \<Longrightarrow> P (x # y # z # zs)\<rbrakk>
    \<Longrightarrow> P xs"
by induction_schema (pat_completeness, lexicographic_order)

lemma tl_path_is_path: "path E p \<Longrightarrow> path E (tl p)"
  by (induction p rule: path.induct) (simp_all)

lemma path_concat:
  "\<lbrakk>path E p; path E q; q \<noteq> []; p \<noteq> [] \<Longrightarrow> last p = hd q\<rbrakk> \<Longrightarrow> path E (p @ tl q)"
  by (induction rule: path.induct) (simp_all add: tl_path_is_path)

lemma path_append:
  "\<lbrakk>path E p1; path E p2; \<lbrakk>p1 \<noteq> []; p2 \<noteq> []\<rbrakk> \<Longrightarrow> {last p1, hd p2} \<in> E\<rbrakk> \<Longrightarrow> path E (p1 @ p2)"
  by (induction rule: path.induct) (auto simp add: neq_Nil_conv elim: path.cases)

lemma mem_path_Vs: 
  "\<lbrakk>path E p; a\<in>set p\<rbrakk> \<Longrightarrow> a \<in> Vs E"
  by (induction rule: path.induct) (simp; blast)+

lemma subset_path_Vs: 
  "\<lbrakk>path E p\<rbrakk> \<Longrightarrow> set p \<subseteq> Vs E"
  by (induction rule: path.induct) (simp; blast)+

lemma path_suff:
  assumes "path E (p1 @ p2)"
  shows "path E p2"
  using assms
proof(induction p1)
  case (Cons a p1)
  then show ?case using Cons tl_path_is_path by force
qed simp

lemma path_pref:
  assumes "path E (p1 @ p2)"
  shows "path E p1"
  using assms
proof(induction p1)
  case (Cons a p1)
  then show ?case using Cons by (cases p1; auto simp add: mem_path_Vs)
qed simp

lemma rev_path_is_path:
  assumes "path E p"
  shows "path E (rev p)"
  using assms
proof(induction)
  case (path2 v v' vs)
  moreover hence "{last (rev vs @ [v']), hd [v]} \<in> E"
    by (simp add: insert_commute)
  ultimately show ?case 
    using path_append edges_are_Vs
    by force
qed simp_all

lemma rev_path_is_path_iff:
  "path E p \<longleftrightarrow> path E (rev p)"
  using rev_path_is_path
  by force

lemma Vs_subset:
  "E \<subseteq> E' \<Longrightarrow> Vs E \<subseteq> Vs E'"
  by (auto simp: Vs_def)

lemma path_subset:
  assumes "path E p" "E \<subseteq> E'"
  shows "path E' p"
  using assms Vs_subset
  by (induction, auto)

lemma path_edges_of_path_refl: "length p \<ge> 2 \<Longrightarrow> path (set (edges_of_path p)) p"
proof (induction p rule: edges_of_path.induct)
  case (3 v v' l)
  thus ?case
    apply (cases l)
    by (auto intro: path_subset simp add: edges_are_Vs insert_commute path2)
qed simp_all

lemma edges_of_path_Vs: "Vs (set (edges_of_path p)) \<subseteq> set p"
  by (auto elim: vs_member_elim intro: v_in_edge_in_path_gen)

subsection \<open>walks, and connected components\<close>

definition "walk_betw E u p v \<equiv> (p \<noteq> [] \<and> path E p \<and> hd p = u \<and> last p = v)"

lemma nonempty_path_walk_between:
  "\<lbrakk>path E p; p \<noteq> []; hd p = u; last p = v\<rbrakk> \<Longrightarrow> walk_betw E u p v"
  by (simp add: walk_betw_def)

lemma nonempty_path_walk_betweenE:
  assumes "path E p" "p \<noteq> []" "hd p = u" "last p = v"
  obtains p where "walk_betw E u p v"
  using assms
  by (simp add: walk_betw_def)

lemma walk_nonempty:
  assumes "walk_betw E u p v"
  shows [simp]: "p \<noteq> []"
  using assms walk_betw_def by fastforce

lemma walk_between_nonempty_pathD:
  assumes "walk_betw E u p v"
  shows "path E p" "p \<noteq> []" "hd p = u" "last p = v"
  using assms unfolding walk_betw_def by simp_all

lemma walk_reflexive:
  "w \<in> Vs E \<Longrightarrow> walk_betw E w [w] w"
  by (simp add: nonempty_path_walk_between)

lemma walk_symmetric:
  "walk_betw E u p v \<Longrightarrow> walk_betw E v (rev p) u"
  by (auto simp add: hd_rev last_rev walk_betw_def intro: rev_path_is_path)

lemma walk_transitive:
   "\<lbrakk>walk_betw E u p v; walk_betw E v q w\<rbrakk> \<Longrightarrow> walk_betw E u (p @ tl q) w"
  by (auto simp add: walk_betw_def intro: path_concat elim: path.cases)

lemma walk_transitive_2:
  "\<lbrakk>walk_betw E v q w; walk_betw E u p v\<rbrakk> \<Longrightarrow> walk_betw E u (p @ tl q) w"
  by (auto simp add: walk_betw_def intro: path_concat elim: path.cases)

lemma walk_in_Vs:
  "walk_betw E a p b \<Longrightarrow> set p \<subseteq> Vs E"
  by (simp add: subset_path_Vs walk_betw_def)

lemma walk_endpoints:
  assumes "walk_betw E u p v"
  shows [simp]: "u \<in> Vs E"
  and   [simp]: "v \<in> Vs E"
  using assms mem_path_Vs walk_betw_def
  by fastforce+

lemma walk_pref:
  "walk_betw E u (pr @ [x] @ su) v \<Longrightarrow> walk_betw E u (pr @ [x]) x"
proof(rule nonempty_path_walk_between, goal_cases)
  case 1
  hence "walk_betw E u ((pr @ [x]) @ su) v"
    by auto
  thus ?case
    by (fastforce dest!: walk_between_nonempty_pathD(1) path_pref)
next
  case 3
  then show ?case
    by(cases pr) (auto simp: walk_betw_def)
qed auto

lemma walk_suff:
   "walk_betw E u (pr @ [x] @ su) v \<Longrightarrow> walk_betw E x (x # su) v"
  by (fastforce simp: path_suff walk_betw_def)

lemma edges_are_walks:
  "{v, w} \<in> E \<Longrightarrow> walk_betw E v [v, w] w"
  using edges_are_Vs insert_commute
  by (auto 4 3 intro!: nonempty_path_walk_between)

lemma walk_subset:
  "\<lbrakk>walk_betw E u p v; E \<subseteq> E'\<rbrakk> \<Longrightarrow> walk_betw E' u p v"
  using path_subset
  by (auto simp: walk_betw_def)

lemma induct_walk_betw[case_names path1 path2, consumes 1, induct set: walk_betw]:
  assumes "walk_betw E a p b"
  assumes Path1: "\<And>v. v \<in> Vs E \<Longrightarrow> P v [v] v"
  assumes Path2: "\<And>v v' vs b. {v, v'} \<in> E \<Longrightarrow> walk_betw E v' (v' # vs) b \<Longrightarrow> P v' (v' # vs) b \<Longrightarrow> P v (v # v' # vs) b"
  shows "P a p b"
proof-
  have "path E p" "p \<noteq> []" "hd p = a" "last p = b"
    using assms(1)
    by (auto dest: walk_between_nonempty_pathD)
  thus ?thesis
    by (induction arbitrary: a b rule: path.induct) (auto simp: nonempty_path_walk_between assms(2,3))
qed

definition reachable where
  "reachable E u v = (\<exists>p. walk_betw E u p v)"

lemma reachableE:
  "reachable E u v \<Longrightarrow> (\<And>p. p \<noteq> [] \<Longrightarrow> walk_betw E u p v \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: reachable_def)

lemma reachableD:
  "reachable E u v \<Longrightarrow> \<exists>p. walk_betw E u p v"
  by (auto simp: reachable_def)

lemma reachableI:
  "walk_betw E u p v \<Longrightarrow> reachable E u v"
  by (auto simp: reachable_def)

lemma reachable_trans:
  "\<lbrakk>reachable E u v; reachable E v w\<rbrakk> \<Longrightarrow> reachable E u w"
  apply(erule reachableE)+
  apply (drule walk_transitive)
   apply assumption
  by (rule reachableI)

lemma reachable_sym:
  "reachable E u v \<longleftrightarrow> reachable E v u"
  by(auto simp add: reachable_def dest: walk_symmetric)

lemma reachable_refl:
  "u \<in> Vs E \<Longrightarrow> reachable E u u"
  by(auto simp add: reachable_def dest: walk_reflexive)

definition connected_component where
  "connected_component E v = {v'. v' = v \<or> reachable E v v'}"

text \<open>This is an easier to reason about characterisation, especially with automation\<close>

lemma connected_component_rechability:
  "connected_component E v = {v'. v' = v \<or> (reachable E v v')}"
  by (auto simp add: reachable_def connected_component_def)

definition connected_components where
  "connected_components E \<equiv> {vs. \<exists>v. vs = connected_component E v \<and> v \<in> (Vs E)}"

lemma in_own_connected_component: "v \<in> connected_component E v"
  unfolding connected_component_def by simp

lemma in_connected_componentE:
  "\<lbrakk>v \<in> connected_component E w; \<lbrakk>reachable E w v; w \<in> Vs E\<rbrakk> \<Longrightarrow> P; w = v \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: connected_component_def reachable_refl elim: reachableE dest: walk_endpoints(1))

lemma in_connected_component_has_walk:
  assumes "v \<in> connected_component E w" "w \<in> Vs E"
  obtains p where "walk_betw E w p v"
proof(cases "v = w")
  case True thus ?thesis
   using that assms(2)
   by (auto dest: walk_reflexive )
next
  case False
  hence "reachable E w v"
    using assms(1) unfolding connected_component_def by blast
  thus ?thesis
    by (auto dest: reachableD that)
qed

(* TODO: Call in_connected_componentI *)

lemma has_path_in_connected_component:
  "walk_betw E u p v \<Longrightarrow> v \<in> connected_component E u"
  by(auto simp: connected_component_def reachable_def)

lemma in_connected_componentI:
  "reachable E w v \<Longrightarrow> v \<in> connected_component E w"
  by (auto simp: connected_component_rechability)

lemma in_connected_componentI2:
  "w = v \<Longrightarrow> v \<in> connected_component E w"
  by (auto simp: connected_component_rechability)

lemma edges_reachable:
  "{v, w} \<in> E \<Longrightarrow> reachable E v w"
  by (auto intro: edges_are_walks reachableI)

(* TODO: Call in_connected_componentI2 *)

lemma has_path_in_connected_component2:
  "(\<exists>p. walk_betw E u p v) \<Longrightarrow> v \<in> connected_component E u"
  unfolding connected_component_def reachable_def
  by blast

lemma connected_components_notE_singletons:
  "x \<notin> Vs E \<Longrightarrow> connected_component E x = {x}"
  by (fastforce simp add: connected_component_def reachable_def)

lemma connected_components_member_sym:
  "v \<in> connected_component E w \<Longrightarrow> w \<in> connected_component E v"
  by (auto elim!: in_connected_componentE intro: in_connected_componentI in_connected_componentI2
           simp: reachable_sym)

lemma connected_components_member_trans:
  "\<lbrakk>x \<in> connected_component E y; y \<in> connected_component E z\<rbrakk> \<Longrightarrow> x \<in> connected_component E z"
  by (auto elim!: in_connected_componentE dest: reachable_trans intro: in_connected_componentI
           simp: reachable_refl)

method in_tc uses tc_thm = 
  (match conclusion in "R x z" for R and x::'a and z::'a \<Rightarrow>
     \<open>match premises in a: "R x y" for  y \<Rightarrow>
       \<open>match premises in b: "R y z" \<Rightarrow>
          \<open>(insert tc_thm[OF a b])\<close>\<close>\<close>)

method in_tc_2 uses tc_thm refl_thm = 
  (match conclusion in "R x z" for R and x::'a and z::'a \<Rightarrow>
     \<open>match premises in a: "R x y" for  y \<Rightarrow>
       \<open>match premises in b: "R z y" \<Rightarrow>
          \<open>(insert tc_thm[OF a refl_thm[OF b]])\<close>\<close>\<close>)

method in_tc_3 uses tc_thm refl_thm = 
  (match conclusion in "R x z" for R and x::'a and z::'a \<Rightarrow>
     \<open>match premises in b: "R y z" for  y \<Rightarrow>
       \<open>match premises in a: "R y x" \<Rightarrow>
          \<open>(insert tc_thm[OF refl_thm[OF a] b])\<close>\<close>\<close>)

method in_tc_4 uses tc_thm refl_thm = 
  (match conclusion in "R x z" for R and x::'a and z::'a \<Rightarrow>
     \<open>match premises in a: "R y x" for  y \<Rightarrow>
       \<open>match premises in b: "R z y" \<Rightarrow>
          \<open>(insert tc_thm[OF refl_thm[OF a] refl_thm[OF b]])\<close>\<close>\<close>)

method in_rtc uses tc_thm refl_thm =
  (safe?; (in_tc tc_thm: tc_thm | in_tc_2 tc_thm: tc_thm refl_thm: refl_thm |
    in_tc_3 tc_thm: tc_thm refl_thm: refl_thm | in_tc_4 tc_thm: tc_thm refl_thm: refl_thm),
    assumption?)+

lemma connected_components_member_eq:
  "v \<in> connected_component E w \<Longrightarrow> connected_component E v = connected_component E w"
  by(in_rtc tc_thm: connected_components_member_trans refl_thm: connected_components_member_sym)

lemma connected_components_closed:
    "\<lbrakk>v1 \<in> connected_component E v4; v3 \<in> connected_component E v4\<rbrakk> \<Longrightarrow> v3 \<in> connected_component E v1"
  by(in_rtc tc_thm: connected_components_member_trans refl_thm: connected_components_member_sym)

lemma C_is_componentE:
  assumes "C \<in> connected_components E"
  obtains v where "C = connected_component E v" "v \<in> Vs E"
  using assms
  by (fastforce simp add: connected_components_def)

lemma connected_components_closed':
  "\<lbrakk>v \<in> C; C \<in> connected_components E\<rbrakk> \<Longrightarrow> C = connected_component E v"
  by (fastforce elim: C_is_componentE simp: connected_components_member_eq)

lemma connected_components_closed'':
  "\<lbrakk>C \<in> connected_components E; v \<in> C\<rbrakk> \<Longrightarrow> C = connected_component E v"
  by (simp add: connected_components_closed')

lemma connected_components_eq:
  "\<lbrakk>v \<in> C ; v \<in> C'; C \<in> connected_components E; C' \<in> connected_components E\<rbrakk> \<Longrightarrow> C = C'"
  using connected_components_closed'[where E = E]
  by auto

lemma connected_components_eq':
  "\<lbrakk>C \<in> connected_components E; C' \<in> connected_components E; v \<in> C ; v \<in> C'\<rbrakk> \<Longrightarrow> C = C'"
  using connected_components_eq .

lemma connected_components_disj:
  "\<lbrakk>C \<noteq> C'; C \<in> connected_components E; C' \<in> connected_components E\<rbrakk> \<Longrightarrow> C \<inter> C' = {}"
  using connected_components_eq[where E = E]
  by auto

lemma own_connected_component_unique:
  assumes "x \<in> Vs E"
  shows "\<exists>!C \<in> connected_components E. x \<in> C"
proof(standard, intro conjI)
  show "connected_component E x \<in> connected_components E"
    using assms connected_components_def
    by blast
  show "x \<in> connected_component E x"
    using in_own_connected_component
    by fastforce
  fix C assume "C \<in> connected_components E \<and> x \<in> C"
  thus "C = connected_component E x"
    by (simp add: connected_components_closed')
qed

lemma edge_in_component:
  assumes "{x,y} \<in> E"
  shows "\<exists>C. C \<in> connected_components E \<and> {x,y} \<subseteq> C"
proof-
  have "y \<in> connected_component E x"
  proof(rule has_path_in_connected_component)
    show "walk_betw E x [x, y] y" 
      apply(rule nonempty_path_walk_between)
      using assms
      by auto
  qed
  moreover have "x \<in> Vs E" using assms
    by (auto dest: edges_are_Vs)
  ultimately show ?thesis
    unfolding connected_components_def
    using in_own_connected_component
    by fastforce
qed

lemma edge_in_unique_component:
  "{x,y} \<in> E \<Longrightarrow> \<exists>!C. C \<in> connected_components E \<and> {x,y} \<subseteq> C"
  by(force dest: connected_components_closed' edge_in_component )

lemma connected_component_set:
  "\<lbrakk>u \<in> Vs E; \<And>x. x \<in> C \<Longrightarrow> reachable E u x; \<And>x. reachable E u x \<Longrightarrow> x \<in> C\<rbrakk> \<Longrightarrow> connected_component E u = C"
  by (auto elim: in_connected_componentE intro: in_connected_componentI dest: reachable_refl)

text\<open>
  Now we should be able to partition the set of edges into equivalence classes
  corresponding to the connected components.\<close>

definition component_edges where
"component_edges E C = {{x, y} | x y.  {x, y} \<subseteq> C \<and> {x, y} \<in> E}"

lemma component_edges_disj_edges:
  assumes "C \<in> connected_components E" "C' \<in> connected_components E" "C \<noteq> C'"
  assumes "v \<in> component_edges E C" "w \<in> component_edges E C'"
  shows "v \<inter> w = {}"
proof(intro equals0I)
  fix x assume "x \<in> v \<inter> w"
  hence "x \<in> C" "x \<in> C'" using assms(4, 5) unfolding component_edges_def by blast+
  thus False
    using assms(1-3)
    by(auto dest: connected_components_closed')
qed

lemma component_edges_disj:
  assumes "C \<in> connected_components E" "C' \<in> connected_components E" "C \<noteq> C'"
  shows "component_edges E C \<inter> component_edges E C' = {}"
proof(intro equals0I, goal_cases)
  case (1 y)
  hence "y = {}"
    apply(subst Int_absorb[symmetric])
    apply(intro component_edges_disj_edges)
    using assms  
    by auto

  thus False using 1 unfolding component_edges_def by blast
qed

lemma reachable_in_Vs:
  assumes "reachable E u v"
  shows "u \<in> Vs E" "v \<in> Vs E"
  using assms
  by(auto dest: reachableD)

lemma connected_component_subs_Vs:
  "C \<in> connected_components E \<Longrightarrow> C \<subseteq> Vs E"
  by (auto simp: dest: reachable_in_Vs(2) elim: in_connected_componentE C_is_componentE)

definition components_edges where
"components_edges E = {component_edges E C| C. C \<in> connected_components E}"

lemma connected_comp_nempty:
  "C \<in> connected_components E \<Longrightarrow> C \<noteq> {}"
  using in_own_connected_component
  by (fastforce simp: connected_components_def)

lemma connected_comp_verts_in_verts:
  "\<lbrakk>v \<in> C; C \<in> connected_components E\<rbrakk> \<Longrightarrow> v \<in> Vs E"
  using connected_component_subs_Vs
  by blast

(* TODO replace  everywhere with C_componentE*)

lemma connected_comp_has_vert:
  assumes "C \<in> connected_components E"
  obtains w where "w \<in> Vs E" "C = connected_component E w"
  using C_is_componentE[OF assms]
  .

lemma component_edges_partition:
  shows "\<Union> (components_edges E) = E \<inter> {{x,y}| x y. True}"
  unfolding components_edges_def
proof(safe)
  fix x y
  assume "{x, y} \<in> E"
  then obtain C where "{x, y} \<subseteq> C" "C \<in> connected_components E"
    by (auto elim!: exE[OF edge_in_component])
  moreover then have "{x, y} \<in> component_edges E C"
    using \<open>{x, y} \<in> E\<close> component_edges_def
    by fastforce
  ultimately show "{x, y} \<in> \<Union> {component_edges E C |C. C \<in> connected_components E}"
    by blast
qed (auto simp add: component_edges_def)

text\<open>Since one of the matchings is bigger, there must be one edge equivalence class
  that has more edges from the bigger matching.\<close>

lemma lt_sum:
  "(\<Sum>x\<in>s. g x) < (\<Sum>x\<in>s. f x) \<Longrightarrow> \<exists>(x::'a ) \<in> s. ((g::'a \<Rightarrow> nat) x < f x)"
  by (auto simp add: not_le[symmetric] intro: sum_mono)

lemma Union_lt:
  assumes finite: "finite S" "finite t" "finite u" and
    card_lt: "card ((\<Union> S) \<inter> t) < card ((\<Union> S) \<inter> u)" and 
    disj: "\<forall>s\<in>S.\<forall>s'\<in>S. s \<noteq> s' \<longrightarrow> s \<inter> s' = {}"
  shows "\<exists>s\<in>S. card (s \<inter> t) < card (s \<inter> u)"
proof-
  {
    fix t::"'a set"
    assume ass: "finite t"
    have "card (\<Union>s\<in>S. s \<inter> t) = (\<Sum>s\<in>S. card (s \<inter> t))"
      using ass disj
      by(fastforce intro!: card_UN_disjoint finite)
  }note * = this
  show ?thesis
    using card_lt *[OF finite(2)] *[OF finite(3)]
    by (auto intro: lt_sum)
qed

(*
  The edges in that bigger equivalence class can be ordered in a path, since the degree of any
  vertex cannot exceed 2. Also that path should start and end with edges from the bigger matching.
*)

subsection\<open>Alternating lists and auxilliary theory about them\<close>

inductive alt_list where
"alt_list P1 P2 []" |
"P1 x \<Longrightarrow> alt_list P2 P1 l \<Longrightarrow> alt_list P1 P2 (x#l)"

inductive_simps alt_list_empty: "alt_list P1 P2 []"
inductive_simps alt_list_step: "alt_list P1 P2 (x#l)"

lemma induct_alt_list012[consumes 1, case_names nil single sucsuc]:
  assumes "alt_list P1 P2 l"
  assumes "T []"
  assumes "\<And>x. P1 x \<Longrightarrow> T [x]"
  assumes "\<And>x y zs. P1 x \<Longrightarrow> P2 y \<Longrightarrow> T zs \<Longrightarrow> T (x#y#zs)"
  shows "T l"
  using assms(1)
proof(induction l rule: induct_list012)
  case nil thus ?case using assms(2) by simp
next
  case (single x) thus ?case
    by (simp add: alt_list_step assms(3))
next
  case (sucsuc x y zs)
  thus ?case
    by (simp add: alt_list_step assms(4))
qed

lemma alternating_length:
  assumes "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "length l = length (filter P1 l) + length (filter P2 l)"
  using assms by (induction l) auto

lemma alternating_length_balanced:
  assumes "alt_list P1 P2 l" "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "length (filter P1 l) = length (filter P2 l) \<or>
         length (filter P1 l) = length (filter P2 l) + 1"
  using assms by (induction l) auto

lemma alternating_eq_iff_even:
  assumes "alt_list P1 P2 l" "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "length (filter P1 l) = length (filter P2 l) \<longleftrightarrow> even (length l)"
proof
  assume "length (filter P1 l) = length (filter P2 l)"
  thus "even (length l)" using assms alternating_length by force
next
  assume "even (length l)"
  thus "length (filter P1 l) = length (filter P2 l)"
    using alternating_length_balanced[OF assms] alternating_length[OF assms(2)]
    by auto
qed

lemma alternating_eq_iff_odd:
  assumes "alt_list P1 P2 l" "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "length (filter P1 l) = length (filter P2 l) + 1 \<longleftrightarrow> odd (length l)"
proof
  assume "length (filter P1 l) = length (filter P2 l) + 1"
  thus "odd (length l)" using assms alternating_length by force
next
  assume "odd (length l)"
  thus "length (filter P1 l) = length (filter P2 l) + 1"
    using assms alternating_length_balanced alternating_eq_iff_even by blast
qed

lemma alternating_list_odd_index:
  assumes "alt_list P1 P2 l" "odd n" "n < length l"
  shows "P2 (l ! n)"
  using assms                                  
proof(induction arbitrary: n rule: induct_alt_list012)
  case (sucsuc x y zs)
  consider (l) "n = 1" | (h) "n \<ge> 2" using odd_pos sucsuc.prems(1) by fastforce
  thus ?case
  proof cases
    case l thus ?thesis by (simp add: sucsuc.hyps(2))
  next
    case h
    then obtain m where "n = Suc (Suc m)" using add_2_eq_Suc le_Suc_ex by blast
    hence "P2 (zs ! m)" using sucsuc.IH sucsuc.prems(1, 2) by fastforce
    thus ?thesis by (simp add: \<open>n = Suc (Suc m)\<close>)
  qed
qed simp_all

lemma alternating_list_even_index:
  assumes "alt_list P1 P2 l" "even n" "n < length l"
  shows "P1 (l ! n)"
  using assms
proof(induction arbitrary: n rule: induct_alt_list012)
  case (sucsuc x y zs)
  consider (l) "n = 0" | (h) "n \<ge> 2" using odd_pos sucsuc.prems(1) by fastforce
  thus ?case
  proof cases
    case l thus ?thesis by (simp add: sucsuc.hyps(1))
  next
    case h
    then obtain m where "n = Suc (Suc m)" using add_2_eq_Suc le_Suc_ex by blast
    hence "P1 (zs ! m)" using sucsuc.IH sucsuc.prems(1, 2) by fastforce
    thus ?thesis by (simp add: \<open>n = Suc (Suc m)\<close>)
  qed
qed simp_all

lemma alternating_list_even_last:
  assumes "alt_list P1 P2 l" "even (length l)" "l \<noteq> []"
  shows "P2 (last l)"
proof-
  have "odd (length l - 1)" by (simp add: assms(2) assms(3))
  hence "P2 (l ! (length l - 1))" 
    by(auto intro: alternating_list_odd_index[OF assms(1)])
  thus ?thesis using assms(3) by (simp add: last_conv_nth)
qed

lemma alternating_list_odd_last:
  assumes "alt_list P1 P2 l" "odd (length l)"
  shows "P1 (last l)"
proof-
  have "even (length l - 1)" by (simp add: assms(2))
  hence "P1 (l ! (length l - 1))" using alternating_list_even_index
    using assms(1) assms(2) odd_pos by fastforce
  thus ?thesis using assms(2) last_conv_nth odd_pos by force
qed

lemma alternating_list_gt_odd:
  assumes "length (filter P1 l) > length (filter P2 l)"
  assumes "alt_list P1 P2 l"
  assumes "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "odd (length l)"
  using assms alternating_eq_iff_even by fastforce

lemma alternating_list_eq_even:
  assumes "length (filter P1 l) = length (filter P2 l)"
  assumes "alt_list P1 P2 l" (* not actually used but complements gt_odd *)
  assumes "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "even (length l)"
  using assms alternating_eq_iff_even by fastforce

(*TODO fix metis *)

lemma alternating_list_eq_last':
  "\<lbrakk>length (filter P1 l) = length (filter P2 l); \<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x; l \<noteq> []; P2 (last l)\<rbrakk>
    \<Longrightarrow> \<not> alt_list P2 P1 l"
  using alternating_eq_iff_even alternating_list_even_last last_in_set
  by fastforce

lemma gt_zero:"x < (y::nat) \<Longrightarrow> 0 < y"
  by auto

lemma alternating_list_gt:
  "\<lbrakk>length (filter P1 l) > length (filter P2 l); \<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x; alt_list P1 P2 l\<rbrakk> \<Longrightarrow>
    P1 (hd l) \<and> P1 (last l)"
  apply(intro conjI)
  subgoal by (fastforce  simp: neq_Nil_conv alt_list_step dest: gt_zero order.strict_trans2[OF _ length_filter_le])
  subgoal using alternating_list_odd_last alternating_list_gt_odd
    by fastforce
  done

(*TODO fix metis *)

lemma alt_list_not_commute:
  assumes "alt_list P1 P2 l"
          "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
          "l \<noteq> []"
    shows "\<not> alt_list P2 P1 l"
  using assms
  by(auto simp add: neq_Nil_conv alt_list_step)

lemma alternating_list_gt_or:
  assumes "length (filter P1 l) > length (filter P2 l)"
          "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
    shows "\<not> alt_list P2 P1 l"
  using alternating_length_balanced assms by fastforce

lemma alt_list_cong_1:
  assumes "alt_list P1 P2 l" "\<forall>x \<in> set l. P2 x \<longrightarrow> P3 x"
  shows "alt_list P1 P3 l"
  using assms
  by (induction rule: induct_alt_list012)
     (simp_all add: alt_list_empty alt_list_step)

lemma alt_list_cong_2:
  assumes "alt_list P1 P2 l" "\<And>x. \<lbrakk>x \<in> set l; P1 x\<rbrakk> \<Longrightarrow> P3 x"
  shows "alt_list P3 P2 l"
  using assms
  by (induction rule: induct_alt_list012)
     (simp_all add: alt_list_empty alt_list_step)

lemma alt_list_cong:
  assumes "alt_list P1 P2 l" "\<forall>x \<in> set l. P1 x \<longrightarrow> P3 x" "\<forall>x \<in> set l. P2 x \<longrightarrow> P4 x"
  shows "alt_list P3 P4 l"
  using assms
  by (induction rule: induct_alt_list012)
     (simp_all add: alt_list_empty alt_list_step)

lemma alt_list_append_1:
  assumes "alt_list P1 P2 (l1 @ l2)"
  shows "alt_list P1 P2 l1  \<and> (alt_list P1 P2 l2 \<or> alt_list P2 P1 l2)"
  using assms
  by (induction l1 rule: induct_list012)
     (simp_all add: alt_list_empty alt_list_step)

lemma alt_list_append_2:
  assumes "alt_list P1 P2 l1" "alt_list P2 P1 l2" "odd (length l1)"
  shows "alt_list P1 P2 (l1 @ l2)"
  using assms
proof (induction l1 rule: induct_list012)
  case (sucsuc x y zs)
  thus ?case
    by (auto simp: alt_list_step)
qed (simp_all add: alt_list_step)


lemma alt_list_append_3:
  assumes "alt_list P1 P2 l1" "alt_list P1 P2 l2" "even (length l1)"
  shows "alt_list P1 P2 (l1 @ l2)"
  using assms
proof (induction l1 rule: induct_list012)
  case (sucsuc x y zs)
  thus ?case
    by (auto simp: alt_list_step)
qed (simp_all add: alt_list_step)

lemma alt_list_split_1:
  assumes "alt_list P1 P2 (l1 @ l2)" "even (length l1)"
  shows "alt_list P1 P2 l2"
  using assms
  by (induction l1 rule: induct_list012)
     (simp_all add: alt_list_step)

lemma alt_list_split_2:
  assumes "alt_list P1 P2 (l1 @ l2)" "odd (length l1)"
  shows "alt_list P2 P1 l2"
  using assms
  by (induction l1 rule: induct_list012)
     (simp_all add: alt_list_step)

lemma alt_list_append_1':
  assumes "alt_list P1 P2 (l1 @ l2)" "l1 \<noteq> []" "\<And>x. x\<in>set l1 \<Longrightarrow> P1 x = (\<not> P2 x)"
  shows "(alt_list P1 P2 l1  \<and> ((P2 (last l1) \<and> alt_list P1 P2 l2) \<or> (P1 (last l1) \<and> alt_list P2 P1 l2)))"
proof(cases "alt_list P2 P1 l2")
  case True
  then show ?thesis
    using assms[unfolded neq_Nil_conv] alt_list_append_1[OF assms(1)]
    by (force simp add: alt_list_step dest!: alt_list_split_2 alternating_list_even_last)
next
  case False
  then show ?thesis
    using assms[unfolded neq_Nil_conv] alt_list_append_1[OF assms(1)]
    by (force simp add: alt_list_step dest: alt_list_split_1 alternating_list_odd_last)
qed

lemma alt_list_rev_even:
  assumes "alt_list P1 P2 l" "even (length l)"
  shows "alt_list P2 P1 (rev l)"
  using assms
proof(induction rule: induct_alt_list012)
  case (sucsuc x y zs)
  hence "alt_list P2 P1 (rev zs)" by simp
  moreover have "alt_list P2 P1 [y, x]"
    by (simp add: alt_list_empty alt_list_step sucsuc.hyps(1) sucsuc.hyps(2))
  ultimately have "alt_list P2 P1 (rev zs @ [y, x])"
    using alt_list_append_3 sucsuc.prems by fastforce
  thus ?case by simp
qed (simp_all add: alt_list_empty)

lemma alt_list_rev:
  assumes "alt_list P1 P2 l" "odd (length l)"
  shows "alt_list P1 P2 (rev l)" 
  using assms
proof-
  obtain x zs where "l = x # zs" using assms(2) by (cases l, fastforce+)
  hence "alt_list P1 P2 (rev zs)"using assms
    by (auto intro!: alt_list_rev_even simp: alt_list_step) 
  moreover have "alt_list P1 P2 [x]"
    using assms(1)[simplified \<open>l = x # zs\<close>]
    by (auto simp: alt_list_empty alt_list_step )
  ultimately show ?thesis using alt_list_append_3 \<open>l = x # zs\<close> assms(2) by fastforce
qed

subsection\<open>Every connected component can be linearised in a path.\<close>

lemma path_subset_conn_comp:
  assumes "path E p"
  shows "set p \<subseteq> connected_component E (hd p)"
  using assms
proof(induction)
  case path0
  then show ?case by simp
next
  case path1
  then show ?case using in_own_connected_component by simp
next
  case (path2 v v' vs)
  hence "walk_betw E v' [v',v] v"
    by (simp add: edges_are_walks insert_commute)
  hence "v \<in> connected_component E v'"
    by (auto dest:has_path_in_connected_component) 
  moreover hence "connected_component E v = connected_component E v'"
    by (simp add: connected_components_member_eq)
  ultimately show ?case using path2.IH by fastforce
qed

lemma walk_betw_subset_conn_comp:
  "walk_betw E u p v \<Longrightarrow> set p \<subseteq> connected_component E u"
  using path_subset_conn_comp
  by (auto simp: walk_betw_def)

lemma path_in_connected_component:
  "\<lbrakk>path E p; hd p \<in> connected_component E x\<rbrakk> \<Longrightarrow> set p \<subseteq> connected_component E x"
  by (fastforce dest: path_subset_conn_comp simp: connected_components_member_eq)

lemma component_has_path:
  assumes "finite C'" "C' \<subseteq> C" "C \<in> connected_components E"
  shows "\<exists>p. path E p \<and> C' \<subseteq> (set p) \<and> (set p) \<subseteq> C"
  using assms
proof(induction C')
  case empty thus ?case
    using path0 by fastforce
next
  case ass: (insert x F)
  then obtain p where p: "path E p" "F \<subseteq> set p" "set p \<subseteq> C"
    by auto
  have "x \<in> C" using ass.prems(1) by blast
  hence C_def: "C = connected_component E x"
    by (simp add: assms(3) connected_components_closed')

  show ?case
  proof(cases "p = []")
    case True
    have "path E [x]" using ass connected_comp_verts_in_verts by force
    then show ?thesis using True p ass.prems(1) by fastforce
  next
    case F1: False
    then obtain h t where "p = h # t" using list.exhaust_sel by blast
    hence walkhp: "walk_betw E h p (last p)" using p(1) walk_betw_def by fastforce

    have "h \<in> C" using \<open>p = h # t\<close> p(3) by fastforce
    moreover have "x \<in> Vs E"
      using \<open>x \<in> C\<close> assms(3) connected_component_subs_Vs
      by auto
    ultimately obtain q where walkxh: "walk_betw E x q h"
      by (auto simp: C_def elim: in_connected_component_has_walk)
    hence walkxp: "walk_betw E x (q @ tl p) (last p)"
      by (simp add: walk_transitive walkhp)
    moreover hence "set (q @ tl p) \<subseteq> C"
      by(auto simp: C_def dest!: walk_betw_subset_conn_comp)
    moreover from walkxp have "path E (q @ tl p)"
      by (fastforce dest: walk_between_nonempty_pathD)
    moreover {
      from walkxh have "last q = h" "hd q = x" by (fastforce dest: walk_between_nonempty_pathD)+
      then have "insert x F \<subseteq> set (q @ tl p)" using \<open>p = h # t\<close> walkxh p(2) by fastforce
    }
    ultimately show ?thesis by blast
  qed
qed

lemma component_has_path':
  "\<lbrakk>finite C; C \<in> connected_components E\<rbrakk> \<Longrightarrow> \<exists>p. path E p \<and> C = (set p)"
  using component_has_path
  by fastforce

subsection\<open>Every connected component can be linearised in a simple path\<close>

text\<open>An important part of this proof is setting up and induction on the graph, i.e. on a set of
     edges, and the different cases that could arise.\<close>

definition card' :: "'a set \<Rightarrow> enat" where
  "card' A \<equiv> (if infinite A then \<infinity> else card A)"

lemma card'_finite: "finite A \<Longrightarrow> card' A = card A"
  unfolding card'_def by simp

lemma card'_mono: "A \<subseteq> B \<Longrightarrow> card' A \<le> card' B"
  using finite_subset
  by (auto simp add: card'_def intro: card_mono)

lemma card'_empty[iff]: "(card' A = 0) \<longleftrightarrow> A = {}"
  unfolding card'_def using enat_0_iff(2) by auto

lemma card'_finite_nat[iff]: "(card' A = numeral m) \<longleftrightarrow> (finite A \<and> card A = numeral m)"
  unfolding card'_def
  by (simp add: numeral_eq_enat)

(*TODO: remove the enat notions*)

declare one_enat_def

declare zero_enat_def

lemma eval_enat_numeral:
  "numeral Num.One = eSuc 0"
  "numeral (Num.Bit0 n) = eSuc (numeral (Num.BitM n))"
  "numeral (Num.Bit1 n) = eSuc (numeral (Num.Bit0 n))"
  by (simp_all add: BitM_plus_one eSuc_enat numeral_plus_one[symmetric] zero_enat_def one_enat_def)

declare eSuc_enat[symmetric, simp]

lemma card'_finite_enat[iff]: "(card' A = enat m) \<longleftrightarrow> (finite A \<and> card A = m)"
  unfolding card'_def by simp

(*TODO: FIX METIS*)

lemma card'_1_singletonE:
  assumes "card' A = 1"
  obtains x where "A = {x}"
  using assms
  unfolding card'_def
  by (fastforce elim!: card_1_singletonE dest: iffD1[OF enat_1_iff(1)] split: if_splits)

lemma card'_insert[simp]: "card' (insert a A) = (if a \<in> A then id else eSuc) (card' A)"
  using card_insert_if finite_insert
  by (simp add: card_insert_if card'_def)

lemma card'_empty_2[simp]: "card' {} = enat 0"
  by (simp add: card'_def)

definition degree where
  "degree E v \<equiv> card' ({e. v \<in> e} \<inter> E)"

lemma degree_def2: "degree E v \<equiv> card' {e \<in> E. v \<in> e}"
  unfolding degree_def
  by (simp add: Collect_conj_eq Int_commute)

lemma degree_Vs: "degree E v \<ge> 1" if "v \<in> Vs E"
proof-
  obtain e where "e \<in> E" "v \<in> e"
    using \<open>v \<in> Vs E\<close>
    by (auto simp: Vs_def)
  hence "{e} \<subseteq> {e \<in> E. v \<in> e}" by simp
  moreover have "card' {e} = 1" by (simp add: one_enat_def)
  ultimately show ?thesis
    by(fastforce dest!: card'_mono simp: degree_def2)
qed

lemma degree_not_Vs: "v \<notin> Vs E \<Longrightarrow> degree E v = 0"
  by (fastforce simp only: Vs_def degree_def)

lemma degree_insert: "\<lbrakk>v \<in> a; a \<notin> E\<rbrakk> \<Longrightarrow> degree (insert a E) v = eSuc (degree E v)"
  by (simp add: degree_def)

lemma degree_empty[simp]: "degree {} a = 0"
  unfolding degree_def by (simp add: zero_enat_def)

lemma degree_card_all:
  assumes "card E \<ge> numeral m"
  assumes "\<forall>e \<in> E. a \<in> e"
  assumes "finite E"
  shows "degree E a \<ge> numeral m"
  using assms unfolding degree_def
  by (simp add: card'_finite inf.absorb2 subsetI)

lemma subset_edges_less_degree:
  "E' \<subseteq> E \<Longrightarrow> degree E' v \<le> degree E v"
  by (auto intro: card'_mono simp: degree_def)

lemma less_edges_less_degree:
  shows "degree (E - E') v \<le> degree E v"
  by (intro subset_edges_less_degree)
     (simp add: subset_edges_less_degree)

lemma in_edges_of_path':
  "\<lbrakk> v \<in> set p; length p \<ge> 2\<rbrakk> \<Longrightarrow> v \<in> Vs (set (edges_of_path p))"
  by(auto dest: path_vertex_has_edge simp: Vs_def)

lemma in_edges_of_path:
  assumes "v \<in> set p" "v \<noteq> hd p"
  shows "v \<in> Vs (set (edges_of_path p))"
proof-
  have "length p \<ge> 2" using assms 
    by(cases p, auto dest!: length_pos_if_in_set simp: neq_Nil_conv)
  thus ?thesis by (simp add: assms(1) in_edges_of_path')
qed

lemma degree_edges_of_path_hd:
  assumes "distinct p" "length p \<ge> 2"
  shows "degree (set (edges_of_path p)) (hd p) = 1"
proof-
  obtain h nxt rest where p_def: "p = h # nxt # rest" using assms(2)
    by (auto simp: Suc_le_length_iff eval_nat_numeral)
  have calc: "{e. hd (h # nxt # rest) \<in> e} \<inter> set (edges_of_path (h # nxt # rest)) = {{h, nxt}}"
  proof(standard; standard)
    fix e assume "e \<in> {e. hd (h # nxt # rest) \<in> e} \<inter> set (edges_of_path (h # nxt # rest))"
    hence "e = {h, nxt} \<or> e \<in> set (edges_of_path (nxt # rest))" "h \<in> e" by fastforce+
    hence "e = {h, nxt}" using assms(1) v_in_edge_in_path_gen unfolding p_def by fastforce
    then show "e \<in> {{h, nxt}}" by simp
  qed simp
  show ?thesis unfolding p_def degree_def calc by (simp add: one_enat_def)
qed

lemma degree_edges_of_path_last:
  assumes "distinct p" "length p \<ge> 2"
  shows "degree (set (edges_of_path p)) (last p) = 1"
proof-
  have "distinct (rev p)" using assms(1) by simp
  moreover have "length (rev p) \<ge> 2" using assms(2) by simp
  ultimately have "degree (set (edges_of_path (rev p))) (hd (rev p)) = 1"
    using degree_edges_of_path_hd by blast
  then show ?thesis
    by(simp add: edges_of_path_rev[symmetric] hd_rev)
qed

lemma degree_edges_of_path_ge_2:
  assumes "distinct p" "v\<in>set p" "v \<noteq> hd p" "v \<noteq> last p"
  shows "degree (set (edges_of_path p)) v = 2"
  using assms
proof(induction p arbitrary: v rule: induct_list012)
  case nil then show ?case by simp
next
  case single then show ?case by simp
next
  case Cons: (sucsuc a a' p v)
  thus ?case
  proof(cases p)
    case Nil thus ?thesis using Cons.prems by simp
  next
    case p: (Cons a'' p')
    let ?goalset = "{e. a' \<in> e} \<inter> set (edges_of_path (a # a' # a'' # p'))"
    {
      have anotaa: "{a, a'} \<noteq> {a', a''}" using p Cons.prems(1) by fastforce
      moreover have "?goalset = {{a, a'}, {a', a''}}"
      proof(standard; standard)
        fix e assume "e \<in> ?goalset"
        moreover have "a' \<notin> f" if "f \<in> set (edges_of_path (a'' # p'))" for f
          using Cons.prems(1) p that v_in_edge_in_path_gen by fastforce
        ultimately show "e \<in> {{a, a'}, {a', a''}}" by force
      qed fastforce
      moreover have "card {{a, a'}, {a', a''}} = 2" using anotaa by simp
      ultimately have "2 = degree (set (edges_of_path (a # a' # p))) a'"
        unfolding degree_def p by (simp add: eval_enat_numeral one_enat_def)
    }
    moreover {
      fix w assume "w \<in> set (a' # p)" "w \<noteq> hd (a' # p)" "w \<noteq> last (a' # p)"
      hence "2 = degree (set (edges_of_path (a' # p))) w"
        using Cons.IH(2) Cons.prems(1) by fastforce
      moreover have "w \<notin> {a, a'}"
        using Cons.prems(1) \<open>w \<in> set (a' # p)\<close> \<open>w \<noteq> hd (a' # p)\<close> by auto
      ultimately have "2 = degree (set (edges_of_path (a # a' # p))) w" unfolding degree_def by simp
    }
    ultimately show ?thesis using Cons.prems(2-4) by auto
  qed
qed

lemma in_Vs_insertE:
  "v \<in> Vs (insert e E) \<Longrightarrow> (v \<in> e \<Longrightarrow> P) \<Longrightarrow> (v \<in> Vs E \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Vs_def)

lemma list_sing_conv:
  "([x] = ys @ [y]) \<longleftrightarrow> (ys = [] \<and> y = x)"
  "([x] = y#ys) \<longleftrightarrow> (ys = [] \<and> y = x)"
  by (induction ys) auto

lemma path_insertE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>path (insert e E) p; 
     (p = [] \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v \<in> e \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v \<in> Vs E \<Longrightarrow> P);
     (\<And>p' v1 v2. \<lbrakk>path {e} [v1, v2]; path (insert e E) (v2 # p'); p = v1 # v2 # p'\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v1 v2. \<lbrakk>path E [v1,v2]; path (insert e E) (v2 # p'); p = v1 # v2 # p'\<rbrakk> \<Longrightarrow> P )\<rbrakk>
    \<Longrightarrow> P"
proof(induction rule: path.induct)
  case path0
  then show ?case 
    by auto
next
  case (path1 v)
  then show ?case
    by (auto elim!: in_Vs_insertE)
next
  case (path2 v v' vs)
  then show ?case
    apply (auto simp: vs_member)
    by blast
qed

text \<open>A lemma which allows for case splitting over paths when doing induction on graph edges.\<close>

lemma welk_betw_insertE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>walk_betw (insert e E) v1 p v2; 
     (\<lbrakk>v1\<in>Vs (insert e E); v1 = v2; p = []\<rbrakk> \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v = v1 \<Longrightarrow> v = v2 \<Longrightarrow> v \<in> e \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v = v1 \<Longrightarrow> v = v2 \<Longrightarrow> v \<in> Vs E \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>walk_betw {e} v1 [v1,v3] v3; walk_betw (insert e E) v3 (v3 # p') v2; p = v1 # v3 # p'\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>walk_betw E v1 [v1,v3] v3; walk_betw (insert e E) v3 (v3 # p') v2; p = v1 # v3 # p'\<rbrakk> \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  unfolding walk_betw_def
  apply safe
  apply(erule path_insertE)
  by (simp | force)+

lemma reachable_insertE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>reachable (insert e E) v1 v2;
     (\<lbrakk>v1 \<in> e; v1 = v2\<rbrakk> \<Longrightarrow> P);
     (\<lbrakk>v1 \<in> Vs E; v1 = v2\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>reachable {e} v1 v3; reachable (insert e E) v3 v2\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>reachable E v1 v3; reachable (insert e E) v3 v2\<rbrakk> \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  unfolding reachable_def
  apply(erule exE)
  apply(erule welk_betw_insertE)
  by (force simp: Vs_def)+

lemma in_Vs_unionE:
  "v \<in> Vs (E1 \<union> E2) \<Longrightarrow> (v \<in> Vs E1 \<Longrightarrow> P) \<Longrightarrow> (v \<in> Vs E2 \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Vs_def)

lemma path_unionE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>path (E1 \<union> E2) p; 
     (p = [] \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v \<in> Vs E1 \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v \<in> Vs E2 \<Longrightarrow> P);
     (\<And>p' v1 v2. \<lbrakk>path E1 [v1, v2]; path (E1 \<union> E2) (v2 # p'); p = v1 # v2 # p'\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v1 v2. \<lbrakk>path E2 [v1,v2]; path (E1 \<union> E2) (v2 # p'); p = v1 # v2 # p'\<rbrakk> \<Longrightarrow> P )\<rbrakk>
    \<Longrightarrow> P"
proof(induction rule: path.induct)
  case path0
  then show ?case 
    by auto
next
  case (path1 v)
  then show ?case
    by (auto elim!: in_Vs_unionE)
next
  case (path2 v v' vs)
  then show ?case
    by (simp add: vs_member) blast+
qed

lemma welk_betw_unionE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>walk_betw (E1 \<union> E2) v1 p v2; 
     (\<lbrakk>v1\<in>Vs (E1 \<union> E2); v1 = v2; p = []\<rbrakk> \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v = v1 \<Longrightarrow> v = v2 \<Longrightarrow> v \<in> Vs E1 \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v = v1 \<Longrightarrow> v = v2 \<Longrightarrow> v \<in> Vs E2 \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>walk_betw E1 v1 [v1,v3] v3; walk_betw (E1 \<union> E2) v3 (v3 # p') v2; p = v1 # v3 # p'\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>walk_betw E2 v1 [v1,v3] v3; walk_betw (E1 \<union> E2) v3 (v3 # p') v2; p = v1 # v3 # p'\<rbrakk> \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  unfolding walk_betw_def
  apply safe
  apply(erule path_unionE)
  by (simp | force)+

lemma reachable_unionE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>reachable (E1 \<union> E2) v1 v2;
     (\<lbrakk>v1 \<in> Vs E2; v1 = v2\<rbrakk> \<Longrightarrow> P);
     (\<lbrakk>v1 \<in> Vs E1; v1 = v2\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>reachable E1 v1 v3; reachable (E1 \<union> E2) v3 v2\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>reachable E2 v1 v3; reachable (E1 \<union> E2) v3 v2\<rbrakk> \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  unfolding reachable_def
  apply(erule exE)
  apply(erule welk_betw_unionE)
  by (force simp: Vs_def)+

lemma singleton_subset: "path {e} p \<Longrightarrow> set p \<subseteq> e"
  by (induction rule: path.induct) (auto simp: Vs_def)

lemma path_singletonD: 
  "path {{v1::'a,v2}} p \<Longrightarrow> p \<noteq> [] \<Longrightarrow> (hd p = v1 \<or> hd p = v2) \<and> (last p = v1 \<or> last p = v2)"
  by (induction rule: path.induct) (auto simp: Vs_def)

lemma path_repl_edge:
  assumes "path (insert {w, x} E) p" "p \<noteq> []" "walk_betw E w puv x"
  shows "\<exists>p'. walk_betw E (hd p) p' (last p)"
  using assms
proof(induction rule: induct_list012)
  case nil
  then show ?case
    by auto
next
  case (single x)
  then show ?case
    using walk_reflexive
    by (fastforce elim!: in_Vs_insertE dest: walk_endpoints)+
next
  case (sucsuc x y zs)
  then show ?case
    apply -
  proof(erule path_insertE, goal_cases)
    case (4 p' v1 v2)
    then show ?case
      using walk_symmetric walk_transitive
      by(fastforce simp del: path_simps dest!: path_singletonD)
  next
    case (5 p' v1 v2)
    then show ?case
      using walk_transitive
      by (fastforce simp del: path_simps elim!: nonempty_path_walk_betweenE)
  qed auto
qed

lemma in_connected_componentI3:
  "\<lbrakk>C \<in> connected_components E; w \<in> C; x \<in> C\<rbrakk> \<Longrightarrow> x \<in> connected_component E w"
  using connected_components_closed'
  by fastforce

lemma same_con_comp_reachable:
  "\<lbrakk>C \<in> connected_components E; w \<in> C; x \<in> C\<rbrakk> \<Longrightarrow> reachable E w x"
  using in_connected_componentI3
  by(fastforce intro: reachable_refl connected_comp_verts_in_verts elim: in_connected_componentE)

lemma same_con_comp_walk:
  assumes "C \<in> connected_components E" "w \<in> C" "x \<in> C"
  obtains pwx where "walk_betw E w pwx x"
proof-
  have "x \<in> connected_component E w" 
    using assms
    by (rule in_connected_componentI3)
  thus ?thesis
    using connected_comp_verts_in_verts[OF \<open>w \<in> C\<close> \<open>C \<in> connected_components E\<close>]
    by (auto elim: that in_connected_component_has_walk)
qed                             

lemma in_connected_componentI4:
  assumes "walk_betw E u puv v" "u \<in> C" "C \<in> connected_components E"
  shows "v \<in> C"
  using assms connected_components_closed'
  by (fastforce intro: has_path_in_connected_component)

lemma walk_betw_singletonD:
  "walk_betw {{v1::'a,v2}} u p v \<Longrightarrow> p \<noteq> [] \<Longrightarrow> (hd p = v1 \<or> hd p = v2) \<and> (last p = v1 \<or> last p = v2) \<and> hd p = u \<and> last p = v"
  by (fastforce simp: walk_betw_def dest: path_singletonD)

(*TODO rename: path_can_be_split \<rightarrow> walk_can_be_split *)

lemma path_can_be_split:
  assumes "walk_betw (insert {w, x} E) u p v" "w \<in> Vs E" "x \<in> Vs E"
  shows "(\<exists>p. walk_betw E u p v) \<or>
         (\<exists>p1 p2. walk_betw E u p1 w \<and> walk_betw E x p2 v) \<or>
         (\<exists>p1 p2. walk_betw E u p1 x \<and> walk_betw E w p2 v)"
  using assms
proof(induction p arbitrary: u v)
  case Nil
  then show ?case
    by (auto simp: walk_betw_def)
next
  case (Cons a zs)
  then show ?case
    apply -
  proof(erule welk_betw_insertE, goal_cases)
    case (4 p' v3)
    (*TODO: Lukas*)
      then show ?case
      apply simp
      using walk_between_nonempty_pathD(4)[OF \<open>walk_betw {{w, x}} u [u, v3] v3\<close>]
            walk_betw_singletonD[OF \<open>walk_betw {{w, x}} u [u, v3] v3\<close>]
      by (auto dest: walk_reflexive)
  next
    case (5 p' v3)
    then show ?case
      (*TODO: Lukas*)
      using walk_transitive[OF \<open>walk_betw E u [u, v3] v3\<close>]
      by blast
  qed (insert walk_reflexive, fastforce)+
qed

lemma reachability_split:
  "\<lbrakk>reachable (insert {w, x} E) u v; w \<in> Vs E; x \<in> Vs E\<rbrakk> \<Longrightarrow>
        (reachable E u v) \<or>
         (reachable E u w \<and> reachable E x v) \<or>
         (reachable E u x \<and> reachable E w v)"
  by(auto simp: reachable_def dest: path_can_be_split)

lemma connected_component_in_components:
  "v \<in> Vs E \<Longrightarrow> connected_component E v \<in> connected_components E"
  by (fastforce simp: connected_components_def)

lemma reachable_subset:
  "\<lbrakk>reachable E u v; E \<subseteq> E'\<rbrakk> \<Longrightarrow> reachable E' u v"
  by (auto dest: walk_subset intro: reachableI elim!: reachableE)

lemma in_Vs_insert: "x \<in> Vs E \<Longrightarrow> x \<in> Vs (insert e E)"
  by (auto simp: Vs_def)
  
lemma path_can_be_split_2:
  assumes "walk_betw (insert {w, x} E) u p v" "w \<in> Vs E" "x \<notin> Vs E"
  shows "(\<exists>p'. walk_betw E u p' v) \<or>
         (\<exists>p'. walk_betw E u p' w \<and> v = x) \<or>
         (\<exists>p'. walk_betw E w p' v \<and> u = x) \<or>
         (u = x \<and> v = x)"
  using assms
proof(induction p arbitrary: u v)
  case Nil
  then show ?case
    by (auto simp: walk_betw_def)
next
  case (Cons a zs)
  then show ?case
    apply -
  proof(erule welk_betw_insertE, goal_cases)
    case (4 p' v3)
    then show ?case
      (*TODO: Lukas*)
      using walk_betw_singletonD[OF \<open>walk_betw {{w, x}} u [u, v3] v3\<close>]
      by (auto dest: walk_endpoints(1) walk_reflexive)
  next
    case (5 p' v3)
    then show ?case
     (*TODO: Lukas*)
      using walk_transitive[OF \<open>walk_betw E u [u, v3] v3\<close>] walk_endpoints(2)
      by (metis list.sel(3))
  qed (auto dest: walk_reflexive)+
qed

lemma reachability_split_2:
  "\<lbrakk>reachable (insert {w, x} E) u v; w \<in> Vs E; x \<notin> Vs E\<rbrakk> \<Longrightarrow>
     (reachable E u v) \<or>
     (reachable E u w \<and> v = x) \<or>
     (reachable E w v \<and> u = x) \<or>
     (u = x \<and> v = x)"
  by(auto simp: reachable_def dest: path_can_be_split_2)

lemma walk_betw_cons:
  "walk_betw E v1 (v2 # v3 # p) v4 \<longleftrightarrow> 
    (walk_betw E v3 (v3 # p) v4 \<and> walk_betw E v1 [v2, v3] v3)"
  by(auto simp: walk_betw_def)

lemma path_can_be_split_3:
  assumes "walk_betw (insert {w, x} E) u p v" "w \<notin> Vs E" "x \<notin> Vs E"
  shows "walk_betw E u p v \<or> walk_betw {{w, x}} u p v"
  using assms
proof(induction p arbitrary: u v)
  case Nil
  then show ?case
    by (auto simp: walk_betw_def)
next
  case (Cons a zs)
  then show ?case
    apply -
  proof(erule welk_betw_insertE, goal_cases)
    case (4 p' v3)
    then show ?case
      (*TODO: Lukas*)
      using walk_betw_singletonD[OF \<open>walk_betw {{w, x}} u [u, v3] v3\<close>]
      by (simp, metis walk_betw_cons walk_endpoints(1))
  next
    case (5 p' v3)
    then show ?case
      (*TODO: Lukas*)
      using walk_transitive[OF \<open>walk_betw E u [u, v3] v3\<close>] walk_betw_singletonD
      by fastforce
  qed (auto simp add: Vs_def walk_reflexive)
qed

lemma reachability_split3:
  "\<lbrakk>reachable (insert {w, x} E) u v; w \<notin> Vs E; x \<notin> Vs E\<rbrakk> \<Longrightarrow> 
  reachable E u v \<or> reachable {{w, x}} u v"
  by(auto simp: reachable_def dest: path_can_be_split_3)

lemma unchanged_connected_component:
  assumes "u \<notin> C" "v \<notin> C" 
  shows "C \<in> connected_components E \<longleftrightarrow> C \<in> connected_components (insert {u, v} E)"
proof-

  text \<open>This is to cover two symmetric cases\<close>
  have unchanged_con_comp_2:
    "C \<in> connected_components E \<longleftrightarrow> C \<in> connected_components (insert {u, v} E)"
    if "u \<notin> C" "v \<notin> C" "u \<in> Vs E" "v \<notin> Vs E"
    for u v
  proof-
    note assms = that
    show ?thesis
    proof(rule iffI, goal_cases)
      case 1
      then obtain v' where *: "C = connected_component E v'" "v' \<in> Vs E"
        by (rule C_is_componentE)
      hence "v' \<in> Vs (insert {u, v} E)"
        by(simp add: Vs_def)
      moreover have "x \<in> C \<Longrightarrow> reachable (insert {u, v} E) v' x"for x
        using *
        by (auto intro: in_Vs_insert reachable_refl dest: reachable_subset elim!: in_connected_componentE)
      moreover have "reachable (insert {u, v} E) v' x \<Longrightarrow> x \<in> C" for x
        using * assms
        by (auto dest: reachability_split_2 intro!: in_connected_componentI)
      ultimately have "connected_component (insert {u,v} E) v' = C"
        by (rule connected_component_set)
      then show ?case
        using \<open>v' \<in> Vs (insert {u, v} E)\<close> connected_component_in_components
        by auto
    next
      case 2
      then obtain v' where *: "C = connected_component (insert {u, v} E) v'" "v' \<in> Vs (insert {u, v} E)"
        by (rule C_is_componentE)
      hence "v' \<in> Vs E"
        using assms in_own_connected_component
        by (fastforce elim: in_Vs_insertE)
      moreover have "reachable (insert {u, v} E) v' x \<Longrightarrow> reachable E v' x" for x
        using *(1) assms \<open>v' \<in> Vs E\<close>
        by (auto dest: in_connected_componentI reachable_subset reachability_split_2) 
      hence "x \<in> C \<Longrightarrow> reachable E v' x" for x
        using *
        by (auto simp: reachable_refl elim: in_connected_componentE)
      moreover have "reachable E v' x \<Longrightarrow> x \<in> C" for x
        using *
        by (auto simp: reachable_refl dest: reachable_subset intro: in_connected_componentI)
      ultimately have "connected_component E v' = C"
        by (rule connected_component_set)
      then show ?case
        using \<open>v' \<in> Vs E\<close> connected_component_in_components
        by auto
    qed
  qed

  show ?thesis
  proof(cases \<open>u \<in> Vs E\<close>)
    assume "u \<in> Vs E"
    then show ?thesis
    proof(cases \<open>v \<in> Vs E\<close>)
      assume "v \<in> Vs E"
      note assms = assms \<open>u \<in> Vs E\<close> \<open>v \<in> Vs E\<close>
      show ?thesis
      proof(rule iffI, goal_cases)
        case 1
        then obtain v' where *: "C = connected_component E v'" "v' \<in> Vs E"
          by (rule C_is_componentE)
        hence "v' \<in> Vs (insert {u, v} E)"
          by(simp add: Vs_def)
        moreover have "x \<in> C \<Longrightarrow> reachable (insert {u, v} E) v' x"for x
          using * 
          by (auto intro: in_Vs_insert reachable_refl dest: reachable_subset
              elim!: in_connected_componentE)
        moreover have "reachable (insert {u, v} E) v' x \<Longrightarrow> x \<in> C" for x
          using *(1) assms
          by (auto dest: reachability_split intro!: in_connected_componentI)
        ultimately have "connected_component (insert {u,v} E) v' = C"
          by (rule connected_component_set)
        then show ?case
          using \<open>v' \<in> Vs (insert {u, v} E)\<close> connected_component_in_components
          by auto
      next
        case 2
        then obtain v' where *: "C = connected_component (insert {u, v} E) v'"
                                "v' \<in> Vs (insert {u, v} E)"
          by (rule C_is_componentE)
        hence "v' \<in> Vs E"
          using assms
          by (auto elim: in_Vs_insertE)
        moreover have "x \<in> C \<Longrightarrow> reachable E v' x" for x    
          using assms \<open>v' \<in> Vs E\<close>
          by (auto simp: *(1) elim!: in_connected_componentE 
              dest!: reachability_split dest: in_connected_componentI reachable_subset
              intro: reachable_refl)
        moreover have "reachable E v' x \<Longrightarrow> x \<in> C" for x
          using *
          by (auto dest: reachable_subset in_connected_componentI)
        ultimately have "connected_component E v' = C"
          by (rule connected_component_set)
        then show ?case
          using \<open>v' \<in> Vs E\<close> connected_component_in_components
          by auto
      qed

    next
      assume "v \<notin> Vs E"
      show ?thesis
        using unchanged_con_comp_2[OF assms \<open>u \<in> Vs E\<close> \<open>v \<notin> Vs E\<close>]
        .
    qed
  next
    assume "u \<notin> Vs E"
    then show ?thesis
    proof(cases \<open>v \<in> Vs E\<close>)
      assume "v \<in> Vs E"
      show ?thesis
        using unchanged_con_comp_2[OF assms(2,1) \<open>v \<in> Vs E\<close> \<open>u \<notin> Vs E\<close>]
        by (subst insert_commute)
    next
      assume "v \<notin> Vs E"
      note assms = assms \<open>u \<notin> Vs E\<close> \<open>v \<notin> Vs E\<close>
      show ?thesis
      proof(rule iffI, goal_cases)
        case 1
        then obtain v' where *: "C = connected_component E v'" "v' \<in> Vs E"
          by (rule C_is_componentE)
        hence "v' \<in> Vs (insert {u, v} E)"
          by(simp add: Vs_def)
        moreover have "x \<in> C \<Longrightarrow> reachable (insert {u, v} E) v' x"for x
          using *
          by (auto intro: reachable_refl in_Vs_insert dest: reachable_subset elim!: in_connected_componentE)
        moreover have "x \<in> C" if "reachable (insert {u, v} E) v' x" for x
        proof-
          have "\<not> reachable {{u, v}} v' x"
            using * assms \<open>u \<notin> Vs E\<close> \<open>v \<notin> Vs E\<close>
            by (auto dest: reachable_in_Vs(1) elim: vs_member_elim)
          thus ?thesis                                     
            using * that assms
            by (fastforce dest!: reachability_split3 simp add: in_connected_componentI)
        qed
        ultimately have "connected_component (insert {u,v} E) v' = C"
          by (rule connected_component_set)
        then show ?case
          using \<open>v' \<in> Vs (insert {u, v} E)\<close> connected_component_in_components
          by auto
      next
        case 2
        then obtain v' where *: "C = connected_component (insert {u, v} E) v'" "v' \<in> Vs (insert {u, v} E)"
          by (rule C_is_componentE)
        hence "v' \<in> Vs E"
          using assms in_own_connected_component
          by (force elim!: in_Vs_insertE)
        moreover have "reachable E v' x" if "reachable (insert {u, v} E) v' x" for x
        proof-
          have "\<not> reachable {{u, v}} v' x"
            using \<open>v' \<in> Vs E\<close> assms
            by (auto dest: reachable_in_Vs(1) elim: vs_member_elim)
          thus ?thesis
            using * assms that
            by (auto dest: reachability_split3)
        qed
        hence "x \<in> C \<Longrightarrow> reachable E v' x" for x
          using *
          by (auto simp: *(1) reachable_refl elim!: in_connected_componentE)
        moreover have "reachable E v' x \<Longrightarrow> x \<in> C" for x
          using *
          by (auto dest: reachable_subset in_connected_componentI)
        ultimately have "connected_component E v' = C"
          by (rule connected_component_set)
        then show ?case
          using \<open>v' \<in> Vs E\<close> connected_component_in_components
          by auto
      qed
    qed
  qed
qed

(*TODO rename connected_components_insert *)

lemma connected_components_union:
  assumes "Cu \<in> connected_components E" "Cv \<in> connected_components E"
  assumes "u \<in> Cu" "v \<in> Cv"
  shows "Cu \<union> Cv \<in> connected_components (insert {u, v} E)"
proof-
  have "u \<in> Vs (insert {u, v} E)" using assms(1) by (simp add: Vs_def)
  have "v \<in> Vs (insert {u, v} E)" using assms(1) by (simp add: Vs_def)

  have "reachable (insert {u, v} E) v x" if x_mem: "x \<in> Cu \<union> Cv" for x
  proof-
    have "reachable E u x \<or> reachable E v x"
      using x_mem assms
      by (auto dest: same_con_comp_reachable)
    then have "reachable (insert {u, v} E) u x \<or> reachable (insert {u, v} E) v x"
      by (auto dest: reachable_subset)
    thus ?thesis
      using edges_reachable[where E = "insert {u,v} E"]
      by (auto dest: reachable_trans)
  qed

  moreover note * = connected_comp_verts_in_verts[OF \<open>u \<in> Cu\<close> \<open>Cu \<in> connected_components E\<close>]
          connected_comp_verts_in_verts[OF \<open>v \<in> Cv\<close> \<open>Cv \<in> connected_components E\<close>]
  hence "reachable (insert {u, v} E) v x \<Longrightarrow> x \<in> Cu \<union> Cv" for x
    by(auto dest: in_connected_componentI reachability_split
            simp: connected_components_closed'[OF \<open>u \<in> Cu\<close> \<open>Cu \<in> connected_components E\<close>]
                  connected_components_closed'[OF \<open>v \<in> Cv\<close> \<open>Cv \<in> connected_components E\<close>])

  ultimately have "Cu \<union> Cv = connected_component (insert {u, v} E) v"
    apply(intro connected_component_set[symmetric])
    by(auto intro: in_Vs_insert)
  thus ?thesis
    using \<open>v \<in> Vs (insert {u, v} E)\<close> 
    by(auto intro: connected_component_in_components)
qed

lemma connected_components_insert_2:
  assumes "Cu \<in> connected_components E" "Cv \<in> connected_components E"
  assumes "u \<in> Cu" "v \<in> Cv"
  shows "connected_components (insert {u, v} E) = 
           insert (Cu \<union> Cv) ((connected_components E) - {Cu, Cv})"
proof-
  have Cuvins: "Cu \<union> Cv \<in> connected_components (insert {u, v} E)"
    by (simp add: assms connected_components_union)
  have "C \<in> connected_components (insert {u, v} E)" 
    if in_comps: "C \<in> insert (Cu \<union> Cv) (connected_components E - {Cu, Cv})" for C
  proof-
    consider (Cuv) "C = (Cu \<union> Cv)" | (other) "C \<in> connected_components E" "C \<noteq> Cu" "C \<noteq> Cv"
      using in_comps
      by blast
    thus ?thesis
    proof cases
      case other
      then show ?thesis
        using assms
        apply(subst unchanged_connected_component[symmetric])
        by (auto dest: connected_components_closed'[where C = C]
            connected_components_closed'[where C = Cu]
            connected_components_closed'[where C = Cv])
    qed (simp add: Cuvins)
  qed
  moreover have "C \<in> insert (Cu \<union> Cv) ((connected_components E) - {Cu, Cv})"
    if in_comps: "C \<in> connected_components (insert {u, v} E)" for C
  proof-
    have "u \<in> C \<or> v \<in> C \<Longrightarrow> C = Cu \<union> Cv"
      using Cuvins in_comps connected_components_closed'[where C = C] \<open>u \<in> Cu\<close> \<open>v \<in> Cv\<close>
            connected_components_closed'[where C = "Cu \<union> Cv"]
      by blast
    moreover have "C \<in> connected_components E" if "u \<notin> C"
    proof(cases \<open>v \<in> C\<close>)
      case True
      then show ?thesis
        using in_comps \<open>u \<in> Cu\<close> calculation that
        by auto
    next
      case False
      then show ?thesis
        apply(subst unchanged_connected_component[where u = u and v = v])
        using that in_comps
        by auto
    qed
    ultimately show ?thesis
      using assms(3, 4) by blast
  qed
  ultimately show ?thesis
    by auto

qed

lemma connected_components_insert_1:
  assumes "C \<in> connected_components E" "u \<in> C" "v \<in> C"
  shows "connected_components (insert {u, v} E) = connected_components E"
  using assms connected_components_insert_2 by fastforce

lemma in_connected_component_in_edges: "v \<in> connected_component E u \<Longrightarrow> v \<in> Vs E \<or> u = v"
  by(auto simp: connected_component_def Vs_def dest: walk_endpoints(2) elim!: reachableE vs_member_elim)

lemma in_con_comp_has_walk: assumes "v \<in> connected_component E u" "v \<noteq> u"
  obtains p where "walk_betw E u p v"
  using assms
  by(auto simp: connected_component_def elim!: reachableE)

find_theorems "(\<subseteq>)" reachable

lemma con_comp_subset: "E1 \<subseteq> E2 \<Longrightarrow> connected_component E1 u \<subseteq> connected_component E2 u"
  by (auto dest: reachable_subset simp: connected_component_def)

lemma in_con_comp_insert: "v \<in> connected_component (insert {u, v} E) u"
  using edges_are_walks[OF insertI1]
  by (force simp add: connected_component_def reachable_def)

lemma connected_components_insert:
  assumes "C \<in> connected_components E" "u \<in> C" "v \<notin> Vs E"
  shows "insert v C \<in> connected_components (insert {u, v} E)"
proof-
  have "u \<in> Vs (insert {u, v} E)" by (simp add: Vs_def)
  moreover have "connected_component (insert {u, v} E) u = insert v C"
  proof(standard, goal_cases)
    case 1
    thus ?case
      using assms
      by (fastforce elim: in_con_comp_has_walk dest!: path_can_be_split_2
                    simp add: in_connected_componentI4 connected_comp_verts_in_verts)
  next
    case 2
    have "C = connected_component E u"
      by (simp add: assms connected_components_closed')
    then show ?case
      by(auto intro!: insert_subsetI con_comp_subset[simplified]
              simp add: in_con_comp_insert)
  qed
  ultimately show ?thesis 
    using connected_components_closed' 
    by (fastforce dest: own_connected_component_unique)
qed

lemma connected_components_insert_3:
  assumes "C \<in> connected_components E" "u \<in> C" "v \<notin> Vs E"
  shows "connected_components (insert {u, v} E) = insert (insert v C) (connected_components E - {C})"
proof-
  have un_con_comp: "insert v C \<in> connected_components (insert {u, v} E)"
    by (simp add: assms connected_components_insert)
  have "D \<in> connected_components (insert {u, v} E)" 
    if "D \<in> insert (insert v C) (connected_components E - {C})"
    for D
  proof-
    from that consider (ins) "D = insert v C" | (other) "D \<in> connected_components E" "D \<noteq> C"
      by blast
    thus ?thesis
    proof cases
      case other
      moreover hence "v \<notin> D"
        using assms
        by (auto intro: connected_comp_verts_in_verts) 
      moreover have "u \<notin> D"
        using other assms 
        by (auto dest: connected_components_closed') 
      ultimately show ?thesis
        by(auto dest: unchanged_connected_component)
    qed (simp add: un_con_comp)
  qed
  moreover have "D \<in> insert (insert v C) (connected_components E - {C})"
    if "D \<in> connected_components (insert {u, v} E)"
    for D
  proof-
    have "u \<in> D \<longleftrightarrow> D = insert v C"
      using that assms(2) un_con_comp
      by (fastforce dest: connected_components_closed'')
    moreover hence "u \<in> D \<longleftrightarrow> v \<in> D"
      using that un_con_comp
      by (auto dest: connected_components_eq')
    ultimately show ?thesis 
        using that assms(2)
        by (auto simp: unchanged_connected_component[symmetric])
    qed
  ultimately show ?thesis by blast
qed

lemma connected_components_insert_1':
  "\<lbrakk>u \<in> Vs E; v \<in> Vs E\<rbrakk> \<Longrightarrow> 
     connected_components (insert {u, v} E)
       = insert (connected_component E u \<union> connected_component E v)
                     ((connected_components E) - {connected_component E u, connected_component E v})"
  by (auto simp add: connected_components_insert_2 in_own_connected_component
           dest!: connected_component_in_components)

lemma connected_components_insert_2':
  "\<lbrakk>u \<in> Vs E; v \<notin> Vs E\<rbrakk> 
   \<Longrightarrow> connected_components (insert {u, v} E)
         = insert (insert v (connected_component E u)) (connected_components E - {connected_component E u})"
  by (fastforce simp add: connected_components_insert_3 in_own_connected_component
                dest!: connected_component_in_components)

(*TODO: replace with connected_components_insert_4 everywhere*)

lemma connected_components_insert_4:
  assumes "u \<notin> Vs E" "v \<notin> Vs E"
  shows "connected_components (insert {u, v} E) = insert {u, v} (connected_components E)"
proof-
  have connected_components_small:
    "{u, v} \<in> connected_components (insert {u, v} E)"
  proof-
    have "u \<in> Vs (insert {u, v} E)"
      by (simp add: Vs_def)
    moreover have "connected_component (insert {u, v} E) u = {u, v}"
    proof(intro connected_component_set, goal_cases)
      case 1
      then show ?case
        by (simp add: Vs_def)
    next
      case (2 x)
      then show ?case
        by (auto simp add: \<open>u \<in> Vs (insert {u, v} E)\<close> reachable_refl edges_reachable)
    next
      case (3 x)
      then show ?case
        using reachable_in_Vs(1)
        by (fastforce simp add: assms dest: reachability_split3 walk_betw_singletonD elim: reachableE)
    qed
    ultimately show ?thesis
      by (fastforce dest: connected_component_in_components)
  qed

  have "{u, v} \<in> connected_components (insert {u, v} E)"
    by (simp add: assms connected_components_small)
  hence "C \<in> insert {u, v} (connected_components E)"
    if "C \<in> connected_components (insert {u, v} E)"
    for C
  proof(cases "C = {u, v}")
    case False
    hence "u \<notin> C" "v \<notin> C"
      using \<open>{u, v} \<in> connected_components (insert {u, v} E)\<close> that
      by (auto dest: connected_components_eq')
    hence "C \<in> connected_components E"
      using that
      by (auto dest: unchanged_connected_component)
    thus ?thesis
      by simp
  qed simp
  moreover have "C \<in> connected_components (insert {u, v} E)"
    if "C \<in> insert {u, v} (connected_components E)"
    for C
  proof(cases "C = {u, v}")
    case True
    thus ?thesis
      by (simp add: \<open>{u, v} \<in> connected_components (insert {u, v} E)\<close>)
  next
    case False
    hence "u \<notin> C" "v \<notin> C"
      using \<open>{u, v} \<in> connected_components (insert {u, v} E)\<close> that assms
      by (force simp add: insert_commute connected_comp_verts_in_verts)+
    thus ?thesis
      using that 
      by (auto dest: unchanged_connected_component)
  qed 
  ultimately show ?thesis
    by auto
qed

lemma connected_components_insert_3':
  "\<lbrakk>u \<notin> Vs E; v \<notin> Vs E\<rbrakk>
   \<Longrightarrow> connected_components (insert {u, v} E) = insert {u, v} (connected_components E)"
  using connected_components_insert_4
  .

text \<open>Elimination rule for proving lemmas about connected components by induction on graph edges.\<close>

lemma in_insert_connected_componentE[case_names both_nin one_in two_in]:
  assumes "C \<in> connected_components (insert {u,v} E)"
    "\<lbrakk>u \<notin> Vs E; v \<notin> Vs E;
     C \<in> insert {u,v} (connected_components E)\<rbrakk>
     \<Longrightarrow> P"
    "\<And>u' v'.
     \<lbrakk>u' \<in> {u,v}; v' \<in> {u, v}; u' \<in> Vs E; v' \<notin> Vs E;
     C \<in> insert (insert v' (connected_component E u')) (connected_components E - {connected_component E u'})\<rbrakk>
     \<Longrightarrow> P"
    "\<lbrakk>u \<in> Vs E; v \<in> Vs E; connected_component E u \<noteq> connected_component E v;
     C \<in> insert (connected_component E u \<union> connected_component E v)
                     ((connected_components E) - {connected_component E u, connected_component E v})\<rbrakk>
     \<Longrightarrow> P"
    "C \<in> (connected_components E) \<Longrightarrow> P"
  shows "P"
proof(cases \<open>u \<in> Vs E\<close>)
  assume \<open>u \<in> Vs E\<close>
  show ?thesis
  proof(cases \<open>v \<in> Vs E\<close>)
    assume \<open>v \<in> Vs E\<close>
    show ?thesis
    proof(cases "connected_component E u = connected_component E v")
      assume \<open>connected_component E u = connected_component E v\<close>
      hence "connected_components (insert {u,v} E) = connected_components E"        
        using \<open>u \<in> Vs E\<close>
        by (subst connected_components_insert_1[OF connected_component_in_components])
           (auto intro!: in_own_connected_component)
      thus ?thesis
        apply -
        apply(rule assms(5))
        using assms(1)
        by simp
    next
      assume \<open>connected_component E u \<noteq> connected_component E v\<close>
      then show ?thesis
      apply(rule assms(4)[OF \<open>u \<in> Vs E\<close> \<open>v \<in> Vs E\<close>])
      using assms(1)
      apply(subst connected_components_insert_1'[OF \<open>u \<in> Vs E\<close> \<open>v \<in> Vs E\<close>, symmetric])
      .
    qed
  next
    assume \<open>v \<notin> Vs E\<close>
    show ?thesis
      apply(rule assms(3)[where u' = u and v' = v])
      using assms(1) \<open>u \<in> Vs E\<close> \<open>v \<notin> Vs E\<close>
      by (auto simp: connected_components_insert_2'[symmetric])
  qed
next
  assume \<open>u \<notin> Vs E\<close>
  show ?thesis
  proof(cases \<open>v \<in> Vs E\<close>)
    assume \<open>v \<in> Vs E\<close>
    show ?thesis
      apply(rule assms(3)[where u' = v and v' = u])
      using assms(1) \<open>u \<notin> Vs E\<close> \<open>v \<in> Vs E\<close>
      by (auto simp: connected_components_insert_2'[symmetric] insert_commute)
  next
    assume \<open>v \<notin> Vs E\<close>
    show ?thesis
      apply(rule assms(2)[OF \<open>u \<notin> Vs E\<close> \<open>v \<notin> Vs E\<close>])
      using assms(1)
      apply(subst connected_components_insert_3'[OF \<open>u \<notin> Vs E\<close> \<open>v \<notin> Vs E\<close>, symmetric])
      .
  qed
qed

lemma exists_Unique_iff: "(\<exists>!x. P x) \<longleftrightarrow> (\<exists>x. P x \<and> (\<forall>y. P y \<longrightarrow> y = x))"
  by auto

lemma degree_one_unique:
  assumes "degree E v = 1"
  shows "\<exists>!e \<in> E. v \<in> e"
  using assms
proof-
  from assms obtain e where "{e} = {e. v \<in> e} \<inter> E"
    by (fastforce simp only: degree_def elim!: card'_1_singletonE)
  thus ?thesis
    by (auto simp: exists_Unique_iff)
qed

lemma complete_path_degree_one_head_or_tail:
  assumes "path E p" "distinct p" "v \<in> set p" "degree E v = 1"
  shows "v = hd p \<or> v = last p"
proof(rule ccontr)
  assume "\<not> (v = hd p \<or> v = last p)"
  hence "v \<noteq> hd p" "v \<noteq> last p" by simp_all
  hence "degree (set (edges_of_path p)) v = 2"
    by (simp add: degree_edges_of_path_ge_2 assms(2) assms(3))
  hence "2 \<le> degree E v"
    using subset_edges_less_degree[OF path_edges_subset[OF assms(1)], where v = v]
    by presburger
  then show False
    using assms(4) not_eSuc_ilei0
    by simp
qed

(*
  The proof of the following theorem should be improved by devising an induction principle for
  edges and connected components.
*)

lemma gr_zeroI: "(x::enat) \<noteq> 0 \<Longrightarrow> 0 < x"
  by auto

lemma degree_neq_zeroI: "\<lbrakk>e \<in> E; v \<in> e\<rbrakk> \<Longrightarrow> degree E v \<noteq> 0"
  by (auto simp add: degree_def)

lemma exists_conj_elim_2_1: "\<lbrakk>\<And>x. \<lbrakk>P x; Q x\<rbrakk> \<Longrightarrow> V x; \<lbrakk>\<And>x. P x \<and> Q x \<Longrightarrow> V x\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_3_1: "\<lbrakk>\<And>x. \<lbrakk>P x; Q x; V x\<rbrakk> \<Longrightarrow> W x; \<lbrakk>\<And>x. P x \<and> Q x \<and> V x \<Longrightarrow> W x\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_4_1: "\<lbrakk>\<And>x. \<lbrakk>P x; Q x; V x; W x\<rbrakk> \<Longrightarrow> X x; \<lbrakk>\<And>x. P x \<and> Q x \<and> V x \<and> W x \<Longrightarrow> X x\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_2_2: "\<lbrakk>\<And>x y. \<lbrakk>P x y; Q x y\<rbrakk> \<Longrightarrow> V x y; \<lbrakk>\<And>x y. P x y \<and> Q x y \<Longrightarrow> V x y\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_3_2: "\<lbrakk>\<And>x y. \<lbrakk>P x y; Q x y; V x y\<rbrakk> \<Longrightarrow> W x y; \<lbrakk>\<And>x y. P x y \<and> Q x y \<and> V x y \<Longrightarrow> W x y\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_4_2: "\<lbrakk>\<And>x y. \<lbrakk>P x y; Q x y; V x y; W x y\<rbrakk> \<Longrightarrow> X x y; \<lbrakk>\<And>x y. P x y \<and> Q x y \<and> V x y \<and> W x y \<Longrightarrow> X x y\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_2_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z\<rbrakk> \<Longrightarrow> V x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<Longrightarrow> V x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_3_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z\<rbrakk> \<Longrightarrow> W x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<Longrightarrow> W x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_4_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z; W x y z\<rbrakk> \<Longrightarrow> X x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<and> W x y z \<Longrightarrow> X x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_5_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z; W x y z; X x y z\<rbrakk> \<Longrightarrow> Y x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<and> W x y z \<and> X x y z \<Longrightarrow> Y x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_5_3': "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z; W x y z; X x y z\<rbrakk> \<Longrightarrow> Y x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<and> W x y z \<and> X x y z \<Longrightarrow> Y x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_6_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z; W x y z; X x y z; Y x y z\<rbrakk> \<Longrightarrow> Z x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<and> W x y z \<and> X x y z \<and> Y x y z \<Longrightarrow> Z x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

method instsantiate_obtains =
  (match conclusion in "P" for P
     \<Rightarrow> \<open>(match premises in ass[thin]: "\<And>x. _ x \<Longrightarrow> P" \<Rightarrow> \<open>rule ass\<close>) |
         (match premises in ass[thin]: "\<And>x y. _ x y \<Longrightarrow> P" \<Rightarrow> \<open>rule ass\<close>)\<close>)

lemmas exists_conj_elims = exists_conj_elim_2_1 exists_conj_elim_3_1 exists_conj_elim_4_1
                           exists_conj_elim_2_2 exists_conj_elim_3_2 exists_conj_elim_4_2

lemma edge_mid_path:
  "path E (p1 @ [v1,v2] @ p2) \<Longrightarrow> {v1,v2} \<in> E"
  using path_suff
  by fastforce

lemma snoc_eq_iff_butlast':
  "ys = xs @ [x] \<longleftrightarrow> (ys \<noteq> [] \<and> butlast ys = xs \<and> last ys = x)"
  by fastforce

lemma neq_Nil_conv_snoc: "xs \<noteq> [] \<longleftrightarrow> (\<exists>x ys. xs = ys @ [x])"
  by (auto simp add: snoc_eq_iff_butlast')

lemma degree_2: "\<lbrakk>{u,v} \<in> E; {v,w} \<in> E; distinct [u,v]; u \<noteq> w; v \<noteq> w\<rbrakk> \<Longrightarrow>2 \<le> degree E v"
  using degree_insert[where a = "{u,v}" and E = "E - {{u,v}}"]
  using degree_insert[where a = "{v,w}" and E = "(E - {{u,v}}) - {{v,w}}"]
  by (auto simp: degree_def doubleton_eq_iff eval_enat_numeral one_eSuc split: if_splits)

lemma degree_3:
 "\<lbrakk>{u,v} \<in> E; {v,w} \<in> E; {v, x} \<in> E; distinct [u,v,w]; u \<noteq> x; v \<noteq> x; w \<noteq> x\<rbrakk> \<Longrightarrow> 3 \<le> degree E v"
  using degree_insert[where a = "{u,v}" and E = "E - {{u,v}}"]
  using degree_insert[where a = "{v,w}" and E = "(E - {{u,v}}) - {{v,w}}"]
  using degree_insert[where a = "{v,x}" and E = "((E - {{u,v}}) - {{v,w}}) - {{v, x}}"]
  by (auto simp: degree_def doubleton_eq_iff eval_enat_numeral one_eSuc split: if_splits)

lemma Hilbert_choice_singleton: "(SOME x. x \<in> {y}) = y"
  by force

lemma Hilbert_set_minus: "s - {y} \<noteq>{} \<Longrightarrow> y \<noteq> (SOME x. x \<in> s - {y})"
  by(force dest!: iffD2[OF some_in_eq])

lemma connected_components_empty: "connected_components {} = {}"
  by (auto simp: connected_components_def Vs_def)

theorem component_has_path_distinct:
  assumes "finite E" and
    "C \<in> connected_components E" and
    "\<And>v. v\<in>Vs E \<Longrightarrow> degree E v \<le> 2" and
    "\<And>e. e\<in>E \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "\<exists>p. path E p \<and> C = (set p) \<and> distinct p"
  using assms
proof(induction "E" arbitrary: C)    
  case (insert e E')
  then obtain u v where uv[simp]: "e = {u,v}" "u \<noteq> v"
    by (force elim!: exists_conj_elims)
  hence "u \<in> Vs (insert e E')" "v \<in> Vs (insert e E')"
    using insert
    by (auto simp: Vs_def)
  moreover have "degree (insert e E') u \<noteq> 0" "degree (insert e E') v \<noteq> 0"
    by(fastforce simp: degree_neq_zeroI[where e = e])+
  moreover have "\<lbrakk>x \<noteq>0; x \<noteq> 1; x \<noteq> 2\<rbrakk> \<Longrightarrow> 2 < x" for x::enat
    by (fastforce simp: eval_enat_numeral one_eSuc dest!: ileI1[simplified order_le_less] dest: gr_zeroI)  
  ultimately have degree_uv:
    "degree (insert e E') u \<le> 2" "degree (insert e E') v \<le> 2"
    by (auto simp: linorder_not_le[symmetric] simp del: \<open>e = {u,v}\<close>
        dest!: \<open>\<And>v'. v' \<in> Vs (insert e E') \<Longrightarrow> degree (insert e E') v' \<le> 2\<close>)

  have "v \<in> Vs E' \<Longrightarrow> degree E' v \<le> 2" for v
    using subset_edges_less_degree[where E' = E' and E = "insert e E'"]
    by (fastforce intro: dual_order.trans dest!: insert.prems(2) dest: in_Vs_insert[where e = e])
  then have IH: "C \<in> connected_components E' \<Longrightarrow> \<exists>p. path E' p \<and> C = set p \<and> distinct p"    
    for C
    by (auto intro: insert)

  have deg_3: False
    if "p1 \<noteq> []" "p2 \<noteq> []" "path E (p1 @ u' # p2)" "{u, v} \<in> E" "v' \<notin> set (p1 @ u' # p2)"
      "distinct (p1 @ u' # p2)" "u' \<in> {u,v}" "u \<noteq> v" "v' \<in> {u, v}"
      "degree E u' \<le> 2"
    for E p1 u' v' p2
  proof-
    obtain v1 p1' where [simp]: "p1 = p1' @ [v1]"
      using \<open>p1 \<noteq> []\<close>
      by (auto simp: neq_Nil_conv_snoc)
    moreover obtain v2 p2' where [simp]: "p2 = v2 # p2'"
      using \<open>p2 \<noteq> []\<close>
      by (auto simp: neq_Nil_conv)
    ultimately have "v1 \<noteq> v2"
      using \<open>distinct (p1 @ u' # p2)\<close> \<open>path E (p1 @ u' # p2)\<close> path_2 path_suff
      by fastforce+
    moreover have "{v1,u'} \<in> E" "{u',v2} \<in> E"
      using \<open>path E (p1 @ u' # p2)\<close> path_2 path_suff
      by fastforce+
    moreover have "v1 \<noteq> v" "v1 \<noteq> u" "v2 \<noteq> v" "v2 \<noteq> u"
      using \<open>u' \<in> {u,v}\<close> \<open>v' \<in> {u, v}\<close> \<open>distinct (p1 @ u' # p2)\<close> \<open>v' \<notin> set (p1 @ u' # p2)\<close>
        mem_path_Vs[OF \<open>path E (p1 @ u' # p2)\<close>] \<open>u \<noteq> v\<close>
      by fastforce+
    moreover have "{u', SOME x. x \<in> {u, v} - {u'}} = {u,v}"
    proof-
      have "{u,v} - {v} = {u}"
        using \<open>u \<noteq> v\<close>
        by auto
      thus ?thesis
        using \<open>u' \<in> {u, v}\<close> \<open>u \<noteq> v\<close>
        by (fastforce simp add: Hilbert_choice_singleton)
    qed
    moreover have "u' \<noteq> (SOME x. x \<in> {u, v} - {u'})"
      using \<open>u' \<in> {u,v}\<close> \<open>u \<noteq> v\<close>
      by (fastforce intro!: Hilbert_set_minus)
    ultimately have "3 \<le> degree E u'"
      using \<open>{u, v} \<in> E\<close> \<open>v' \<notin> set (p1 @ u' # p2)\<close> \<open>distinct (p1 @ u' # p2)\<close>
      by (intro degree_3[where u = v1 and w = v2 and x = "SOME x. x \<in> ({u,v} - {u'})"]) auto
    thus False
      using degree_uv \<open>u' \<in> {u,v}\<close> \<open>degree E u' \<le> 2\<close>
      by(auto simp add: eval_enat_numeral one_eSuc dest: order_trans[where z = "eSuc 1"])
  qed

  from \<open>C \<in> connected_components (insert e E')\<close>[simplified \<open>e = {u, v}\<close>]
  show ?case
  proof(elim in_insert_connected_componentE, goal_cases)
    case 1
    then show ?case
    proof(safe, goal_cases)
      case 1
      then show ?case
        using \<open>u \<noteq> v\<close> \<open>v \<in> Vs (insert e E')\<close> \<open>e = {u,v}\<close>
        by (fastforce intro!: exI[where x = "[u, v]"])
    qed (fastforce dest: IH intro: path_subset)
  next
    case (2 u' v')
    moreover obtain p where "path E' p" "(connected_component E' u') = set p" "distinct p"
      using \<open>u' \<in> Vs E'\<close>
      by (force elim!: exists_conj_elims intro: IH simp add: connected_component_in_components)
    moreover then obtain p1 p2 where [simp]: "p = p1 @ u' # p2" "u' \<notin> set p1"
      using in_own_connected_component iffD1[OF in_set_conv_decomp_first]
      by (force elim!: exists_conj_elims)
    moreover hence "u' \<notin> set p2"
      using \<open>distinct p\<close>
      by auto
    moreover have "v' \<notin> set (p1 @ u' # p2)"
      using \<open>v' \<notin> Vs E'\<close> mem_path_Vs[OF \<open>path E' p\<close> ]
      by auto
    ultimately have False
      if "p1 \<noteq> []" "p2 \<noteq> []"
      by (fastforce intro!: deg_3[OF that, where E = "insert e E'" and v' = v' and u' = u']
          intro!: insert(5) in_Vs_insert dest: path_subset[where E' = "insert e E'"])
    hence "p1 = [] \<or> p2 = []"
      by auto

    from "2"(5) show ?case
    proof(elim insertE[where a = C], goal_cases)
      case 1
      moreover from 2 have "path (insert e E') (v' # u' # p2)"
        using \<open>path E' p\<close>[simplified]
        by (fastforce intro: path_subset dest: path_suff)
      moreover from 2 have "path (insert e E') (p1 @ [u', v'])" if "p2 = []"
        using \<open>path E' p\<close>[simplified ] that 
        by (subst rev_path_is_path_iff, subst (asm) rev_path_is_path_iff) (auto intro: path_subset)

      ultimately show ?case
        using \<open>p1 = [] \<or> p2 = []\<close> \<open>distinct p\<close> \<open>u' \<notin> set p2\<close> mem_path_Vs \<open>path E' p\<close> "2"(1-4)
        by (force intro!: exI[where x = "if p1 = [] then  v' # u' # p2 else p1 @ [u', v']"]
            simp add: \<open>connected_component E' u' = set p\<close>)
    qed (fastforce dest: IH intro: path_subset)
  next
    case 3

    from \<open>connected_component E' u \<noteq> connected_component E' v\<close>
    have "v \<notin> connected_component E' u" "u \<notin> connected_component E' v"
      using connected_components_member_eq
      by (fastforce simp only:)+
    from \<open>connected_component E' u \<noteq> connected_component E' v\<close>
    have "connected_component E' u \<inter> connected_component E' v = {}"
      using connected_components_disj
      by(auto intro!: connected_component_in_components 3)

    {
      fix u'
      assume "u' \<in> {u,v}"
      then obtain v' where \<open>v' \<in> {u,v}\<close> \<open>u' \<noteq> v'\<close>
        using uv(2)
        by blast
      obtain p where i: "path E' p" "(connected_component E' u') = set p" "distinct p"
        using \<open>u \<in> Vs E'\<close> \<open>v \<in> Vs E'\<close> \<open>u' \<in> {u,v}\<close>
        by (force elim!: exists_conj_elims intro: IH simp add: connected_component_in_components)
      moreover then obtain p1 p2 where [simp]: "p = p1 @ u' # p2" "u' \<notin> set p1"
        using in_own_connected_component iffD1[OF in_set_conv_decomp_first]
        by (force elim!: exists_conj_elims)
      moreover hence "u' \<notin> set p2"
        using \<open>distinct p\<close>
        by auto
      moreover have "v' \<notin> set (p1 @ u' # p2)"
        using \<open>v \<notin> connected_component E' u\<close> \<open>u \<notin> connected_component E' v\<close>
          \<open>connected_component E' u' = set p\<close> \<open>u' \<in> {u,v}\<close> \<open>v' \<in> {u,v}\<close> \<open>u' \<noteq> v'\<close>
        by auto
      ultimately have False
        if "p1 \<noteq> []" "p2 \<noteq> []"
        using \<open>u' \<in> {u,v}\<close> \<open>v' \<in> {u,v}\<close> degree_uv
        by (intro deg_3[OF that, where E = "insert e E'" and v' = v' and u' = u']) 
          (force intro!: degree_uv(1) in_Vs_insert dest: path_subset[where E' = "insert e E'"])+
      hence "p1 = [] \<or> p2 = []"
        by auto
      hence "\<exists>p p1 p2. path E' p \<and> (connected_component E' u') = set p \<and> distinct p \<and>
                       p = p1 @ u' # p2 \<and> (p1 = [] \<or> p2 = [])"
        by (fastforce intro!: i intro: exI[where x = p])
    } note * = this

    obtain p p1 p2 where
      "path E' p" "(connected_component E' u) = set p" "distinct p" "(p1 = [] \<or> p2 = [])" and
      [simp]: "p = p1 @ u # p2"
      apply (elim exists_conj_elim_5_3)
      using *
      by blast

    obtain p' p1' p2' where
      "path E' p'" "(connected_component E' v) = set p'" "distinct p'" "(p1' = [] \<or> p2' = [])" and
      [simp]: "p' = p1' @ v # p2'"
      apply (elim exists_conj_elim_5_3)
      using *
      by blast
    from "3"(4) show ?case
    proof(elim insertE[where a = C], goal_cases)
      case 1
      define witness_p where
        "witness_p = 
               (if p1 = [] \<and> p1' = [] then
                  (rev p2 @ [u, v] @ p2')
                else if p1 = [] \<and> p2' = [] then
                  (rev p2 @ [u, v] @ rev p1')
                else if p2 = [] \<and> p1' = [] then
                  (p1 @ [u, v] @ p2')
                else if p2 = [] \<and> p2' = [] then
                  (p1 @ [u, v] @ rev p1')
                else
                  undefined)"

      from \<open>p1 = [] \<or> p2 = []\<close> \<open>p1' = [] \<or> p2' = []\<close> have "path (insert e E') witness_p"
        using \<open>path E' p\<close> \<open>path E' p'\<close>
        by (auto intro!: path_subset[where E' = "(insert {u, v} E')"]
            path_concat[where p = "p1 @ [u]" and q = "u # v # rev p1'", simplified]
            path_concat[where p = "rev p2 @ [u]" and q = "u # v # p2'", simplified]
            path_concat[where p = "rev p2 @ [u]" and q = "u # v # rev p1'", simplified]
            path_concat[where p = "p1 @ [u]" and q = "u # v # []", simplified]
            path_concat[where p = "p1 @ [u]" and q = "u # v # p2'", simplified]
            simp: rev_path_is_path_iff[where p = "(rev p2 @ [u])"]
            rev_path_is_path_iff[where p = "(rev p2 @ [u, v])"]
            rev_path_is_path_iff[where p = "(v # rev p1')"]
            witness_p_def
            split: if_splits)
      moreover from \<open>p1 = [] \<or> p2 = []\<close> \<open>p1' = [] \<or> p2' = []\<close> have "distinct witness_p"
        using \<open>distinct p\<close> \<open>distinct p'\<close>
          \<open>(connected_component E' u) = set p\<close>
          \<open>v \<notin> connected_component E' u\<close>
          \<open>(connected_component E' v) = set p'\<close>
          \<open>u \<notin> connected_component E' v\<close>
          \<open>connected_component E' u \<inter> connected_component E' v = {}\<close>
        by (fastforce simp: witness_p_def  split: if_splits)
      moreover from \<open>p1 = [] \<or> p2 = []\<close> \<open>p1' = [] \<or> p2' = []\<close> have "C = set witness_p"
        using \<open>(connected_component E' u) = set p\<close> \<open>(connected_component E' v) = set p'\<close>
          \<open> C = connected_component E' u \<union> connected_component E' v\<close>
        by (fastforce simp: witness_p_def  split: if_splits)
      ultimately show ?case
        by auto
    qed (fastforce dest: IH intro: path_subset)
  qed (fastforce dest: IH intro: path_subset)
qed (auto simp: connected_components_empty intro!: exI[where x = "[]"])

subsection \<open>matchings and symmetric difference + accompanying auxiliary theory\<close>

definition matching where
  "matching M \<longleftrightarrow> (\<forall>e1 \<in> M. \<forall>e2 \<in> M. e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 = {})"

lemma matchingE:
  "matching M \<Longrightarrow> ((\<And>e1 e2. \<lbrakk>e1 \<in> M; e2 \<in> M; e1 \<noteq> e2\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: matching_def)

lemma matching_def2:
  "matching M \<longleftrightarrow> (\<forall>v \<in> Vs M. \<exists>!e\<in>M. v \<in> e)"
  unfolding matching_def Vs_def by blast

lemma matching_unique_match:
  "\<lbrakk>matching M; v \<in> e; v \<in> f; e \<in> M; f \<in> M\<rbrakk> \<Longrightarrow> e = f"
  by (auto simp: matching_def)

definition symmetric_diff (infixl "\<oplus>" 65) where
  "symmetric_diff s t \<equiv> (s - t) \<union> (t - s)"

lemma sym_diff_subset:
  "s \<oplus> s' \<subseteq> s \<union> s'"
  by (auto simp: symmetric_diff_def)

(* TODO: is this lemma needed? *)

lemma card3_subset:
  "card s \<ge> 3 \<Longrightarrow> \<exists>x y z. {x, y, z} \<subseteq> s \<and> x \<noteq> y  \<and> x \<noteq> z  \<and> y \<noteq> z"
  by(auto simp: eval_nat_numeral card_le_Suc_iff)

lemma finite_symm_diff:
  "\<lbrakk>finite s; finite t\<rbrakk> \<Longrightarrow> finite (s \<oplus> t)"
  by (auto simp: symmetric_diff_def)

lemma degree_matching_in_M:
  assumes "matching M" "v \<in> Vs M"
  shows "degree M v = 1"
proof-
  obtain e where edef: "v \<in> e" "e \<in> M"
    using assms
    by (fastforce simp: matching_def2)
  hence "{e} = {e. v \<in> e} \<inter> M"
    using assms edef
    by (auto simp: matching_def2)
  moreover have "card' {e} = 1" 
    by (simp add: card'_def one_eSuc enat_0)
  ultimately show ?thesis
    by (simp add: degree_def)
qed

lemma degree_matching:
  assumes "matching M"
  shows "degree M v \<le> 1"
proof(cases "v \<in> Vs M")
  case True thus ?thesis
    by (simp add: assms degree_matching_in_M)
next
  case False thus ?thesis
    by (simp add: degree_not_Vs)
qed

lemma degree_symm_diff:
  assumes "matching M" "matching M'"
  shows "degree (M \<oplus> M') v \<le> 2"
proof-
  have "{e. v \<in> e} \<inter> ((M - M') \<union> (M' - M)) \<subseteq> ({e. v \<in> e} \<inter> M) \<union> ({e. v \<in> e} \<inter> M')"
    by blast
  hence "degree (M \<oplus> M') v \<le> degree (M \<union> M') v"
    by (simp add: card'_mono Int_Un_distrib degree_def symmetric_diff_def)
  also have "... \<le> degree M v + degree M' v"
    by (simp add: Int_Un_distrib card'_def card_Un_le degree_def)
  also have "... \<le> degree M v + 1"
    using degree_matching[OF \<open>matching M'\<close>]
    by auto
  also have "... \<le> 2"
    using degree_matching[OF \<open>matching M\<close>]
    by (subst one_add_one[symmetric]) (fastforce intro!:  add_right_mono)
  finally show ?thesis .
qed

subsection\<open>Direction 1 of Berge\<close>
text\<open>If there is a bigger matching, then there is an augmenting path\<close>

lemma smaller_matching_less_members:
  assumes "finite E" "card E < card E'"
  shows "card ((E \<oplus> E') \<inter> E) < card ((E \<oplus> E') \<inter> E')"
proof-
  have "card ((E \<oplus> E') \<inter> E) = card (E - E')"
    by (auto intro: HOL.arg_cong[where f = card] simp: symmetric_diff_def)
  moreover have "card ((E \<oplus> E') \<inter> E') = card (E' - E)"
    by (auto intro: HOL.arg_cong[where f = card] simp: symmetric_diff_def)
  moreover have "card (E - E') < card (E' - E)"
    using assms card.infinite
    by (fastforce intro!: card_less_sym_Diff)
  ultimately show "card ((E \<oplus> E') \<inter> E) < card ((E \<oplus> E') \<inter> E')"
    by simp
qed

lemma one_unbalanced_comp_edges:
  assumes finite: "finite E" and
          card_lt: "card E < card E'" and
          finite_conn_comps: "finite (connected_components (E \<oplus> E'))" and
          doubleton_edges: "\<forall>e\<in>(E \<oplus> E'). \<exists>u v. e = {u, v}"
  shows "\<exists>eC \<in> components_edges (E \<oplus> E'). card (eC \<inter> E) < card (eC \<inter> E')"
proof(intro Union_lt assms)
  have *: "(E \<oplus> E') \<inter> {{x, y} |x y. True} = (E \<oplus> E')" 
    using doubleton_edges
    by auto
  show "card (\<Union> (components_edges (E \<oplus> E')) \<inter> E) < card (\<Union> (components_edges (E \<oplus> E')) \<inter> E')"
    unfolding component_edges_partition *
    by(intro smaller_matching_less_members finite card_lt)
  show "\<forall>eC\<in>components_edges (E \<oplus> E'). \<forall>s'\<in>components_edges (E \<oplus> E'). eC \<noteq> s' \<longrightarrow> eC \<inter> s' = {}"
    unfolding components_edges_def
    using component_edges_disj
    by auto
  show "finite E'"
    using finite card_lt
    using card_gt_0_iff by fastforce
qed(auto simp add: components_edges_def finite_conn_comps)

lemma matchings_in_diff:
  assumes "matching M" "matching M'" "{a, b} \<in> M \<oplus> M'" "{b, c} \<in> M \<oplus> M'" "a \<noteq> c"
  shows "{a, b} \<in> M \<longleftrightarrow> {b, c} \<in> M'"
proof-
  have sym_def: "x \<in> M \<oplus> M' \<Longrightarrow> x \<in> M \<or> x \<in> M' \<and> (x \<in> M \<longrightarrow> x \<notin> M') \<and> (x \<in> M' \<longrightarrow> x \<notin> M)" for x
    unfolding symmetric_diff_def by blast
  have aneqc: "{a, b} \<noteq> {b, c}"
    by(auto simp: \<open>a \<noteq> c\<close> doubleton_eq_iff)
  hence notbothM: "\<not> ({a, b} \<in> M \<and> {b, c} \<in> M)" 
    using \<open>matching M\<close>
    by(fastforce simp: matching_def)
  from aneqc
  have notbothM': "\<not> ({a, b} \<in> M' \<and> {b, c} \<in> M')"
    using \<open>matching M'\<close>
    by(fastforce simp: matching_def)
  show ?thesis
  proof
    assume "{a, b} \<in> M"
    then show "{b, c} \<in> M'" using sym_def[OF assms(4)] notbothM by simp
  next
    assume "{b, c} \<in> M'"
    then show "{a, b} \<in> M" using sym_def[OF assms(3)] notbothM' by simp
  qed
qed

lemma matching_paths_alternate:
  assumes "path (M \<oplus> M') p" "matching M" "matching M'" "distinct (edges_of_path p)"
  shows "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<in> M') (edges_of_path p) \<or>
         alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path p)"
  using assms
proof(induction p rule: induct_list0123)
  case (list2 v v')
  then show ?case
    using distinct_edges_of_paths_cons sym_diff_subset
    by (fastforce simp add: alt_list_empty alt_list_step split: if_splits)
next
  case (list3 v v' v'' vs)
  have "v \<noteq> v''" using list3.prems(4) by auto
  from list3 consider
    "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<in> M') (edges_of_path (v'#v''#vs))"
    | "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path (v'#v''#vs))"
    by fastforce
  then show ?case
  proof cases
    case 1
    hence "{v', v''} \<in> M" by (simp add: alt_list_step)
    hence "{v, v'} \<in> M'"
      using path_2 list3.prems(1,4) matchings_in_diff[OF list3.prems(2,3)]
      by (fastforce simp: \<open>v\<noteq>v''\<close> insert_commute)
    thus ?thesis
      using "1" alt_list.simps
      by force
  next
    case 2
    hence "{v', v''} \<in> M'" by (simp add: alt_list_step)
    hence "{v, v'} \<in> M"
      using path_2 list3.prems(1,4) matchings_in_diff[OF list3.prems(2,3)]
      by (fastforce simp: \<open>v\<noteq>v''\<close> insert_commute)
    thus ?thesis using "2" alt_list.simps by force
  qed
qed (simp_all add: alt_list_empty)

(*
  Every edge in the set of edges belonging to the connected component with more edges from M'
  belongs to the edge path representing that connected component.
*)

definition component_path' where
  "component_path' E C \<equiv> (SOME p. path E p \<and> C = set p \<and> distinct p)"

lemma component_path'_works':
  "\<lbrakk>finite E; C \<in> connected_components E;
    \<And>v. v\<in>Vs E \<Longrightarrow> degree E v \<le> 2;
    \<And>e. e\<in>E \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v\<rbrakk> \<Longrightarrow>
    path E (component_path' E C) \<and> C = set (component_path' E C) \<and> distinct (component_path' E C)"
  unfolding component_path'_def
  apply(rule someI_ex)
  using component_has_path_distinct .

lemma component_path'_works:
  assumes "finite E" "C \<in> connected_components E" "\<And>v. v\<in>Vs E \<Longrightarrow> degree E v \<le> 2"
           "\<And>e. e\<in>E \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "path E (component_path' E C)" "set (component_path' E C) = C" "distinct (component_path' E C)"
  using component_path'_works'[OF assms]
  by auto

lemma rev_component_path'_works:
  assumes "finite E" "C \<in> connected_components E" "\<And>v. v\<in>Vs E \<Longrightarrow> degree E v \<le> 2"
           "\<And>e. e\<in>E \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "path E (rev (component_path' E C))" "set (rev (component_path' E C)) = C"
        "distinct (rev (component_path' E C))"
  using component_path'_works[OF assms]
  by (auto intro: rev_path_is_path)

lemma component_edges_subset:
  shows "component_edges E C \<subseteq> E"
  by (auto simp: component_edges_def)

lemma symm_diff_mutex:
  "\<lbrakk>x \<in> (s \<oplus> t); x \<in> s\<rbrakk> \<Longrightarrow> x \<notin> t"
  by (auto simp: symmetric_diff_def)

lemma edges_path_subset_edges:
  assumes "path E p" "set p \<subseteq> C"
  shows "set (edges_of_path p) \<subseteq> component_edges E C"
  using assms
  by (induction) (auto simp add: component_edges_def)

lemma degree_edges_of_path_ge_2_all:
  assumes "distinct p" "length p \<ge> 3" "v\<in>set p"
  shows "degree (set (edges_of_path (last p # p))) v \<ge> 2"
proof(cases "v = hd p \<or> v = last p")
  case True
  moreover obtain a a' a'' p' where p: "p = a # a' # a'' # p'"
    using assms(2)
    by(auto simp add: Suc_le_length_iff eval_nat_numeral)
  ultimately have "v = a \<or> v = last (a'' # p')"
    by auto
  moreover have "2 \<le> degree (set (edges_of_path (last p # p))) a"
  proof-
    have "last p \<noteq> a'" using assms(1) p by auto
    hence "{last p, a} \<noteq> {a, a'}" by (auto simp: doubleton_eq_iff)
    hence "2 \<le> degree {{last p, a}, {a, a'}} a"
      by (simp add: degree_insert eval_enat_numeral one_eSuc)
    moreover have "{{last p, a}, {a, a'}} \<subseteq> set (edges_of_path (last p # p))"
      by (simp add: p)
    ultimately show ?thesis
      using order.trans 
      by (force dest!: subset_edges_less_degree[where v = a])
  qed
  moreover have "2 \<le> degree (set (edges_of_path (last p # p))) (last (a'' # p'))"
  proof-
    obtain u where u: "{u, last (a'' # p')} \<in> set (edges_of_path (a' # a'' # p'))" "u \<in> set (a' # a'' # p')"
      by (elim exists_conj_elims, rule exE[OF last_in_edge]) force
    hence "{u, last (a'' # p')} \<noteq> {a, last (a'' # p')}"
      using assms(1) u
      by (auto simp add: p doubleton_eq_iff)
    hence "2 \<le> degree {{u, last (a'' # p')}, {a, last (a'' # p')}} (last (a'' # p'))"
      by (simp add: degree_insert eval_enat_numeral one_eSuc)
    moreover have "{{u, last (a'' # p')}, {a, last (a'' # p')}} \<subseteq> set (edges_of_path (last p # p))"
      using p u(1) by fastforce
    ultimately show ?thesis
      using order.trans
      by (fastforce dest!: subset_edges_less_degree[where v = "(last (a'' # p'))"])
  qed
  ultimately show ?thesis
    by fastforce
next
  case False
  hence "2 = degree (set (edges_of_path p)) v"
    by (simp add: assms(1) assms(3) degree_edges_of_path_ge_2)
  moreover have "set (edges_of_path p) \<subseteq> set (edges_of_path (last p # p))"
    by (cases p) fastforce+
  then show ?thesis
    by (simp add: \<open>2 = degree (set (edges_of_path p)) v\<close> subset_edges_less_degree)
qed

lemma degree_insert_leq: "degree G e \<le> degree (insert e' G) e"
  by (simp add: subset_edges_less_degree subset_insertI)

lemma in_singleton: "\<lbrakk>s = {x}; y \<in> s\<rbrakk> \<Longrightarrow> x = y"
  by auto

lemma all_edges_covered_long_proof:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_neq_edges: "\<And>e. e\<in>(M \<oplus> M') \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v" and
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')"
  shows "component_edges (M \<oplus> M') C \<subseteq> set (edges_of_path (component_path' (M \<oplus> M') C))"
proof(cases "C ={}")
  case True
  then show ?thesis
    using assms
    unfolding component_edges_def component_path'_def
    by simp
next
  case C_nempty: False
  show ?thesis
  proof(cases "card C = 1")
    case True
    then obtain u where "C = {u}"
      using card_1_singletonE by blast
    then show ?thesis
      using assms
      unfolding component_edges_def component_path'_def
      by auto
  next
    case False
    then have comp_ge_2: "card C \<ge> 2"
      by (simp add: C_nempty Suc_leI finite_comp order_less_le eval_nat_numeral)
    show ?thesis
    proof(safe; rule ccontr)                                          
      fix e
      assume ass: 
        "e \<in> component_edges (M \<oplus> M') C"
        "e \<notin> set (edges_of_path (component_path' (M \<oplus> M') C))"
      define vs where "vs \<equiv> (component_path' (M \<oplus> M') C)"
      define es where "es \<equiv> (edges_of_path (component_path' (M \<oplus> M') C))"
      have doubleton_edges: "\<exists>u v. e = {u,v} \<and> u \<noteq> v" if "e\<in>(M \<oplus> M')" for e
        using doubleton_neq_edges that
        by fastforce
      have deg_le_2: "degree (M \<oplus> M') v \<le> 2" if "v\<in> Vs (M \<oplus> M')" for v
        using matchings
        by (simp add: degree_symm_diff)
      note finite_bla = finite_symm_diff
      note comp_works = component_path'_works[OF finite_bla con_comp deg_le_2 doubleton_edges]
      show False    
      proof(cases "hd vs \<in> e \<and> last vs \<in> e")
        case T1: True
        moreover have "distinct vs"
          unfolding vs_def 
          using comp_ge_2
          by (auto intro!: comp_works)
        moreover have "length vs \<ge> 2"
          unfolding vs_def
          using comp_ge_2 card_length distinct_card[OF comp_works(3)]
          by (simp add: comp_works(2))
        ultimately have vpath_hd_neq_last: "hd vs \<noteq> last vs"
          by (auto simp: Suc_le_length_iff eval_nat_numeral split: if_splits)
        hence e: "e = {hd vs, last vs}"
          using doubleton_edges component_edges_subset ass(1) T1
          by fastforce
        show ?thesis
        proof(cases "(component_edges (M \<oplus> M') C = insert e (set es))")
          case T2: True
          have vs_ge2: "length vs \<ge> 2"
            using comp_ge_2 comp_works distinct_card
            by (fastforce simp: vs_def)
          define vs' where "vs' = (last vs # vs)"
          have *: "set (edges_of_path vs') = component_edges (M \<oplus> M') C"
            using vs_ge2
            by (auto simp: es_def e vs_def vs'_def T2 Suc_le_length_iff eval_nat_numeral)
          have horrid_lt_expr: 
            "length (filter (\<lambda>x. x \<in> M) (edges_of_path vs')) <
                length (filter (\<lambda>e. e \<in> M') (edges_of_path vs'))"
          proof-
            have "component_path' (M \<oplus> M') C \<noteq> []"
              using C_nempty comp_works(2)
              by fastforce
            hence "\<exists>v vs. component_path' (M \<oplus> M') C = v # vs"
              by(auto simp add: neq_Nil_conv)
            hence "distinct (edges_of_path vs')"
              using comp_works(3) ass(1,2) "*"
              by (auto simp: vs'_def vs_def e distinct_edges_of_vpath insert_absorb)
            hence "length (filter (\<lambda>x. x \<in> N) (edges_of_path vs')) = 
                     card (N \<inter> (component_edges (M \<oplus> M') C))"
              for N
              using *
              by (simp add: distinct_length_filter)
            then show ?thesis
              using more_M'_edges
              by auto
          qed
          moreover have horrid_eq_expr: "\<forall>x\<in>set (edges_of_path vs'). (x \<in> M') = (x \<notin> M)"
            using sym_diff_subset symm_diff_mutex component_edges_subset[where E = "M \<oplus> M'"]
            by (fastforce simp: *)
          moreover have "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path vs')"
          proof-
            have "path (M \<oplus> M') (last vs # vs)"
            proof-
              obtain a l where l: "vs = a # l"
                using vs_ge2
                by (auto simp: Suc_le_length_iff eval_nat_numeral)
              show ?thesis
              proof(cases l)
                case Nil
                then show ?thesis 
                  using l comp_ge_2 comp_works
                  by (auto simp: vs_def)
              next
                case l': (Cons a' l')

                show ?thesis
                  using e 
                  apply(simp add: l' l split: if_splits)
                  subgoal using \<open>e \<notin> set (edges_of_path (component_path' (M \<oplus> M') C))\<close> l l'
                    by (auto simp: vs_def)
                  subgoal apply(rule conjI)
                    subgoal using T2 component_edges_subset
                      by fastforce
                    subgoal using e ass l l' vs_def comp_works
                      by simp
                    done
                  done
              qed
            qed
            moreover have "distinct (edges_of_path vs)"
              by (simp add: component_path'_works(3) con_comp deg_le_2 distinct_edges_of_vpath
                            doubleton_edges finite_bla vs_def)
            hence "distinct (edges_of_path (last vs # vs))"
              using \<open>e \<notin> set (edges_of_path (component_path' (M \<oplus> M') C))\<close> e vs_ge2
              by (cases vs, auto simp: vs_def insert_commute)
            moreover with vs_ge2 
              have "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<in> M') (edges_of_path (last vs # vs)) \<or>
                 alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path  (last vs # vs))"
              by (intro calculation(1) matching_paths_alternate assms; simp add: vs_def )
            ultimately show ?thesis
              using alternating_list_gt_or horrid_eq_expr horrid_lt_expr vs'_def by blast
          qed
          ultimately have "hd (edges_of_path vs') \<in> M' \<and> last (edges_of_path vs') \<in> M'"
            by(intro alternating_list_gt; simp)
          moreover have "hd (edges_of_path vs') \<noteq> last (edges_of_path vs')"
            unfolding vs'_def
            apply(intro hd_edges_neq_last)
            using \<open>e \<notin> set (edges_of_path (component_path' (M \<oplus> M') C))\<close> e comp_works 
                  comp_ge_2 vpath_hd_neq_last
              by (auto simp: vs_def)
          moreover have "last vs' \<in> hd (edges_of_path vs')"
            using vs_ge2
            by (cases vs, auto simp add: vs'_def)
          moreover have "last vs' \<in> last (edges_of_path vs')"
            apply(subst rev_rev_ident[symmetric])
            apply(subst last_rev)
            apply(subst (3) rev_rev_ident[symmetric])
            apply(subst edges_of_path_rev)
            using vs_ge2
            by (auto simp add: vs'_def last_rev intro: hd_v_in_hd_e)
          ultimately have "degree M (last vs') \<ge> 2"
            using \<open>matching M'\<close>[unfolded matching_def2]                  
            by fastforce
          then show ?thesis
            using degree_matching[OF \<open>matching M\<close>] not_eSuc_ilei0
            by (fastforce simp add: eval_enat_numeral one_eSuc dest: order_trans)
        next
          case F2: False
          show ?thesis
          proof(cases "card C \<ge> 3")
            case T3: True
            obtain e' where e': "e' \<in> component_edges (M \<oplus> M') C" "e' \<notin> insert e (set es)"
              using F2
              unfolding es_def
              using edges_path_subset_edges comp_works(1,2) ass(1)
              by blast
            obtain u v where uv: "e' = {u, v}" "v \<in> C"
              using e'(1)[unfolded component_edges_def] doubleton_edges
              by auto
            have "3 \<le> degree (insert e' (insert e (set es))) v"
            proof-
              have "degree (insert e (set es)) x \<ge> 2" if "x \<in> C" for x
              proof-
                have rw: "insert e (set es) = set (edges_of_path((last vs) # vs))"
                proof-
                  obtain a l where "vs = a # l"
                    using component_path'_works(2)[OF finite_bla con_comp deg_le_2 doubleton_edges] 
                          uv(2)
                    by (cases vs, simp add: vs_def)
                  then show ?thesis
                    unfolding es_def vs_def e
                    by auto
                qed
                show ?thesis
                  using comp_works T3 distinct_card \<open>x \<in> C\<close>
                  by (fastforce simp: rw vs_def intro!: degree_edges_of_path_ge_2_all)
              qed
              then have "degree (insert e (set es)) v \<ge> 2"
                using uv
                by simp
              moreover have "v \<in> e'"
                using uv(1) by force
              ultimately show ?thesis
                using e'(2)
                by (auto simp: degree_insert eval_enat_numeral)
            qed
            moreover have "(insert e' (insert e (set es))) \<subseteq> component_edges (M \<oplus> M') C"
              using ass(1) e' edges_path_subset_edges comp_works
              by (auto simp: es_def e vs_def)
            ultimately have "3 \<le> degree (component_edges (M \<oplus> M') C) v"
              using  order_trans
              by (fastforce dest!: subset_edges_less_degree)
            moreover have "(component_edges (M \<oplus> M') C) \<subseteq> (M \<oplus> M')"
              unfolding component_edges_def
              by auto
            ultimately have "3 \<le> degree (M \<oplus> M') v"
              using order_trans
              by (fastforce dest!: subset_edges_less_degree)
            then have "(3 :: enat) \<le> 2"
              using degree_symm_diff[OF matchings(1) matchings(2)] order_trans
              by fastforce
            then show False by simp
          next
            case F3: False
            then have C2: "card C = 2"
              using comp_ge_2
              by simp
            moreover obtain u v where uv: "C = {u, v}" "u \<noteq> v"
              using C2 
              by (auto simp add: eval_nat_numeral dest!: card_eq_SucD)
            moreover hence "e = {u,v}"
              using ass(1)[unfolded component_edges_def] e vpath_hd_neq_last
              by force
            ultimately have "component_edges (M \<oplus> M') C = {{u, v}}"
              using ass(1)[unfolded component_edges_def] doubleton_neq_edges
              by (fastforce simp: doubleton_eq_iff component_edges_def)
            moreover have "set (edges_of_path (component_path' (M \<oplus> M') C)) \<subseteq> component_edges (M \<oplus> M') C"
              by (simp add: comp_works(1,2) edges_path_subset_edges)
            ultimately have "False"
              using F2 ass(1) 
              by (simp add: es_def)
            then show ?thesis .
          qed
        qed
      next
        case False
        then obtain u v where "e = {u, v}"" v \<in> C"" u \<in> C" "u \<noteq> v"
          using ass(1)[unfolded component_edges_def] doubleton_neq_edges[of e]
          by fastforce
        moreover hence "(v \<noteq> hd vs \<and> v \<noteq> last vs) \<or> (u \<noteq> hd vs \<and> u \<noteq> last vs)"
          using False
          by auto
        ultimately obtain u v where uv: "e = {u, v}"" v \<in> C"" u \<in> C" "v \<noteq> hd vs" "v \<noteq> last vs"
          by auto
        have "3 \<le> degree (insert e (set es)) v"
        proof-
          have "2 = degree (set es) x" 
            if "x \<in> C" "x \<noteq> hd (component_path' (M \<oplus> M') C)" 
               "x \<noteq> last (component_path' (M \<oplus> M') C)"
            for x
          proof-
            have rw: "(set es) = set (edges_of_path(vs))"
              unfolding es_def vs_def
              by simp
            show ?thesis
              unfolding rw vs_def
              using comp_works that
              by (fastforce intro: degree_edges_of_path_ge_2)
          qed
          then have "degree (set es) v \<ge> 2"
            using uv
            by (simp add: vs_def)
          moreover have "v \<in> e"
            using uv(1) by force
          ultimately show ?thesis
            using degree_insert ass(2) es_def
            by(auto simp add: eval_enat_numeral degree_insert)
        qed
        moreover have "(insert e (set es)) \<subseteq> component_edges (M \<oplus> M') C"
          using ass(1) edges_path_subset_edges comp_works
          by (auto simp: es_def vs_def)
        ultimately have "3 \<le> degree (component_edges (M \<oplus> M') C) v"
          by (fastforce dest!: subset_edges_less_degree dest: order.trans)
        moreover have "(component_edges (M \<oplus> M') C) \<subseteq> (M \<oplus> M')"
          by (auto simp: component_edges_def)
        ultimately have "3 \<le> degree (M \<oplus> M') v"          
          by (fastforce dest!: subset_edges_less_degree dest: order.trans)
        moreover have "degree (M \<oplus> M') v \<le> 2"
          by (force intro!: deg_le_2 con_comp connected_comp_verts_in_verts uv(2))
        find_theorems "enat (Suc _)"
        ultimately show False
          by (auto simp add: eval_enat_numeral one_eSuc dest: order.trans)
      qed
    qed
  qed
qed

lemma all_edges_covered_long_proof_eq:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_neq_edges: "\<And>e. e\<in>(M \<oplus> M') \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v" and
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')"
  shows "component_edges (M \<oplus> M') C = set (edges_of_path (component_path' (M \<oplus> M') C))"
  using assms
  apply(intro equalityI edges_path_subset_edges all_edges_covered_long_proof assms component_path'_works)
  subgoal
    by auto
  subgoal by (auto simp add: degree_symm_diff matchings(1) matchings(2))
  subgoal by auto
  subgoal apply (intro equalityD1 component_path'_works(2) assms)
    subgoal by (simp add: degree_symm_diff matchings(1) matchings(2))
    subgoal by auto
    done
  done

lemma con_comp_card_2:
  assumes con_comp: "C \<in> connected_components E"
  assumes finite_comp: "finite C"
  assumes doubleton_edges: "\<And>e. e\<in>E \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "card C \<ge> 2"
proof-
  obtain X where "X \<in> C" "X \<in> Vs E"
    using con_comp connected_comp_nempty connected_component_subs_Vs by blast
  then obtain F where "F \<in> E" "X \<in> F" unfolding Vs_def by blast
  then obtain Y where "X \<noteq> Y" "F = {X, Y}" using doubleton_edges by force
  hence "Y \<in> C"
    using \<open>F \<in> E\<close> \<open>X \<in> C\<close> con_comp 
    by (fastforce intro: in_connected_componentI4 dest: edges_are_walks)
  show "card C \<ge> 2"
    using finite_comp \<open>X \<in> C\<close> \<open>X \<noteq> Y\<close> \<open>Y \<in> C\<close>
    by(auto simp: eval_nat_numeral not_less_eq_eq[symmetric] dest: card_le_Suc0_iff_eq)
qed

lemma augmenting_path_exists_1_1_1:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_edges: "\<And>e. e\<in>(M \<oplus> M') \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v" and 
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')" and 
    comp_edges_contained: "set (edges_of_path (component_path' (M \<oplus> M') C)) = component_edges (M \<oplus> M') C"
  shows "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path (component_path' (M \<oplus> M') C))" (is ?g1)
        "hd (edges_of_path (component_path' (M \<oplus> M') C)) \<in> M' \<and>
         last (edges_of_path (component_path' (M \<oplus> M') C)) \<in> M'" (is ?g2)
proof-
  note comp_ge_2 = con_comp_card_2[OF con_comp finite_comp doubleton_edges]

  define vs where "vs = (component_path' (M \<oplus> M') C)"
  then have *: "set (edges_of_path vs) = component_edges (M \<oplus> M') C"
    using comp_edges_contained
    by simp
  have deg_le_2: "\<And>v. v\<in>Vs (M \<oplus> M') \<Longrightarrow> degree (M \<oplus> M') v \<le> 2"
    using matchings
    by (simp add: degree_symm_diff)
  note finite_bla = finite_symm_diff
  note comp_works = component_path'_works[OF finite_bla con_comp deg_le_2 doubleton_edges]
  have vs_ge2: "length vs \<ge> 2"
    using comp_ge_2 comp_works
    unfolding vs_def
    using distinct_card by fastforce
  have horrid_lt_expr: "length (filter (\<lambda>x. x \<in> M) (edges_of_path vs)) < length (filter (\<lambda>e. e \<in> M') (edges_of_path vs))"
  proof-
    have "distinct (edges_of_path vs)"
      by (auto simp: vs_def intro!: comp_works distinct_edges_of_vpath)
    then have "length (filter (\<lambda>x. x \<in> N) (edges_of_path vs)) = card (N \<inter> (component_edges (M \<oplus> M') C))"
      for N
      by (simp add: distinct_length_filter *)
    then show ?thesis
      using more_M'_edges
      by auto
  qed
  moreover have "e \<in> M \<oplus> M'" "e \<in> M \<union> M'"
    if "e \<in> component_edges (M \<oplus> M') C"
    for e
    using component_edges_subset sym_diff_subset that
    by fastforce+
  hence M_M'_comp: "\<forall>x\<in>set (edges_of_path vs). (x \<in> M') = (x \<notin> M)"
    by(auto dest!: symm_diff_mutex simp: *)
  moreover have "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path vs)"
  proof-
    have "path (M \<oplus> M') (vs)"
      unfolding vs_def
      using comp_works
      by simp
    moreover with vs_ge2
    have "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<in> M') (edges_of_path vs) \<or>
             alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path  vs)"
      using component_path'_works(3)[OF finite_bla con_comp deg_le_2 doubleton_edges]
      by (intro matching_paths_alternate assms) (simp add: vs_def distinct_edges_of_vpath)+
    ultimately show ?thesis
      using *
      using alternating_list_gt_or M_M'_comp horrid_lt_expr by blast
  qed
  thus ?g1 
    by (auto simp: vs_def)
  ultimately show ?g2
    by(intro alternating_list_gt) (simp add: vs_def)+
qed

text\<open>Defining an augmenting path\<close>

definition augmenting_path where
  "augmenting_path M p \<equiv> (length p \<ge> 2) \<and> alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)
                          \<and> hd p \<notin> Vs M \<and> last p \<notin> Vs M"
abbreviation "augpath E M p \<equiv> path E p \<and> distinct p \<and> augmenting_path M p"

lemma augmenting_path_feats:
  assumes "augmenting_path M p"
  shows "(length p \<ge> 2)" "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)" "hd p \<notin> Vs M" "last p \<notin> Vs M"
  using assms
  by (auto simp: augmenting_path_def)

lemma augmenting_pathE:
  "\<lbrakk>augmenting_path M p; \<lbrakk>(length p \<ge> 2); alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p); hd p \<notin> Vs M; last p \<notin> Vs M\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: augmenting_path_def)

lemma augmenting_path_last_edge_nin:
  assumes "augmenting_path M p"
  shows "last (edges_of_path p) \<notin> M"
proof- 
  have "last p \<in> last (edges_of_path p)"
    using assms
    by (simp add: augmenting_path_def last_v_in_last_e)
  then show ?thesis
    using augmenting_path_feats(4)[OF assms]
    by (fastforce simp: Vs_def)
qed

lemma augmenting_path_odd_length:
  assumes "augmenting_path M p"
  shows "odd (length (edges_of_path p))"
  using augmenting_path_last_edge_nin[OF assms] assms
  by (fastforce
            simp add: eval_nat_numeral Suc_le_length_iff edges_of_path_length'[where p = p]
                      augmenting_path_last_edge_nin
            dest!: alternating_list_even_last
            elim!: augmenting_pathE)

lemma augmenting_path_exists_1_1:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_edges: "\<And>e. e\<in>M\<oplus>M' \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v" "\<And>e. e\<in>M \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v" and 
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')" and 
    comp_edges_contained: "set (edges_of_path (component_path' (M \<oplus> M') C)) = component_edges (M \<oplus> M') C"
  shows "augmenting_path M (component_path' (M \<oplus> M') C)"
proof-
  note comp_ge_2 = con_comp_card_2[OF con_comp finite_comp doubleton_edges(1)]

  have deg_le_2: "\<And>v. v\<in>Vs (M \<oplus> M') \<Longrightarrow> degree (M \<oplus> M') v \<le> 2"
    using matchings
    by (simp add: degree_symm_diff)
  note finite_bla = finite_symm_diff
  define vs where "vs = (component_path' (M \<oplus> M') C)"
  then have f1: "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path vs)" and
    f2: "hd (edges_of_path vs) \<in> M'" "last (edges_of_path vs) \<in> M'"
    using augmenting_path_exists_1_1_1[OF assms(1-5,7-9), unfolded vs_def]
    by auto
  have *:"hd vs \<notin> Vs M"
    if 
      ass: "path (M \<oplus> M') (vs)"
      "set vs = C"
      "distinct vs"
      "edges_of_path vs = es"
      "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) es"
      "set es = component_edges (M \<oplus> M') C"
    for vs es
  proof(rule ccontr)
    obtain u v vs' where uv[simp]: "vs = u # v # vs'"
      using ass more_M'_edges nat_neq_iff
      apply(elim edges_of_path.elims)
      by auto
    assume "\<not> hd vs \<notin> Vs M"
    then have "hd vs \<in> Vs M" by simp
    then obtain w e where we[simp]: "e = {w, u}" "e \<in> M"
      using doubleton_edges
      by (force simp add: insert_commute Vs_def)
    show False
    proof(cases "e \<in> M'")
      case T1: True
      then have "w = v"
        using ass(4,5) matchings(2)
        by (fastforce elim: matchingE simp add: alt_list_step doubleton_eq_iff)
      moreover have "{u,v} \<in> (M \<oplus> M')"
        using ass(1)
        by (simp add: vs_def)
      ultimately show ?thesis
        using we(2) T1
        by (simp add: insert_commute symmetric_diff_def)
    next
      case F1 :False
      then have "e \<in> (M \<oplus> M')"
        using we
        by (simp add: symmetric_diff_def)
      hence "e \<in> component_edges (M \<oplus> M') C"
        using ass(2) in_con_comp_insert[where v = w and E = "(M \<oplus> M')" and u = u]
          connected_components_closed''[OF con_comp]
        by (auto simp add: insert_absorb insert_commute component_edges_def)
      hence "e \<in> set (edges_of_path vs)"
        using ass 
        by simp
      hence "w = v"
        using ass(3)
        by (fastforce dest: v_in_edge_in_path_gen)
      then show ?thesis
        using F1 ass(4,5)
        by (auto simp add: alt_list_step insert_commute)
    qed    
  qed
  have "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path vs)"
    using comp_edges_contained component_edges_subset contra_subsetD
    by (force simp add: vs_def dest!: symm_diff_mutex intro!: alt_list_cong_2[OF f1])
  moreover have "hd vs \<notin> Vs M"
    using *[OF component_path'_works[OF finite_bla con_comp deg_le_2 doubleton_edges(1)] _ f1[unfolded vs_def] comp_edges_contained]
    by (auto simp: vs_def)
  moreover have "last vs \<notin> Vs M"
  proof-
    have "edges_of_path vs \<noteq> []"
      using  comp_edges_contained more_M'_edges 
      by (auto simp: vs_def)
    hence "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path (rev vs))"
      using comp_edges_contained[symmetric] component_edges_subset f1 f2(2) 
      by (fastforce simp: edges_of_path_rev[symmetric] vs_def
          dest: symm_diff_mutex alternating_list_even_last
          intro: alt_list_rev f2 f1)+
    hence "hd (rev vs) \<notin> Vs M"
      by (intro *[unfolded vs_def[symmetric]]
          rev_component_path'_works[OF finite_bla con_comp deg_le_2 doubleton_edges(1),
                                       unfolded vs_def[symmetric]])
        (auto simp add: edges_of_path_rev[symmetric] comp_edges_contained vs_def)+
    then show ?thesis
      by (simp add: hd_rev)
  qed
  moreover have "2 \<le> length (component_path' (M \<oplus> M') C)"
    using component_path'_works(2,3)[OF finite_bla con_comp deg_le_2 doubleton_edges(1)]
      comp_ge_2
    by (fastforce dest: distinct_card)
  ultimately show ?thesis
    using component_path'_works(1)[OF finite_bla con_comp deg_le_2 doubleton_edges(1)]
    by (auto simp: augmenting_path_def vs_def)
qed

lemma distinct_singleton_set: "distinct xs \<Longrightarrow> set xs = {x} \<longleftrightarrow> xs = [x]"
  by (induction xs arbitrary:) (fastforce simp add: neq_Nil_conv intro: ccontr[where P = "_ = []"])+

lemma empty_iff_card_0: "finite s \<Longrightarrow> s = {} \<longleftrightarrow> card s = 0"
  by auto

lemma augmenting_path_exists_1:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: 
      "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_neq_edges: "\<And>e. e\<in>(M \<oplus> M') \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v"
                         "\<And>e. e\<in>M \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v" and
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')"
  shows "augpath (M \<oplus> M') M (component_path' (M \<oplus> M') C)" (is "?g1 \<and> ?g2 \<and> ?g3")
proof(intro conjI)
  have deg_le_2: "\<And>v. v\<in>Vs (M \<oplus> M') \<Longrightarrow> degree (M \<oplus> M') v \<le> 2"
    using matchings
    by (simp add: degree_symm_diff)
  note finite_bla = finite_symm_diff
  have doubleton_edges: "\<And>e. e\<in>(M \<oplus> M') \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
    by (simp add: doubleton_neq_edges)
  have "card C \<noteq> 1"
  proof(rule ccontr; subst (asm) not_not)
    assume ass: "card C = 1"
    then obtain v where v: "C = {v}"
      by(fastforce elim: card_1_singletonE)
    moreover have C_nempty: "C \<noteq> {}" 
      by (simp add: v)
    ultimately have lv: "(component_path' (M \<oplus> M') C) = [v]"
      using component_path'_works(2,3)[OF finite_bla con_comp deg_le_2 doubleton_edges]
      by (simp add: distinct_singleton_set)
    obtain e where e: "e \<in> (M \<oplus> M')" "v \<in> e"
      using con_comp v
      by (force simp add: connected_components_def connected_component_def Vs_def)
    then obtain u where u: "e = {u, v}" "u \<noteq> v"
      using doubleton_neq_edges(1) e by fastforce
    moreover have "u \<in> connected_component (M \<oplus> M') v"
      using e(1)
      by (auto simp: insert_commute u(1) intro!: in_connected_componentI edges_reachable)
    moreover have "C = connected_component (M \<oplus> M') v"
      using con_comp 
      by (auto simp: connected_components_closed' v)
    ultimately show False using v by auto
  qed
  have C_nempty: "C \<noteq> {}"
    using con_comp
    by (fastforce simp add: connected_components_def connected_component_def intro!: ccontr[where P = "_ = [] "])+
  have comp_ge_2: "card C \<ge> 2"
    using \<open>card C \<noteq> 1\<close> C_nempty 
    by (simp add: empty_iff_card_0[OF \<open>finite C\<close>])
  then show ?g3
    using augmenting_path_exists_1_1(1)[OF assms]
          all_edges_covered_long_proof_eq(1)[symmetric, OF assms(1,2,3,4,5) finite_comp finite_symm_diff]
    by auto
  show ?g1 ?g2
    using matchings
    by (auto intro!: component_path'_works[OF assms(8,3) degree_symm_diff assms(5)])
qed

lemma finite_con_comps:
  "finite (Vs E) \<Longrightarrow> finite (connected_components E)"
  by (auto simp: connected_components_def)

lemma Berge_1:
  assumes finite: "finite M" "finite M'" and
    matchings: "matching M" "matching M'" and
    lt_matching: "card M < card M'" and
    doubleton_neq_edges: 
      "\<And>e. e\<in>(M \<oplus> M') \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v"
      "\<And>e. e\<in>M \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "\<exists>p. augmenting_path M p \<and> path (M \<oplus> M') p \<and> distinct p"
proof-
  have finite_symm_diff: "finite (M \<oplus> M')"
    using finite
    by (simp add: finite_symm_diff)
  then have finiteVs: "finite (Vs (M \<oplus> M'))"
    using doubleton_neq_edges(1)
    by(auto simp: Vs_def)
  have "\<And>e. e\<in>M \<oplus> M' \<Longrightarrow> \<exists>u v. e = {u, v}"
    using doubleton_neq_edges
    by fastforce
  then obtain C where 
    con_comp:
      "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges:
      "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))"
    using one_unbalanced_comp_edges[OF finite(1) lt_matching finite_con_comps[OF finiteVs]]
    by (auto simp add: inf_commute components_edges_def)
  moreover have finite_comp: "finite C"
    using finiteVs connected_component_subs_Vs[OF con_comp]
    by (auto intro: rev_finite_subset)
  moreover note finite_symm_diff
  ultimately have "augpath (M \<oplus> M') M (component_path' (M \<oplus> M') C)"
    by(intro augmenting_path_exists_1 assms; auto)+
  then show ?thesis
    by auto
qed

subsection\<open>Direction 2 of Berge\<close>

text\<open>An augmenting path can be used to construct a larger matching.\<close>

lemma matching_delete:
  assumes "matching M"
  shows "matching (M - N)"
  using assms
  unfolding matching_def by blast

lemma matching_insert:
  assumes "e \<inter> (Vs M) = {}" "matching M"
  shows "matching (insert e M)"
  using assms
  unfolding Vs_def matching_def by blast

lemma symmetric_difference_assoc: "A \<oplus> (B \<oplus> C) = (A \<oplus> B) \<oplus> C"
  unfolding symmetric_diff_def by blast

lemma symm_diff_is_matching:
  assumes 
    "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)"
    "matching M"
    "hd p \<notin> Vs M"
    "length p \<ge> 2 \<and> even (length p) \<Longrightarrow> last p \<notin> Vs M"
    "distinct p"
  shows "matching (M \<oplus> set (edges_of_path p))"
  using assms
proof(induction p arbitrary: M rule: induct_list0123)
  case nil
  then show ?case by (simp add: symmetric_diff_def)
next
  case list1
  then show ?case by (simp add: symmetric_diff_def)
next
  case (list2 x y)
  have "\<nexists>e. e \<in> M \<and> x \<in> e"
    using Vs_def list2.prems(3)
    by fastforce
  moreover have "\<nexists>e. e \<in> M \<and> y \<in> e"
    using Vs_def list2.prems(4)
    by fastforce
  moreover have "z \<in> Vs (insert {x, y} M) \<Longrightarrow> z = x \<or> z = y \<or> z \<in> Vs M"
    for z
    by(auto simp: Vs_def)
  ultimately have "matching (insert {x, y} M)"
    using list2.prems(2)
    by (simp add: matching_def)
  moreover have "{x, y} \<notin> M" using \<open>\<nexists>e. e \<in> M \<and> x \<in> e\<close>
    by blast
  ultimately show ?case 
    by (simp add: symmetric_diff_def)
next
  case (list3 x y z ps)
  from list3.prems(1)
  have "{x, y} \<notin> M" "{y, z} \<in> M"
    by (simp_all add: alt_list_step)

  define M' where "M' \<equiv> insert {x, y} (M - {{y, z}})"
  have M'symmdiff: "M' = M \<oplus> {{x, y}, {y, z}}" unfolding symmetric_diff_def M'_def
    using \<open>{x, y} \<notin> M\<close> \<open>{y, z} \<in> M\<close>
    by fastforce

  have xysymmdiff: "set (edges_of_path (x#y#z#ps)) = {{x, y}, {y, z}} \<oplus> set (edges_of_path (z # ps))"
    using list3.prems(5) v_in_edge_in_path
    by (fastforce simp: symmetric_diff_def)

  have "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path (z # ps))"
    using list3.prems(1)
    by (simp add: alt_list_step)

  hence altlistM': "alt_list (\<lambda>e. e \<notin> M') (\<lambda>e. e \<in> M') (edges_of_path (z # ps))"
    apply (rule alt_list_cong)
    using list3.prems(5) v_in_edge_in_path
    by (force simp: M'_def)+

  have "x \<notin> Vs (M - {{y, z}})"
    using \<open>{y, z} \<in> M\<close> list3.prems(3)
    by (simp add: Vs_def)
  moreover have "y \<notin> Vs (M - {{y, z}})"
    using \<open>{y, z} \<in> M\<close> list3.prems(2)
    by (force simp: Vs_def matching_def)
  ultimately have "matching M'"
    by (simp add: matching_delete matching_insert list3.prems(2) M'_def)

  have "z \<notin> Vs M'"
  proof(rule ccontr, subst (asm) not_not)
    assume "z \<in> Vs M'"
    hence "z \<in> Vs (M - {{y, z}})"
      using list3.prems(5)
      by (fastforce simp: M'_def Vs_def)
    then obtain e where "z \<in> e" "e \<in> M" "e \<noteq> {y, z}"
      by (auto simp: Vs_def)
    thus False
      using \<open>{y, z} \<in> M\<close> list3.prems(2)
      by (force simp: matching_def)
  qed
  moreover have "last (z # ps) \<notin> Vs M'"
    if "2 \<le> length (z # ps)" "even (length (z # ps))"
  proof(rule ccontr, subst (asm) not_not)
    assume "last (z # ps) \<in> Vs M'"
    hence "last (z # ps) \<in> Vs M \<or> last (z # ps) \<in> {x, y}"
      by (force simp: M'_def Vs_def)
    then have "last (z # ps) \<in> {x, y}"
      using list3.prems(4) that
      by force
    thus False
      using list3.prems(5) last_in_set
      by (auto simp: distinct_length_2_or_more split: if_splits)
  qed
  moreover note \<open>matching M'\<close> altlistM' list3.prems(5)
  ultimately have "matching (M' \<oplus> set (edges_of_path (z # ps)))"
    using list3.IH(2)
    by fastforce
  then show ?case
    by(simp only: M'symmdiff xysymmdiff symmetric_difference_assoc)
qed

lemma condition_for_greatness:
  assumes "card (s \<inter> t) < card (s - t)" "finite t"
  shows "card t < card (t \<oplus> s)"
proof-
  have tsstinter: "(t - s) \<inter> (s - t) = {}" by blast

  have "card t = card ((t - s) \<union> (t \<inter> s))"
    by (simp add: Un_Diff_Int)
  also have "... = card (t - s) + card (t \<inter> s)"
    using assms(2)
    by (auto intro!: card_Un_disjoint)
  also have "... < card (t - s) + card (s - t)"
    by (simp add: assms(1) inf.commute)
  also have "... = card ((t - s) \<union> (s - t))"
    using assms order_less_trans
    by (fastforce intro!: card_Un_disjoint[symmetric])
  also have "... = card (t \<oplus> s)"
    by (simp add: symmetric_diff_def)
  finally show ?thesis .
qed

lemma last_edge_in_last_vert_in:
  assumes "length p \<ge> 2" "last (edges_of_path p) \<in> E"
  shows "last p \<in> Vs E"
  using Vs_def assms last_v_in_last_e by fastforce

lemma hd_edge_in_hd_vert_in:
  "\<lbrakk>length p \<ge> 2; hd (edges_of_path p) \<in> E\<rbrakk> \<Longrightarrow> hd p \<in> Vs E"
  using Vs_def hd_v_in_hd_e
  by fastforce

lemma distinct_length_filter_neg: 
  assumes "distinct xs"
 shows "card (set xs - M) = length (filter (\<lambda>e. e \<notin> M) xs)" (is "?lhs = ?rhs")
proof-
  have "?lhs = card (set (filter  (\<lambda>e. e \<notin> M) xs))"
    by (auto intro!: arg_cong[where f = card])
  also have "... = length (remdups (filter (\<lambda>e. e \<notin> M) xs))"
    by (auto simp: length_remdups_card_conv)
  also have "... = ?rhs"
    using \<open>distinct xs\<close>
    by auto
  finally show ?thesis
    by simp
qed

lemma new_matching_bigger:
  assumes "augmenting_path M p"
  assumes "distinct p"
  assumes "finite M"
  shows "card M < card (M \<oplus> set (edges_of_path p))"
proof-
  have dist: "distinct (edges_of_path p)"
    using assms(2)
    by (simp add: distinct_edges_of_vpath)
  have "length (filter (\<lambda>e. e \<notin> M) (edges_of_path p)) = length (filter (\<lambda>e. e \<in> M) (edges_of_path p)) + 1"
    using alternating_eq_iff_odd assms(1) augmenting_path_feats(2) augmenting_path_odd_length
    by blast
  then have "card (set (edges_of_path p) - M) = card (set (edges_of_path p) \<inter> M) + 1"
    using distinct_length_filter_neg[OF dist] distinct_length_filter[OF dist]
    by (simp add: inf_commute)
  then show ?thesis
    using condition_for_greatness[OF _ assms(3)]
    by simp
qed

lemma Berge_2:         
  assumes aug_path: "augmenting_path M p" "M \<subseteq> E" "path E p" "distinct p" and
    finite: "finite M" and
    matchings: "matching M"
  shows "matching (M \<oplus> set (edges_of_path p))" (is ?g1)
        "card M < card (M \<oplus> set (edges_of_path p))" (is ?g2)
        "(M \<oplus> set (edges_of_path p)) \<subseteq> E" (is ?g3)
proof-
  show ?g1
    by (auto intro: symm_diff_is_matching assms simp: aug_path[unfolded augmenting_path_def])
  show ?g2
    by (intro new_matching_bigger assms)
  show ?g3
    using path_edges_subset sym_diff_subset aug_path(2,3)
    by force
qed

theorem Berge:
  assumes matching: "finite M" "matching M" "M \<subseteq> E" and
    graph: "(\<forall>e\<in>E. \<exists>u v. e = {u,v} \<and> u \<noteq> v)"
    "finite (Vs E)"
  shows "(\<exists>p. augmenting_path M p \<and> path E p \<and> distinct p) =
            (\<exists>M' \<subseteq> E. matching M' \<and> card M < card M')"
proof
  assume "\<exists>p. augmenting_path M p \<and> path E p \<and> distinct p"
  then obtain p where "augmenting_path M p" "path E p" "distinct p"
    by blast
  then obtain M' where "M' \<subseteq> E" "matching M'" "card M < card M'"
    using Berge_2 matching
    by metis
  then show "\<exists>M'\<subseteq>E. matching M' \<and> card M < card M'"
    by blast
next
  assume "\<exists>M'\<subseteq>E. matching M' \<and> card M < card M'"
  then obtain M' where M': "M' \<subseteq> E" "matching M'" "card M < card M'"
    by blast
  then have finiteM': "finite M'"
    using card.infinite by force
  have MM'_subset: "M \<oplus> M' \<subseteq> E"
    using sym_diff_subset matching(3) M'(1)
    by fast
  have "\<And>e. e \<in> M \<oplus> M' \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v"
    using MM'_subset graph(1) by blast
  moreover have "\<And>e. e \<in> M \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v"
    using matching(3) graph(1)
    by blast
  ultimately obtain p where "augmenting_path M p" "path (M \<oplus> M') p" "distinct p"
    using Berge_1[OF matching(1) finiteM' matching(2) M'(2, 3)]
    by blast
  moreover then have "path E p"
    using path_subset MM'_subset
    by blast
  ultimately show "\<exists>p. augmenting_path M p \<and> path E p \<and> distinct p"
    by auto
qed

abbreviation "graph_matching E M \<equiv> matching M \<and> M \<subseteq> E"

lemma laterally_transfer_aug_path':
  assumes "card M = card M'"
  assumes matching: "graph_matching E M'" "finite M'"
  assumes matching': "graph_matching E M" "finite M" 
  assumes graph: "(\<forall>e\<in>E. \<exists>u v. e = {u,v} \<and> u \<noteq> v)" "finite (Vs E)"
  assumes augpath: "augpath E M p"
  obtains q where "augpath E M' q"
proof-
  from augpath
  obtain N where N_def: "N \<subseteq> E" "matching N" "card M < card N" using Berge matching' graph by metis
  hence "card M' < card N" using assms(1) by linarith
  then obtain q where "augpath E M' q" using Berge matching graph N_def(1, 2) by metis
  then show ?thesis using that by simp
qed

lemma laterally_transfer_aug_path:
  assumes "card M = card M'"
  assumes matching: "graph_matching E M'" "finite M'"
  assumes matching': "graph_matching E M" "finite M" 
  assumes graph: "(\<forall>e\<in>E. \<exists>u v. e = {u,v} \<and> u \<noteq> v)" "finite (Vs E)"
  shows "(\<exists>p. augpath E M p) \<longleftrightarrow> (\<exists>p. augpath E M' p)"
proof-
  from assms(1) have card': "card M' = card M" by simp
  show ?thesis
    using laterally_transfer_aug_path'[OF assms(1) matching matching' graph]
          laterally_transfer_aug_path'[OF card' matching' matching graph]
    by metis
qed

locale graph_matching_defs =
  graph_defs +
  fixes M :: "'a set set"

abbreviation "alt_path M p \<equiv> alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)"
abbreviation "rev_alt_path M p \<equiv> alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) (edges_of_path p)"

end