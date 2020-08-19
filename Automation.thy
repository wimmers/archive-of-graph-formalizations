theory Automation
  imports Ports.Ports_Overview
begin

section \<open>Automation\<close>
text \<open>
  The purpose of this section is to collect use cases for proof automation in the graph library.
\<close>

subsection \<open>Noschinski\<close>

lemma (in wf_digraph) "u \<rightarrow>\<^sup>+ v \<Longrightarrow> v \<rightarrow>\<^sup>* y \<Longrightarrow> y \<rightarrow> x \<Longrightarrow> u \<rightarrow>\<^sup>+ x"
  using reachable1_reachable_trans by blast

lemma (in wf_digraph)
  assumes "awalk u p v" "v \<rightarrow>\<^sup>* y" "y \<rightarrow> x"
  shows "u \<rightarrow>\<^sup>* x" "\<exists>q. awalk u q x"
  using assms reachable_adj_trans reachable_awalk reachable_trans
   apply -
  apply metis+
  done

lemma
  assumes  "apath G u p1 v" "(v, y) \<in> G" "trail G y p2 x"
  shows "\<exists>e. awalk G u (p1@e#p2) x"
  using assms
     Cons_eq_append_conv trail_def append_butlast_last_cancel arc_implies_awalk awalkI_apath awalk_appendI butlast.simps(2) not_Cons_self2
  by (metis Cons_eq_append_conv Noschinski_to_DDFS.trail_def append_butlast_last_cancel arc_implies_awalk awalkI_apath awalk_appendI butlast.simps(2) not_Cons_self2)

lemma
  assumes "awalk G u p1 v" "awalk G v p2 x" "awalk G x p3 u"
  shows "\<exists>u p. awalk G u p u"
  using assms
  by (meson awalk_appendI)

find_theorems awalk awalk_verts


lemma
  assumes "awalk G u p v" "reachable G v x" "awalk G x (p1#ps1) u"
  shows "\<exists>u p. awalk G u p u \<and> p \<noteq> []"
  using assms
  by (meson append_is_Nil_conv awalk_appendI list.simps(3) reachable_awalk)

lemma 
  assumes "dpath G [a,b]" "dpath G [b,c]"
  shows "dpath G [a,b,c]"
  using assms
  by auto

lemma 
  assumes "dpath_bet G vs1 a b" "dpath_bet G vs3 b c" "dpath_bet G xs4 c e"
  shows "\<exists>xs. dpath_bet G xs b e"
  by (meson assms(2) assms(3) dpath_bet_transitive)


lemma 
assumes "Berge.path E [a,b,c]" "Berge.path E [a,d]"
shows "Berge.path E [d,a,b,c]"
  by (metis assms(1) assms(2) insert_commute path_2)

lemma (in wf_digraph)
  assumes "v \<rightarrow>\<^sup>* x" "awalk x p y"
  shows "\<mu> w v y < \<infinity>"
  sorry

text \<open>
  In general, the automation does not seem to work so well if you mix reachability and awalks.
\<close>

end