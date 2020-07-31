theory Automation
  imports Graph_Theory.Graph_Theory
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

lemma (in wf_digraph)
  assumes  "apath u p1 v" "v \<rightarrow> y" "trail y p2 x"
  shows "\<exists>e. awalk u (p1@e#p2) x"
  using assms
  using reachable_awalk unfolding trail_def apath_def apply(auto) sorry

lemma (in wf_digraph)
  assumes "v \<rightarrow>\<^sup>* y" "y \<rightarrow> x" "x \<rightarrow>\<^sup>+ v"
  shows "\<exists>c. cycle c"
  using assms unfolding cycle_def sorry


lemma (in wf_digraph)
  assumes "awalk u p v" "v \<rightarrow> x" "awalk x (p1#ps1) u"
  shows "\<exists>c. cycle c"
  using assms unfolding cycle_def sorry

lemma (in wf_digraph)
  assumes "v \<rightarrow>\<^sup>* x" "awalk x p y"
  shows "\<mu> w v y < \<infinity>"
  sorry

text \<open>
  In general, the automation does not seem to work so well if you mix reachability and awalks.
\<close>

end