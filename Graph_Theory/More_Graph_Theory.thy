(* Author: Lukas Stevens *)

(* TODO: Add to Noschinski's AFP entry *)

section \<open>Additions to Lars Noschinski's Graph Library\<close>
theory More_Graph_Theory
  imports "Graph_Theory.Graph_Theory"
begin

lemma vwalkE2:
  assumes "vwalk p G"
  obtains u where "p = [u]" "u \<in> verts G"
    | u v es where "p = u # v # es" "(u,v) \<in> arcs_ends G" "vwalk (v # es) G"
  by (metis assms list.sel(1) vwalkE vwalk_consE vwalk_singleton vwalk_to_vpath.cases)

lemma (in wf_digraph) reachable_vwalk_conv2:
  "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<longleftrightarrow> (u = v \<and> u \<in> verts G \<or> (\<exists>vs. vwalk (u # vs @ [v]) G))"
  unfolding reachable_vwalk_conv
  apply (rule iffI)
   apply (elim exE conjE, erule vwalkE2, (simp; fail),
      metis last.simps last_snoc list.distinct(1) list.sel(1) rev_exhaust vwalk_Cons_Cons)
  apply force
  done


context pre_digraph
begin

definition
  "scc_graph = \<lparr>
    verts = sccs_verts,
    arcs = {(x, y). \<exists>a \<in> x. \<exists>b \<in> y. x \<noteq> y \<and> x \<in> sccs_verts \<and> y \<in> sccs_verts \<and> a \<rightarrow> b},
    tail = fst,
    head = snd
  \<rparr>"

interpretation scc_digraph: loopfree_digraph scc_graph
  by standard (auto simp: scc_graph_def)

lemmas scc_digraphI = scc_digraph.loopfree_digraph_axioms

end


context wf_digraph
begin

interpretation scc_digraph: loopfree_digraph scc_graph
  by (rule scc_digraphI)

lemma scc_graph_edgeE:
  assumes \<open>x \<rightarrow>\<^bsub>scc_graph\<^esub> y\<close> obtains a b where
    "a \<in> x" "b \<in> y" "a \<rightarrow> b" "x \<in> sccs_verts" "y \<in> sccs_verts" "x \<noteq> y"
    using assms by (force simp: scc_graph_def dest!: in_arcs_imp_in_arcs_ends)

lemma same_sccI:
  assumes "S \<in> sccs_verts" "x \<in> S" "x \<rightarrow>\<^sup>* y" "y \<rightarrow>\<^sup>* x"
  shows "y \<in> S"
  using assms by (auto simp: in_sccs_verts_conv_reachable)

lemma scc_graph_reachable1E:
  assumes \<open>x \<rightarrow>\<^sup>+\<^bsub>scc_graph\<^esub> y\<close> obtains a b where
    "x \<in> sccs_verts " "y \<in> sccs_verts " "x \<noteq> y" "a \<in> x" "b \<in> y" "a \<rightarrow>\<^sup>+ b"
  using assms
proof (atomize_elim, induction)
  case (base y)
  then show ?case
    by (auto elim!: scc_graph_edgeE)
next
  case (step y z)
  then obtain a b where IH: "x \<in> sccs_verts" "y \<in> sccs_verts" "a \<in> x" "b \<in> y" "a \<rightarrow>\<^sup>+ b" "x \<noteq> y"
    by auto
  from \<open>y \<rightarrow>\<^bsub>scc_graph\<^esub> z\<close> obtain b' c where *:
    "b' \<in> y" "c \<in> z" "b' \<rightarrow> c" "y \<in> sccs_verts" "z \<in> sccs_verts"
    by (elim scc_graph_edgeE)
  with \<open>b \<in> y\<close> have "b \<rightarrow>\<^sup>* b'"
    by (simp add: in_sccs_verts_conv_reachable)
  with \<open>b' \<rightarrow> c\<close> \<open>a \<rightarrow>\<^sup>+ b\<close> have "a \<rightarrow>\<^sup>+ c"
    using reachable1_reachable_trans by blast
  moreover have "x \<noteq> z"
  proof (rule ccontr, simp)
    assume "x = z"
    with \<open>a \<in> x\<close> \<open>c \<in> z\<close> \<open>x \<in> _\<close> have "c \<rightarrow>\<^sup>* a"
      by (simp add: in_sccs_verts_conv_reachable)
    with \<open>b \<rightarrow>\<^sup>* b'\<close> \<open>b' \<rightarrow> c\<close> have "b \<rightarrow>\<^sup>* a" \<comment> \<open>XXX: This should really be \<open>by simp\<close>\<close>
      by (meson reachable_adj_trans reachable_trans)
    with IH have "b \<in> x"
      by - (rule same_sccI, auto)
    with sccs_verts_disjoint IH show False
      by auto
  qed
  ultimately show ?case
    using IH * by auto
qed

end


locale dag = wf_digraph +
  assumes acyclic: "x \<rightarrow>\<^sup>+ x \<Longrightarrow> False"

locale fin_dag = fin_digraph + dag


context wf_digraph
begin

interpretation scc_digraph: loopfree_digraph scc_graph
  by (rule scc_digraphI)

interpretation scc_digraph: dag scc_graph
  by standard (auto elim: scc_graph_reachable1E)

lemmas scc_digraphI = scc_digraph.dag_axioms

end


context fin_digraph
begin

interpretation scc_digraph: dag scc_graph
  thm scc_digraphI
  by (rule scc_digraphI)

interpretation scc_digraph: fin_dag scc_graph
  apply standard
  unfolding scc_graph_def
  subgoal finite_verts
    by (simp add: finite_sccs_verts)
  subgoal finite_arcs
    using finite_sccs_verts
    by - (rule finite_subset[where B = "{(x, y). x \<in> sccs_verts \<and> y \<in> sccs_verts}"], auto)
  done

lemmas scc_digraphI = scc_digraph.fin_dag_axioms

end

subsection \<open>Helper lemmas for directed tree\<close>

lemma (in wf_digraph) awalk_not_distinct:
  assumes "finite (verts G)" and "awalk u p v" and "length p \<ge> card (verts G)"
  shows "\<not> distinct (awalk_verts u p)"
proof -
  have *: "length (awalk_verts u p) > length p"
    by (induction p arbitrary: u) auto

  show ?thesis
  proof(cases "length p = 0")
    case True
    with assms show ?thesis unfolding awalk_def by simp
  next
    case False
    with assms * have "length (awalk_verts u p) > card (verts G)"
      by auto
    moreover
    have "set (awalk_verts u p) \<subseteq> verts G" using assms(2) by blast
    ultimately show ?thesis using assms(1) 
      by (induction p arbitrary: u)
         (auto, metis card_subset_eq distinct_card less_antisym)
  qed
qed

lemma (in wf_digraph) awalk_del_vert:
  "\<lbrakk> awalk u p v; x \<notin> set (awalk_verts u p) \<rbrakk> \<Longrightarrow> pre_digraph.awalk (del_vert x) u p v"
proof(induction p arbitrary: u)
  case Nil
  then have "set (awalk_verts u []) = {u}" by auto
  with Nil have "x \<noteq> u" by simp
  moreover
  from Nil have "u = v" unfolding awalk_def by auto
  ultimately show ?case using Nil
    by (simp add: awalk_hd_in_verts pre_digraph.verts_del_vert
        wf_digraph.awalk_Nil_iff wf_digraph_del_vert)
next
  case (Cons a p)
  then obtain u' where u': "pre_digraph.awalk (del_vert x) u' p v"
    using awalk_Cons_iff by auto
  moreover
  from Cons.prems have "head G a \<noteq> x"
    using hd_in_awalk_verts(1) awalk_Cons_iff by auto
  ultimately show ?case using Cons
    by (auto simp: awalk_Cons_iff head_del_vert pre_digraph.del_vert_simps(2)
        tail_del_vert wf_digraph.awalk_Cons_iff wf_digraph_del_vert)
qed


text \<open>This is an alternative formulation of @{thm pre_digraph.arcs_del_vert}.\<close>
lemma (in pre_digraph) arcs_del_vert2:
  "arcs (del_vert v) = arcs G - in_arcs G v - out_arcs G v"
  using arcs_del_vert by force


lemma (in wf_digraph) sp_non_neg_if_w_non_neg:
  assumes w_non_neg: "\<forall>e \<in> arcs G. w e \<ge> 0"
  shows "\<mu> w u v \<ge> 0"
proof(cases "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v")
  case True
  have *: "awalk u p v \<Longrightarrow> awalk_cost w p \<ge> 0" for p
    by (simp add: pos_cost_pos_awalk_cost w_non_neg)
  then show ?thesis unfolding \<mu>_def
    by (metis (mono_tags, lifting) INF_less_iff ereal_less_eq(5) mem_Collect_eq not_less)
next
  case False
  then show ?thesis by (simp add: shortest_path_inf)
qed


end