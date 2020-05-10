theory DDFS_Summary
  imports DDFS
begin

text \<open>Summary of the graph formalization DDFS.\<close>
text \<open>A graph is a set of edges, where each edge is a pair. The vertices are defined implicitly.\<close>
thm dVs_def

text \<open>Paths are a list of vertices, they are defined via the inductive predicate \<^term>\<open>dpath\<close>. There
      are also paths with a defined start end end (\<^term>\<open>dpath_bet\<close>).\<close>

text \<open>Basic lemmas\<close>
thm path_then_edge path_then_in_Vs dpath_cons
thm hd_of_dpath_bet hd_of_dpath_bet' last_of_dpath_bet

text \<open>Induction principles\<close>
thm induct_pcpl induct_pcpl_2

text \<open>Appending paths\<close>
thm append_dpath_1 append_dpath_pref \<comment> \<open>identical\<close>
thm append_dpath_suff
thm append_dpath

text \<open>Splitting paths\<close>
thm split_dpath

text \<open>Paths with start and end\<close>
thm dpath_bet_cons
thm dpath_bet_cons_2
thm dpath_bet_snoc
thm dpath_bet_dpath

text \<open>Edges and paths\<close>
thm dpath_snoc_edge dpath_snoc_edge'
thm dpath_snoc_edge_2
thm dpath_append_edge

text \<open>Paths representing transitive relations\<close>
thm dpath_transitive_rel
thm dpath_transitive_rel'
end