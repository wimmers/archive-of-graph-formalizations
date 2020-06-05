theory Ports_Overview
  imports
    "../Undirected_Graphs/summary1"
    Berge_to_DDFS
    "../Directed_Graphs/Digraph_Summary"
    Noschinski_to_DDFS
    "../TA_Graphs/TA_Graph_Summary"
    TA_Graph_to_DDFS
begin

text \<open>Vertex set\<close>
thm Vs_def \<comment> \<open>Berge\<close>
thm dVs_def \<comment> \<open>DDFS\<close>
term verts \<comment> \<open>Digraph\<close>
thm Graph_Defs.vertices_def \<comment> \<open>TA_Graph\<close>

text \<open>Path (vertex walks)\<close>
term path \<comment> \<open>Berge: not distinct\<close>
term dpath \<comment> \<open>DDFS: not distinct\<close>
term vwalk \<comment> \<open>Digraph: No empty walks!\<close>
term Graph_Defs.steps \<comment> \<open>TA_Graph: No empty walks!\<close>

text \<open>Edges in a path\<close>
term edges_of_path \<comment> \<open>Berge\<close>
term edges_of_dpath \<comment> \<open>DDFS\<close>
term vwalk_arcs \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

text \<open>Paths, edges and their interactions\<close>
thm path_ball_edges \<comment> \<open>Berge\<close>
thm dpath_ball_edges \<comment> \<open>DDFS\<close>
lemma vwalk_ball_edges: \<comment> \<open>Digraph: this is not 100% equivalent\<close>
  assumes "vwalk p G" "(u,v) \<in> set (vwalk_arcs p)"
  obtains e where "e \<in> arcs G" "tail G e = u" "head G e = v"
  using assms
  by (auto dest!: subsetD)
 \<comment> \<open>TA_Graph\<close>

thm edges_of_path_index \<comment> \<open>Berge\<close>
thm edges_of_dpath_index \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm edges_of_path_length \<comment> \<open>Berge\<close>
thm edges_of_dpath_length \<comment> \<open>DDFS\<close>
thm vwalk_length_simp[simplified vwalk_length_def] \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm edges_of_path_for_inner \<comment> \<open>Berge\<close>
thm edges_of_dpath_for_inner edges_of_dpath_for_inner' \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm Berge.hd_edges_neq_last \<comment> \<open>Berge\<close>
thm Berge_to_DDFS.hd_edges_neq_last \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm path_edges_of_path_refl \<comment> \<open>Berge\<close>
thm dpath_edges_of_dpath_refl \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

text \<open>Distinctness\<close>
thm distinct_edges_of_vpath \<comment> \<open>Berge\<close>
thm distinct_edges_of_dpath \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm distinct_edges_of_paths_cons \<comment> \<open>Berge\<close>
thm distinct_edges_of_dpath_cons \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

text \<open>Tail, appending, concat\<close>
thm tl_path_is_path \<comment> \<open>Berge\<close>
thm tl_dpath_is_dpath \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph: non-emptiness\<close>
 \<comment> \<open>TA_Graph: non-emptiness\<close>

thm path_concat \<comment> \<open>Berge\<close>
thm dpath_concat \<comment> \<open>DDFS\<close>
thm vwalk_joinI_vwalk' vwalk_joinI_vwalk \<comment> \<open>Digraph\<close>
thm Graph_Defs.steps_append \<comment> \<open>TA_Graph\<close>

thm path_append \<comment> \<open>Berge\<close>
thm append_dpath \<comment> \<open>DDFS\<close>
lemma vwalk_append: "vwalk p G \<Longrightarrow> vwalk q G \<Longrightarrow> (last p, hd q) \<in> arcs_ends G \<Longrightarrow> vwalk (p @ q) G"
  by (simp add: vwalk_arcs_append vwalk_def) \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm edges_of_path_append \<comment> \<open>Berge\<close>
thm edges_of_dpath_append \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm edges_of_path_append_2 \<comment> \<open>Berge\<close>
thm edges_of_dpath_append_2 \<comment> \<open>DDFS\<close>
thm vwalk_arcs_append \<comment> \<open>Digraph, similar but more of a mix of the _2 and _3 lemmas\<close>
 \<comment> \<open>TA_Graph\<close>

thm edges_of_path_append_3 \<comment> \<open>Berge\<close>
thm edges_of_dpath_append_3 \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

text \<open>Path prefixes and suffixes\<close>
thm path_suff \<comment> \<open>Berge\<close>
thm append_dpath_suff \<comment> \<open>DDFS\<close>
thm vwalkI_append_r \<comment> \<open>Digraph\<close>
thm Graph_Defs.steps_appendD2 \<comment> \<open>TA_Graph\<close>

thm path_pref \<comment> \<open>Berge\<close>
thm append_dpath_pref \<comment> \<open>DDFS\<close>
thm vwalkI_append_l \<comment> \<open>Digraph\<close>
thm Graph_Defs.steps_appendD1 \<comment> \<open>TA_Graph\<close>

text \<open>Reversing\<close>
thm edges_of_path_rev \<comment> \<open>Berge\<close>
 \<comment> \<open>DDFS, not applicable\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm rev_path_is_path \<comment> \<open>Berge\<close>
 \<comment> \<open>DDFS, not applicable\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

text \<open>Subset/membership relations of paths and vertices\<close>
thm path_vertex_has_edge \<comment> \<open>Berge\<close>
thm dpath_vertex_has_edge \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
lemma vwalk_arcs_edges_of_dpath: "vwalk_arcs p = edges_of_dpath p"
  by (induction p rule: induct_list012) auto
lemma
  assumes "length p \<ge> 2" "v \<in> set p"
  obtains e u where "e \<in> set (vwalk_arcs p)" "e = (u,v) \<or> e = (v,u)"
  using assms by (auto intro: dpath_vertex_has_edge simp: vwalk_arcs_edges_of_dpath)
 \<comment> \<open>TA_Graph\<close>

thm v_in_edge_in_path \<comment> \<open>Berge\<close>
thm v_in_edge_in_dpath \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm v_in_edge_in_path_inj \<comment> \<open>Berge\<close>
thm v_in_edge_in_dpath_inj \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm v_in_edge_in_path_gen \<comment> \<open>Berge\<close>
thm v_in_edge_in_dpath_gen \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm mem_path_Vs \<comment> \<open>Berge\<close>
thm path_then_in_Vs \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph, by definition\<close>
 \<comment> \<open>TA_Graph, does not hold (isolated vertex)\<close>

thm Vs_subset \<comment> \<open>Berge\<close>
thm dVs_subset \<comment> \<open>DDFS\<close>
thm subgraph_imp_subverts \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm path_subset \<comment> \<open>Berge\<close>
thm dpath_subset \<comment> \<open>DDFS\<close>
thm vwalkI_subgraph \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm edges_of_path_Vs \<comment> \<open>Berge\<close>
thm edges_of_dpath_dVs \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm path_edges_subset \<comment> \<open>Berge\<close>
thm dpath_edges_subset \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph, by definition\<close>
 \<comment> \<open>TA_Graph\<close>

thm last_v_in_last_e \<comment> \<open>Berge\<close>
thm last_v_snd_last_e \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm hd_v_in_hd_e \<comment> \<open>Berge\<close>
thm hd_v_fst_hd_e \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm Berge.last_in_edge \<comment> \<open>Berge\<close>
thm Berge_to_DDFS.last_in_edge \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm edges_of_path_append_subset \<comment> \<open>Berge\<close>
thm edges_of_dpath_append_subset \<comment> \<open>DDFS\<close>
thm set_vwalk_arcs_append1 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

text \<open>Walks (start and end vertex)\<close>
thm walk_betw_def \<comment> \<open>Berge\<close>
term dpath_bet \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm nonempty_path_walk_between \<comment> \<open>Berge\<close>
thm nonempty_dpath_dpath_bet \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm walk_nonempty \<comment> \<open>Berge\<close>
thm dpath_bet_nonempty \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm walk_between_nonempty_path \<comment> \<open>Berge\<close>
thm dpath_bet_nonempty_dpath \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm walk_reflexive \<comment> \<open>Berge\<close>
thm dpath_bet_reflexive \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm walk_symmetric \<comment> \<open>Berge\<close>
 \<comment> \<open>DDFS, not applicable\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm walk_transitive \<comment> \<open>Berge\<close>
thm dpath_bet_transitive \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm walk_in_Vs \<comment> \<open>Berge\<close>
thm dpath_bet_in_dVs \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm walk_endpoints \<comment> \<open>Berge\<close>
thm dpath_bet_endpoints \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm walk_pref \<comment> \<open>Berge\<close>
thm dpath_bet_pref \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm walk_suff \<comment> \<open>Berge\<close>
thm dpath_bet_suff \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm edges_are_walks \<comment> \<open>Berge\<close>
thm edges_are_dpath_bet \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm walk_subset \<comment> \<open>Berge\<close>
thm dpath_bet_subset \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

thm induct_walk_betw \<comment> \<open>Berge\<close>
thm induct_dpath_bet \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>
 \<comment> \<open>TA_Graph\<close>

section\<open>Digraph\<close>
text \<open>Digraph -- arc walks, trails, paths\<close>
thm pre_digraph.awalkI_apath \<comment> \<open>Digraph\<close>
thm Noschinski_to_DDFS.awalkI_apath \<comment> \<open>DDFS\<close>
 \<comment> \<open>TA_Graph\<close>

thm wf_digraph.apath_awalk_to_apath \<comment> \<open>Digraph\<close>
thm apath_awalk_to_apath \<comment> \<open>DDFS\<close>
 \<comment> \<open>TA_Graph\<close>

thm wf_digraph.awalk_to_apath_induct \<comment> \<open>Digraph\<close>
thm awalk_to_apath_induct \<comment> \<open>DDFS\<close>
 \<comment> \<open>TA_Graph\<close>

thm wf_digraph.awalk_appendI \<comment> \<open>Digraph\<close>
thm awalk_appendI \<comment> \<open>DDFS\<close>
 \<comment> \<open>TA_Graph\<close>

thm wf_digraph.awalk_append_iff \<comment> \<open>Digraph\<close>
thm awalk_append_iff \<comment> \<open>DDFS\<close>
 \<comment> \<open>TA_Graph\<close>

text \<open>Digraph -- vertex walks\<close>
thm wf_digraph.awalk_imp_vwalk \<comment> \<open>Digraph\<close>
thm awalk_imp_dpath \<comment> \<open>DDFS\<close>
 \<comment> \<open>TA_Graph\<close>

text\<open>Digraph -- reachability with paths\<close>
thm wf_digraph.reachable_awalk \<comment> \<open>Digraph\<close>
thm reachable_awalk \<comment> \<open>DDFS\<close>
 \<comment> \<open>TA_Graph\<close>

thm wf_digraph.reachable_vwalk_conv \<comment> \<open>Digraph\<close>
thm reachable_dpath_iff \<comment> \<open>DDFS\<close>
thm Graph_Defs.reaches_steps_iff \<comment> \<open>TA_Graph\<close>

text\<open>Subgraphs\<close>
thm pre_digraph.reachable_mono \<comment> \<open>Digraph\<close>
thm reachable_mono \<comment> \<open>DDFS\<close>
thm Subgraph.reaches \<comment> \<open>TA_Graph\<close>

thm wf_digraph.subgraph_apath_imp_apath \<comment> \<open>Digraph\<close>
thm subgraph_apath_imp_apath \<comment> \<open>DDFS\<close>
 \<comment> \<open>TA_Graph\<close>

section\<open>TA_Graph\<close>
thm Graph_Defs.steps_remove_cycleE \<comment> \<open>TA_Graph\<close>
thm dpath_remove_cycleE \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>

thm Graph_Defs.steps_rotate \<comment> \<open>TA_Graph\<close>
thm dpath_rotate \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>

thm Graph_Defs.steps_alt_induct \<comment> \<open>TA_Graph\<close>
thm dpath_alt_induct \<comment> \<open>DDFS, note the additional premise for empty paths\<close>
 \<comment> \<open>Digraph\<close>

thm Graph_Defs.steps_append2 \<comment> \<open>TA_Graph\<close>
thm dpath_append2 \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>

thm Graph_Defs.steps_decomp \<comment> \<open>TA_Graph\<close>
thm dpath_decomp \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>

thm Graph_Defs.reaches1_steps_iff \<comment> \<open>TA_Graph\<close>
thm reachable1_dpath_iff \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>

thm Graph_Defs.reaches_steps_iff2 \<comment> \<open>TA_Graph\<close>
thm reachable_dpath_iff2 \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>

thm Subgraph.reaches1 \<comment> \<open>TA_Graph\<close>
thm subgraph_reachable1 \<comment> \<open>DDFS\<close>
 \<comment> \<open>Digraph\<close>

end