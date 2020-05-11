theory Ports_Overview
  imports
    "../Undirected_Graphs/summary1"
    DDFS_Ports
begin

text \<open>Vertex set\<close>
thm Vs_def \<comment> \<open>Berge\<close>
thm dVs_def \<comment> \<open>DDFS\<close>

text \<open>Path\<close>
term path \<comment> \<open>Berge\<close>
term dpath \<comment> \<open>DDFS\<close>

text \<open>Edges in a path\<close>
term edges_of_path \<comment> \<open>Berge\<close>
term edges_of_dpath \<comment> \<open>DDFS\<close>

text \<open>Paths, edges and their interactions\<close>
thm path_ball_edges \<comment> \<open>Berge\<close>
thm dpath_ball_edges \<comment> \<open>DDFS\<close>

thm edges_of_path_index \<comment> \<open>Berge\<close>
thm edges_of_dpath_index \<comment> \<open>DDFS\<close>

thm edges_of_path_length \<comment> \<open>Berge\<close>
thm edges_of_dpath_length \<comment> \<open>DDFS\<close>

thm edges_of_path_for_inner \<comment> \<open>Berge\<close>
thm edges_of_dpath_for_inner edges_of_dpath_for_inner' \<comment> \<open>DDFS\<close>

thm Berge.hd_edges_neq_last \<comment> \<open>Berge\<close>
thm DDFS_Ports.hd_edges_neq_last \<comment> \<open>DDFS\<close>

thm path_edges_of_path_refl \<comment> \<open>Berge\<close>
thm dpath_edges_of_dpath_refl \<comment> \<open>DDFS\<close>

text \<open>Distinctness\<close>
thm distinct_edges_of_vpath \<comment> \<open>Berge\<close>
thm distinct_edges_of_dpath \<comment> \<open>DDFS\<close>

thm distinct_edges_of_paths_cons \<comment> \<open>Berge\<close>
thm distinct_edges_of_dpath_cons \<comment> \<open>DDFS\<close>

text \<open>Tail, appending, concat\<close>
thm tl_path_is_path \<comment> \<open>Berge\<close>
thm tl_dpath_is_dpath \<comment> \<open>DDFS\<close>

thm path_concat \<comment> \<open>Berge\<close>
thm dpath_concat \<comment> \<open>DDFS\<close>

thm path_append \<comment> \<open>Berge\<close>
thm append_dpath \<comment> \<open>DDFS\<close>

thm edges_of_path_append \<comment> \<open>Berge\<close>
thm edges_of_dpath_append \<comment> \<open>DDFS\<close>

thm edges_of_path_append_2 \<comment> \<open>Berge\<close>
thm edges_of_dpath_append_2 \<comment> \<open>DDFS\<close>

thm edges_of_path_append_3 \<comment> \<open>Berge\<close>
thm edges_of_dpath_append_3 \<comment> \<open>DDFS\<close>

text \<open>Path prefixes and suffixes\<close>
thm path_suff \<comment> \<open>Berge\<close>
thm append_dpath_suff \<comment> \<open>DDFS\<close>

thm path_pref \<comment> \<open>Berge\<close>
thm append_dpath_pref \<comment> \<open>DDFS\<close>

text \<open>Reversing\<close>
thm edges_of_path_rev \<comment> \<open>Berge\<close>
 \<comment> \<open>DDFS, not applicable\<close>

thm rev_path_is_path \<comment> \<open>Berge\<close>
 \<comment> \<open>DDFS, not applicable\<close>

text \<open>Subset/membership relations of paths and vertices\<close>
thm path_vertex_has_edge \<comment> \<open>Berge\<close>
thm dpath_vertex_has_edge \<comment> \<open>DDFS\<close>

thm v_in_edge_in_path \<comment> \<open>Berge\<close>
thm v_in_edge_in_dpath \<comment> \<open>DDFS\<close>

thm v_in_edge_in_path_inj \<comment> \<open>Berge\<close>
thm v_in_edge_in_dpath_inj \<comment> \<open>DDFS\<close>

thm v_in_edge_in_path_gen \<comment> \<open>Berge\<close>
thm v_in_edge_in_dpath_gen \<comment> \<open>DDFS\<close>

thm mem_path_Vs \<comment> \<open>Berge\<close>
thm path_then_in_Vs \<comment> \<open>DDFS\<close>

thm Vs_subset \<comment> \<open>Berge\<close>
thm dVs_subset \<comment> \<open>DDFS\<close>

thm path_subset \<comment> \<open>Berge\<close>
thm dpath_subset \<comment> \<open>DDFS\<close>

thm edges_of_path_Vs \<comment> \<open>Berge\<close>
thm edges_of_dpath_dVs \<comment> \<open>DDFS\<close>

thm path_edges_subset \<comment> \<open>Berge\<close>
thm dpath_edges_subset \<comment> \<open>DDFS\<close>

thm last_v_in_last_e \<comment> \<open>Berge\<close>
thm last_v_snd_last_e \<comment> \<open>DDFS\<close>

thm hd_v_in_hd_e \<comment> \<open>Berge\<close>
thm hd_v_fst_hd_e \<comment> \<open>DDFS\<close>

thm Berge.last_in_edge \<comment> \<open>Berge\<close>
thm DDFS_Ports.last_in_edge \<comment> \<open>DDFS\<close>

thm edges_of_path_append_subset \<comment> \<open>Berge\<close>
thm edges_of_dpath_append_subset \<comment> \<open>DDFS\<close>

text \<open>Walks (start and end vertex)\<close>
thm walk_betw_def \<comment> \<open>Berge\<close>
term dpath_bet \<comment> \<open>DDFS\<close>

thm nonempty_path_walk_between \<comment> \<open>Berge\<close>
thm nonempty_dpath_dpath_bet \<comment> \<open>DDFS\<close>

thm walk_nonempty \<comment> \<open>Berge\<close>
thm dpath_bet_nonempty \<comment> \<open>DDFS\<close>

thm walk_between_nonempty_path \<comment> \<open>Berge\<close>
thm dpath_bet_nonempty_dpath \<comment> \<open>DDFS\<close>

thm walk_reflexive \<comment> \<open>Berge\<close>
thm dpath_bet_reflexive \<comment> \<open>DDFS\<close>

thm walk_symmetric \<comment> \<open>Berge\<close>
 \<comment> \<open>DDFS, not applicable\<close>

thm walk_transitive \<comment> \<open>Berge\<close>
thm dpath_bet_transitive \<comment> \<open>DDFS\<close>

thm walk_in_Vs \<comment> \<open>Berge\<close>
thm dpath_bet_in_dVs \<comment> \<open>DDFS\<close>

thm walk_endpoints \<comment> \<open>Berge\<close>
thm dpath_bet_endpoints \<comment> \<open>DDFS\<close>

thm walk_pref \<comment> \<open>Berge\<close>
thm dpath_bet_pref \<comment> \<open>DDFS\<close>

thm walk_suff \<comment> \<open>Berge\<close>
thm dpath_bet_suff \<comment> \<open>DDFS\<close>

thm edges_are_walks \<comment> \<open>Berge\<close>
thm edges_are_dpath_bet \<comment> \<open>DDFS\<close>

thm walk_subset \<comment> \<open>Berge\<close>
thm dpath_bet_subset \<comment> \<open>DDFS\<close>

thm induct_walk_betw \<comment> \<open>Berge\<close>
thm induct_dpath_bet \<comment> \<open>DDFS\<close>
end