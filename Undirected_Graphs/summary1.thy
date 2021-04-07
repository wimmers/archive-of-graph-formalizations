theory summary1
  imports Berge
begin

text \<open>This is a summary of the graph library used for verifying the Blossom algorithm.\<close>

text \<open>In this library a graph is a set of sets of vertices, and thus, the set of vertices of the
      graph are defined implicitly, as follows:\<close>

thm Vs_def

text \<open>Graphs are defined using locales. A finite undirected graph is defined by the following
      locale\<close>

thm graph_abs_def

section \<open>Basic theory about paths:\<close>

text \<open>A (not simple) path is defined as the following inductive predicate:\<close>

term path

text \<open>There is also a function that extracts the list of edges forming a path:\<close>

term edges_of_path

text \<open>The following are theorems about paths, edges of path, and their interactions\<close>

thm path_ball_edges
thm edges_of_path_index
thm edges_of_path_length
thm edges_of_path_for_inner
thm hd_edges_neq_last
thm path_edges_of_path_refl

text \<open>distinctness of vertices and edges\<close>

thm distinct_edges_of_vpath
thm distinct_edges_of_paths_cons

text \<open>Tail of paths, appending, concating\<close>

thm tl_path_is_path
thm path_concat
thm path_append
thm edges_of_path_append
thm edges_of_path_append_2
thm edges_of_path_append_3

text \<open>Path prefixes and suffixes\<close>

thm path_suff
thm path_pref

text \<open>Reversing\<close>

thm edges_of_path_rev
thm rev_path_is_path

text \<open>Different subet/membership relations of paths and vertices\<close>

thm path_vertex_has_edge
thm v_in_edge_in_path
thm v_in_edge_in_path_inj
thm v_in_edge_in_path_gen
thm mem_path_Vs
thm Vs_subset
thm path_subset
thm edges_of_path_Vs
thm path_edges_subset
thm last_v_in_last_e
thm hd_v_in_hd_e
thm last_in_edge
thm edges_of_path_append_subset

section \<open>Similar theory as the above, but for walks, i.e. paths between specified vertices.\<close>

text \<open>Definition of a walk:\<close>

thm walk_betw_def

text \<open>theorems about walks:\<close>

thm nonempty_path_walk_between
thm walk_nonempty
thm walk_between_nonempty_path
thm walk_reflexive
thm walk_symmetric
thm walk_transitive
thm walk_in_Vs
thm walk_endpoints
thm walk_pref
thm walk_suff
thm edges_are_walks
thm walk_subset
thm induct_walk_betw

section \<open>Connected components\<close>

end