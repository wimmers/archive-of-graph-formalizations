theory Mitja_Summary
  imports
    Graph_Theory
begin

text \<open>Summary of Mitja's graph formalization limited to theorems about paths.\<close>

text \<open>A graph has an explicit set of vertices. Edges are two element sets of vertices (hence no 
      loops). There's also \<^term>\<open>finite_graph\<close>\<close>
print_record "'a graph"
thm graph_def

section\<open>Walks\<close>

text \<open>A walk is a non-empty list of vertices. There appear to be no arc walks in this 
      formalization, although there is \<^term>\<open>walk_edges\<close> to obtain the edges of a
      walk. The \<^term>\<open>walk_length\<close> is the number of edges in it.\<close>
thm walk_def

term closed_walk

text \<open>(Single) vertices, edges and walks\<close>
context graph
begin
thm edge_iff_walk

text \<open>Note: A single vertex is a walk!\<close>
thm singleton_is_walk

text \<open>A walk consists of vertices of the graph.\<close>
thm walk_in_vertices
thm walk_hd_in_vertices
thm walk_last_in_vertices

thm walk_hd_neq_last_implies_edges_non_empty

thm walk_edges_in_edges

text \<open>Walk prefixes/suffixes\<close>
thm walk_prefix_is_walk
thm walk_suffix_is_walk

text \<open>Appending\<close>
thm walk_append_is_walk walk_append_append_is_walk
thm walk_edges_append walk_edges_append_2

text \<open>Reversing\<close>
thm walk_rev
thm walk_edges_rev

text \<open>Walk decomposition\<close>
term is_walk_vertex_decomp
thm walk_vertex_decomp_def
thm walk_vertex_decompE walk_vertex_decompE_2 \<comment> \<open>obtaining (de)compositions\<close>
thm walk_vertex_decomp_is_walk_vertex_decomp

text \<open>Closed walk decomposition (e.g. for cycle elimination)\<close>
term is_walk_closed_walk_decomp
thm walk_closed_walk_decomp_def
thm walk_closed_walk_decompE walk_closed_walk_decompE_2
thm walk_closed_walk_decomp_is_walk_closed_walk_decomp
end

subsection \<open>Walks in subgraphs\<close>
thm subgraph_def induced_subgraph_def

thm subgraph.walk_subgraph_is_walk_supergraph
thm induced_subgraph.walk_supergraph_is_walk_subgraph

section \<open>Trails\<close>
text \<open>A trail is a walk with distinct edges.\<close>
thm trail_def

term closed_trail
thm closed_trail_implies_Cons closed_trail_implies_tl_non_empty

context graph
begin

text \<open>A trail consists of vertices of the graph.\<close>
thm trail_in_vertices
thm trail_hd_in_vertices
thm trail_last_in_vertices
thm closed_trail_tl_hd_in_vertices

text \<open>Trail prefixes/suffixes\<close>
thm trail_prefix_is_trail
thm trail_suffix_is_trail

text \<open>Reversing\<close>
thm trail_rev_is_trail closed_trail_rev_is_closed_trail

text \<open>"Convenience Lemmas"\<close>
thm closed_trail_hd_tl_hd_is_trail closed_trail_tl_rev_is_trail closed_trail_hd_tl_hd_neq_tl_rev
end

section \<open>Paths\<close>
text \<open>A path is a walk with distinct vertices.\<close>
thm path_def

thm finite_graph.paths_finite

text \<open>From walks to paths\<close>
context graph
begin

term walk_to_path
thm walk_to_path_induct
thm walk_to_path_is_path
end

text \<open>Reachability and connectedness are defined via the existence of walks.\<close>
thm reachable_def
thm connected_def

text \<open>Properties of reachability\<close>
thm reachable_trans graph.reachable_symmetric
thm graph.not_reachable_if_not_in_vertices
thm subgraph.not_reachable_in_subgraph_if_not_reachable_in_supergraph

section \<open>Trees\<close>
text \<open>A tree is characterized by the existence of a unique trail between any two vertices.\<close>
thm tree_def

text \<open>A tree has no cycles (aka closed trail) and is connected.\<close>
thm tree.no_closed_trail tree.connected

text \<open>Definitions for rooted trees, spanning trees and rooted spanning trees.\<close>
thm rooted_tree_def spanning_tree_def rooted_spanning_tree_def

section \<open>Weighted Graphs\<close>
text \<open>\<^typ>\<open>'a cost_fun\<close> assigning weights/cost to edges. The cost of a walk is the sum of the
      cost of its edges.\<close>
thm walk_cost_def

thm walk_cost_non_negative_if_cost_non_negative

text \<open>Appending and reversing\<close>
thm walk_cost_append walk_cost_append_2 walk_cost_append_append walk_cost_rev

text \<open>Decomposition\<close>
thm graph.walk_cost_closed_walk_decomp

text \<open>Relating walk cost to path cost\<close>
thm graph.walk_cost_ge_walk_to_path_cost

subsection \<open>Shortest paths\<close>
thm shortest_walk_cost_def is_shortest_walk_def

text \<open>Basic lemmas\<close>
thm graph.shortest_walk_cost_symmetric
thm shortest_walk_cost_non_negative_if_cost_non_negative
thm shortest_walk_cost_le_walk_cost
thm graph.shortest_walk_cost_edge_le_cost
thm shortest_walk_cost_reachable_conv
thm singleton_is_shortest_walk

text \<open>Shortest path cost\<close>
thm graph.shortest_walk_cost_eq_shortest_path_cost
thm finite_graph.shortest_walk_cost_path

text \<open>Triangle inequality\<close>
thm finite_graph.shortest_walk_cost_triangle_inequality

text \<open>Decomposing shortest walks\<close>
thm finite_graph.shortest_walk_cost_walk_vertex_decomp

text \<open>Shortest walks in sub-/supergraphs\<close>
thm subgraph.shortest_walk_cost_subgraph_ge_shortest_walk_cost_supergraph
thm induced_subgraph.shortest_walk_supergraph_is_shortest_walk_subgraph

text \<open>Convenience lemmas\<close>
thm graph.shortest_walk_cost_infinite_if_not_in_vertices
thm finite_graph.shortest_walk_cost_walk

thm shortest_walk_def
thm finite_graph.shortest_walk_is_shortest_walk
term shortest_walk_length

thm finite_graph.shortest_walk_length_eq_1_if_edge

section\<open>Shortest path tree\<close>
thm shortest_path_tree_def
end