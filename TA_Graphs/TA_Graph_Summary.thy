theory TA_Graph_Summary
  imports TA_Graphs TA_Graph_Library_Adaptor
begin

text \<open>This theory collects basic concepts about directed graphs in Munta's digraph library.\<close>

chapter \<open>TA Graph\<close>

text \<open>
Graphs are simply a predicate @{term "E :: 'a \<Rightarrow> 'a \<Rightarrow> bool"} specifying the edges.
Most definitions and theorems are specified in a locale without assumptions @{locale Graph_Defs}.
It provides the syntax \<open>\<rightarrow>\<close> for graph edges.
From this, other locales for special types of graphs, e.g.\ @{locale Finite_Graph} are derived.
\<close>

context Graph_Defs
begin

section \<open>Walks And Paths\<close>


subsection \<open>Arc walks\<close>

text \<open>Not used in this library.\<close>


subsection \<open>Vertex walks\<close>

text \<open>Predicate @{term steps}.\<close>

text \<open>Paths could be defined as:\<close>
abbreviation "path xs \<equiv> steps xs \<and> distinct xs"

lemma path_steps:
  "path xs \<Longrightarrow> steps xs"
  by (rule conjE)

text \<open>Eliminating all cycles from a path.\<close>
thm steps_remove_cycleE

thm steps_rotate \<comment> \<open>useful: path rotation\<close>

thm steps_alt_induct \<comment> \<open>A useful induction principle.\<close>

text \<open>No induction principle for making use of paths.\<close>

thm steps_append steps_append2 steps_appendD1 steps_appendD2 steps_decomp
\<comment> \<open>Composing \& decomposing paths\<close>

text \<open>No definition of cycles. It's just @{term "x \<rightarrow>\<^sup>+ x"}. That includes self-loops.\<close>

subsection \<open>Reachability and paths\<close>

thm reaches_steps_iff reaches1_steps_iff reaches_steps_iff2

end


section \<open>Subgraphs And Various Graph Properties\<close>

subsection \<open>Subgraphs\<close>

text \<open>@{locale Subgraph} and @{locale Subgraph_Node_Defs}\<close>

text \<open>No deleting/adding nodes/edges\<close>

thm Subgraph.reaches Subgraph.reaches1


subsection \<open>Graph Properties\<close>

text \<open>The locale for cycle-free graphs/DAGs is @{locale DAG}.\<close>

thm DAG.topological_numbering \<comment> \<open>Every finite DAG has a topological numbering\<close>


subsubsection \<open>Strongly Connected Components\<close>

text \<open>No def of a strongly connected graph.\<close>

thm Finite_Graph.is_max_scc_def  \<comment> \<open>SCCs\<close>

text \<open>The graph of strongly connected components forms a DAG/has a topological ordering.\<close>
context Finite_Graph
begin

interpretation Graph_Invariant
  where E = E and P = "\<lambda>x. x \<in> vertices"
  by standard (auto simp: vertices_def)

interpretation digraph_nodes: fin_digraph G\<^sub>n
  apply standard
  subgoal finite_verts
    by (simp add: Subgraph_Node_Defs.G\<^sub>n_def finite_graph)
  subgoal
    by (rule finite_subset[where B = "verts G\<^sub>n \<times> verts G\<^sub>n"])
       (auto simp: G'_def E'_def G\<^sub>n_def finite_graph)
  done

text \<open>As you can see, we steal this theorem from Lars Noschinski's Library.
It should be reproved directly in this library for comparison.\<close>
interpretation scc_digraph: fin_dag digraph_nodes.scc_graph
  by (rule digraph_nodes.scc_digraphI)

text \<open>These originate in this library\<close>
thm scc_num_inj scc_num_topological

end

subsection \<open>The underlying undirected/symmetric graph of a digraph\<close>
text \<open>Not defined\<close>


section \<open>In- And Out-degrees\<close>

thm Graph_Defs.directed_graph_indegree_ge_1_cycle

text \<open>Characterization of Euler trails: not defined\<close>


section \<open>Rooted directed tree\<close>

text \<open>Only rooted graphs are defined: @{locale Graph_Start_Defs}\<close>
text \<open>A rooted tree would be:\<close>
locale Rooted_Tree =
  Graph_Start_Defs + assumes no_reachable_cycle: "\<not> (reachable x \<and> x \<rightarrow>\<^sup>+ x)"


section \<open>Algorithms\<close>
text \<open>Various DFS-type algorithms can be found here:
@{url "https://github.com/wimmers/munta/tree/master/Worklist_Algorithms"}\<close>


end