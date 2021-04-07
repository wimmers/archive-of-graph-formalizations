theory Digraph_Summary
  imports Graph_Theory.Graph_Theory 
    "../Graph_Theory/Directed_Tree"
    "../Adaptors/TA_Graph_Library_Adaptor"
begin

text \<open>This theory collects basic concepts about directed graphs in Noschinski's digraph library.\<close>

chapter \<open>digraph\<close>

text \<open>We will mostly cover finite digraphs (@{term fin_digraph}), which might include loops and 
      multi-edges.
      It is basically a @{type pre_digraph} featuring a set of vertices,
      a set of arcs and functions that map arcs to their head and tail.
  
      There are several other sorts of digraphs:
          e.g. @{term loopfree_digraph}, @{term nomulti_digraph}, @{term digraph}\<close>
 

context fin_digraph
begin

section \<open>Walks and Paths\<close>

subsection \<open>Arc-walks\<close>

text \<open>An @{term "awalk u p v"} is any valid arc walk \<open>p\<close> from \<open>u\<close> to \<open>v\<close>,
     a @{term trail} uses each arc at most once
     and a @{term apath} visits any vertex at most once.\<close>


thm awalkI_apath \<comment> \<open>Any @{term apath} is an @{term awalk}\<close>

text \<open>You can eliminate cycles from a path:\<close>
thm apath_awalk_to_apath \<comment> \<open>Get a @{term apath} from an @{term awalk}\<close>

thm awalk_to_apath_induct \<comment> \<open>Induction principle\<close>

thm awalk_appendI \<comment> \<open>@{term awalk} can be joined\<close>
thm awalk_append_iff \<comment> \<open>@{term awalk} can be split\<close>


text \<open>Is every @{term apath} a @{term trail}?\<close>

text \<open>Defines @{term cycle}. Note: a loop is not a cycle!\<close>

subsection \<open>Vertex-walks\<close>

text \<open>A list of vertices \<open>p\<close> is a @{term "vwalk p G"} if for all
      adjacent elements in the list there is an arc in \<open>G\<close>.
      A @{term vpath} visits any vertex at most once.\<close>

thm awalk_imp_vwalk \<comment> \<open>you can get a @{term vwalk} from a @{term awalk}\<close>


subsection \<open>Infinite paths\<close>

text \<open>TODO\<close>

section \<open>Reachability\<close>

text \<open>
  We have@{term "(u,v) \<in> arcs_ends G"} iff there is an arc from \<open>u\<close> to \<open>v\<close>.
  The predicates @{term reachable} and @{term reachable1} capture reachability, and
  reachability over at least one arc. They are defined by the reflexive
  transitive closure, respectively the transitive closure of @{term arcs_ends}.\<close>

subsection \<open>Reachability with paths\<close>

thm reachable_vwalk_conv
thm reachable_awalk


section \<open>Subgraphs and various graph properties\<close>


subsection \<open>Subgraphs\<close>

thm subgraph_def
thm spanning_def
thm spanning_tree_def

text \<open>subgraphs and interaction with concepts\<close>

thm subgraph_del_arc
thm subgraph_del_vert

lemma subgraph_add_vert: "subgraph G (add_vert u)"
  using wf_digraph_add_vert 
  by(auto simp add: add_vert_def wf_digraph_axioms compatible_def
          intro!: subgraphI)  
lemma subgraph_add_arc: "subgraph G (add_arc a)"
  using  wf_digraph_add_arc 
  by (auto simp add: add_arc_def wf_digraph_axioms compatible_def
          intro!: subgraphI)  


thm subgraph_cycle
thm vpathI_subgraph
thm subgraph_apath_imp_apath

thm reachable_mono

text \<open>interaction between insertion/deletion and paths\<close>
thm vpathI_subgraph[OF _ subgraph_add_vert]
thm vpathI_subgraph[OF _ subgraph_del_vert]
thm vpathI_subgraph[OF _ subgraph_del_arc]
thm vpathI_subgraph[OF _ subgraph_add_arc]
 
thm subgraph_apath_imp_apath[OF _ subgraph_del_vert]
thm subgraph_apath_imp_apath[OF _ subgraph_del_arc] 


subsection \<open>Graph properties\<close>
text \<open>aka cycle free aka DAG. Note that this definition should be renamed to something more
  appropriate such as dag since there is no reasonable definition of forests in a general digraph.
  Forests and trees should only be defined in @{locale sym_digraph}.\<close>
thm forest_def

text \<open>Every DAG has a topological numbering:\<close>

thm fin_dag_def
lemma (in -) forest_dag_conv: "forest G = dag G"
  oops

thm dag.topological_numbering
\<comment> \<open>
  This theorem exists because has because it has been transferred
  from the \<open>TA_Graph\<close> library. But it should be re-proved for better comparison.\<close>

subsubsection \<open>Strongly Connected Components\<close>

thm strongly_connected_def \<comment> \<open>Q: why does the graph have to be non-empty to be strongly connected?\<close>
thm sccs_def sccs_altdef2
thm sccs_verts_def sccs_verts_conv

text \<open>The graph of strongly connected components forms a DAG/has a topological ordering.\<close>

thm scc_num_topological \<comment> \<open>See note for @{thm dag.topological_numbering} above\<close>

thm scc_digraphI

lemma "forest scc_graph" 
  sorry


subsection \<open>The underlying undirected/symmetric graph of a digraph\<close>

thm mk_symmetric_def

thm reachable_mk_symmetric_eq

text \<open>A graph \<open>G\<close> is @{term connected} if its underlying undirected graph 
      (i.e. symmetric graph) is @{term strongly_connected}\<close>

thm tree_def



section \<open>In- and out-degrees\<close>

thm in_degree_def out_degree_def

find_theorems in_degree 

lemma cycle_of_indegree_ge_1_:
  assumes "\<forall> y \<in> verts G. in_degree G y \<ge> 1"
  shows "\<not> forest G"
  sorry      

text \<open>Characterization of Euler trails:\<close>

thm closed_euler
thm open_euler



section \<open>Rooted directed tree\<close>

thm directed_tree_def
                     
thm directed_tree.finite_directed_tree_induct \<comment> \<open>an induction rule\<close>
                            
section \<open>A BFS algorithm for finding a rooted directed tree.\<close>


section \<open>A DFS algorithm finding a rooted directed tree and computing DFS numberings.\<close>


section \<open>An algorithm for finding the SCCs.\<close>


end


end