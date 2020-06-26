section \<open>Findings on Walks\<close>

theory Findings_Walks
  imports 
    AGF.DDFS
    AGF.Berge
    AGF.Graph
    AGF.TA_Graphs
    Graph_Theory.Digraph
    Graph_Theory.Arc_Walk
    Graph_Theory.Vertex_Walk
    Ports_Overview
begin

text \<open>
  This theory summarizes the findings from porting and comparing lemmas regarding walks (and 
  specializations thereof) from different graph representations. First a short overview of the 
  considered representations is given. Then similarities and differences in definitions and available
  lemmas will be emphasized. One focal point of this analysis was the proof automation obtainable in
  different representations. We conclude that -- solely regarding walks -- the underlying graph
  representation does not substantially impact this aspect. Instead carefully considering rather
  minuscule differences in definitions and formulations of lemmas can enable automation. We will
  refer to relevant lemmas (and their proofs) to illustrate this in more detail. For the full
  overview of ported lemmas, see \<^theory>\<open>Ports.Ports_Overview\<close>.
\<close>

subsection \<open>Considered Graph Representations\<close>
text \<open>
  The target of the ports was \<^theory>\<open>AGF.DDFS\<close>, which represents a graph simply as a set of pairs 
  (\<^typ>\<open>('a \<times> 'a) set\<close>), vertices are defined implicitly as \<^term>\<open>dVs\<close>. This representation will be 
  referred to as DDFS from now on. The original formalization defines walks inductively via 
  \<^term>\<open>dpath\<close>, \<^term>\<open>[]\<close> is also a walk. Additionally there is \<^term>\<open>dpath_bet\<close>, for specifying a 
  start and end vertex, which enforces non-emptiness. Originally this was the smallest representation
  only containing some basic lemmas about paths and how a directed graph can model a transitive
  relation using walks (?):
\<close>
thm dpath_transitive_rel dpath_transitive_rel'
text \<open>
  A selection of lemmas regarding walks (and path, trails, etc.) has been ported from two undirected 
  and two directed graph representations.
\<close>

subsubsection \<open>Undirected Graph Representations\<close>
paragraph \<open>\<^theory>\<open>AGF.Berge\<close>\<close>
text \<open>
  A graph is a set of (two-element) sets (\<^typ>\<open>'a set set\<close>), implicit vertices
 \<^term>\<open>Vs\<close> -- \<^locale>\<open>graph_abs\<close>. Referred to as Berge from now on.

  Defines vertex walks via the inductive predicate \<^term>\<open>Berge.path\<close> which allows empty walks. Also
  provides \<^term>\<open>walk_betw\<close> for specifying start and end vertices. Note that \<^term>\<open>walk_betw\<close>
  doesn't allow empty walks. \<^term>\<open>edges_of_path\<close> is used to extract the edges of a given walk.

  Besides some basic lemmas about walks, the formalization focuses on \<^term>\<open>edges_of_path\<close> and
  goes on to develop theory about connected components and matchings. No notion of reachability
  is introduced.
\<close>

paragraph \<open>\<^theory>\<open>AGF.Graph\<close>\<close>
text \<open>
  Like Berge, but with an explicit vertex set (\<^typ>\<open>'a graph\<close>) -- \<^locale>\<open>Graph.graph\<close>. Referred to 
  as Mitja from now on.

  Defines \<^term>\<open>walk\<close> and \<^term>\<open>walk_edges\<close> which essentially correspond to \<^term>\<open>walk_betw\<close> and
  \<^term>\<open>edges_of_path\<close> from Berge. Also defines \<^term>\<open>closed_walk\<close>s, \<^term>\<open>Walk.trail\<close>s,
  \<^term>\<open>closed_trail\<close> and \<^term>\<open>path\<close>s. Shows the number of paths in a finite graphs is finite.
\<close>
thm finite_graph.paths_finite
text \<open>
  In addition to basic walk lemmas includes decomposition of walks at a given vertex and obtaining
  a path from a walk.
\<close>
thm graph.walk_vertex_decomp_is_walk_vertex_decomp
thm graph.walk_to_path_is_path
text \<open>
  Reachability is defined via the existence of a walk (\<^term>\<open>Walk.reachable\<close>).

  Furthermore defines weighted graphs and on top of that shortest paths, trees etc.
\<close>

subsubsection \<open>Directed Graph Representations\<close>
paragraph \<open>\<^theory>\<open>AGF.TA_Graphs\<close>\<close>
text \<open>
  A graph is defined via its adjacency relation (\<^typ>\<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>), implicit
  \<^term>\<open>Graph_Defs.vertices\<close>. Referred to as TA-Graph from now on.

  Walks are defined via the inductive \<^term>\<open>Graph_Defs.steps\<close>, as nonempty lists of vertices. 
  \<^term>\<open>Graph_Defs.run\<close> formalizes infinite walks.

  Reachability is defined as the reflexive transitive closure of the adjacency relation 
  (\<^term>\<open>Graph_Defs.reaches\<close>), resp.\ its transitive closure (\<^term>\<open>Graph_Defs.reaches1\<close>).

  Formalizes simulations and bisumiluations.
\<close>

paragraph \<open>\<^theory>\<open>Graph_Theory.Digraph\<close>\<close>
text \<open>
  A graph is represented as a set of vertices, a set of edges and functions mapping edges to their 
  head, resp. tail (\<^typ>\<open>('a, 'b) pre_digraph\<close>)-- \<^locale>\<open>wf_digraph\<close>. Referred to as Digraph from 
  now on.

  Formalizes both vertex (\<^term>\<open>vwalk\<close>) and arc walks (\<^term>\<open>pre_digraph.awalk\<close>). The vertex walk 
  part focuses on "joinability" of walks. Provides \<^term>\<open>vwalk_arcs\<close> to compute the arcs belonging
  to a walk. Note, however, that this gives a list of pairs of vertices, which generally are not the
  arcs of the graph (which have an arbitrary type).

  For arc walks also has \<^term>\<open>pre_digraph.trail\<close> and \<^term>\<open>pre_digraph.apath\<close>. Shows how to obtain a
  path from a walk.
\<close>
thm wf_digraph.apath_awalk_to_apath
text \<open>
  Reachability (\<^term>\<open>Digraph.reachable\<close>) is defined via a custom reflexive transitive closure
  (\<^term>\<open>rtrancl_on\<close>) of \<^term>\<open>arcs_ends\<close> as to include potentially disconnected vertices.

  Has lots of additional theory, including Euler trails, shortest paths, a simpler version
  representing the arcs as a set of pairs, and more.
\<close>

subsection \<open>Walk representation and basic reasoning\<close>
text \<open>
  All of the above formalizations define walks as lists of either vertices or arcs. Hence,
  reasoning about walks is essentially reasoning about lists with some additional conditions
  imposed by the edges present in a given graph. After establishing the interactions
  between elementary list operations and walks, the reasoning is pretty much independent from the
  underlying graph representation. However, Digraph which arguably has the most
  abstract approach, has to help itself by employing more helper definitions, in order to formulate
  lemmas in a manageable way (cf.\ \<^term>\<open>arcs_ends\<close>, \<^term>\<open>pre_digraph.awhd\<close>, etc.). All the other
  theories chose a more lightweight representation, allowing to work directly on it.
\<close>

subsection \<open>Arc walks vs.\ vertex walks\<close>
text \<open>
  As mentioned before, walks can be defined as either lists of vertices or as lists of arcs. The
  first variant is present in all candidates. Arc walks, however, are only formalized in Digraph 
  (\<^theory>\<open>Graph_Theory.Arc_Walk\<close>). Strictly concerning the reasoning, the two variants again do not
  differ in a meaningful way. \<^theory>\<open>Graph_Theory.Vertex_Walk\<close> mentions that vertex walks "do not
  really work with multigraphs". As it stands only Digraph is capable of representing multigraphs.
  Obtaining a vertex walk from an arc walk is straightforward.
\<close>
thm wf_digraph.awalk_imp_vwalk
text \<open>
  The converse direction is nontrivial for Digraph because one cannot recover the arcs used by a
  vertex walk. For the other (non multigraph) representations both directions should be obtainable.
  See the following to lemmas for reference:
\<close>
thm awalk_imp_dpath
thm dpath_imp_awalk

subsection \<open>Empty vs.\ nonempty walks\<close>
text \<open>
  As mentioned before, the formalizations differ in whether they allow empty walks (i.e.\ \<^term>\<open>[]\<close>)
  or not. This has some implications on the automation when a proof is conducted with induction on
  the list representing a walk. Consider the proofs of the following lemmas, the first one from DDFS
  which allows empty walks, the second one from TA-Graph, which does not allow empty walks.
\<close>
thm append_dpath_pref
thm Graph_Defs.steps_appendD1
text \<open>
  In TA-Graph an additional case distinction is required in the induction step in order to complete
  the proof. This inconvenience could possibly be fixed with a custom induction scheme. Thus this
  aspect also does not lead to a favorable definition of walks, instead it remains a consideration 
  to be made.
\<close>

subsection \<open>Implicit vs.\ explicit vertex sets\<close>
text \<open>
  Another difference between the different formalizations is whether they define an implicit or
  explicit vertex set. An implicit vertex set does not allow for disconnected vertices. During
  the ports of lemmas about walks, this only came into play in one case. The following lemma from
  Mitja about walks in a (vertex-)induced subgraph took some additional care when formulating, in order to
  accommodate the implicit vertex set of DDFS.
\<close>
thm induced_subgraph.walk_supergraph_is_walk_subgraph
thm dpath_induced_subgraph_dpath

subsection \<open>Comparison of available Theory\<close>
text \<open>
  The introduction of the different representations already briefly introduced what areas they 
  cover. Most of them specialize at some point into different graph topics besides walks. Strictly
  speaking about walks, the most "complete" formalization is probably Digraph. One big reason for
  this of course being that it was the only representation under consideration which formalized
  arc-walks. It also has a very solid foundation for extending the existing walk lemmas (if that is
  even necessary).

  As DDFS was the target of the ports it now also has arc-walks. At the same time it needs more work
  to clean up, unify the concepts introduced by different representations, and also some fleshing out
  of basic lemmas and intermediate results. While working directly with a set of edges works well for
  prototyping and some quick developments, it would probably be also helpful to work with locales in
  further development.
\<close>

subsection \<open>Conclusion\<close>
text \<open>
  In the previous subsections we summarized the findings of porting lemmas from different graph
  representations to DDFS. The goal was to evaluate whether one formalization offers improved
  proof automation for lemmas about walks. We conclude that no meaningful advantages can be
  observed in this regard.

  Subsequently we investigated the differences in the definitions of walks and vertices. Although
  in this case the effects were observable in some cases, the miniscule reduction of effort does not
  merit departing from a wanted definition.
  
\<close>

end