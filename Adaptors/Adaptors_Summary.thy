(*Author: Christoph Madlener *)

theory Adaptors_Summary
  imports
    Pair_Graph_Berge_Adaptor
    Pair_Graph_Library_Adaptor
begin

text \<open>
  This theory summarizes insights from implementing adaptors between different graph representations
  and aspects to consider when doing so. Ideally, an adaptor allows to easily transfer theorems
  from one representation to another by first establishing the relationship of fundamental
  concepts and then using existing lemmas from one representation to obtain them for the other.
  In this work specifically an adaptor from graph representation A to graph representation B works
  in the following way:
    \<^enum> take a graph (as represented) in A
    \<^enum> build an equivalent graph in B
    \<^enum> prove relationship of fundamental concepts -- this typically means proving equalities (of e.g.\ 
      the notion of reachability)
    \<^enum> obtain advanced lemmas for A by using existing ones from B

  In other words an A-to-B adaptor allows transferring lemmas from B to A. This slightly confusing
  convention arises as the graphs are adapted from A to B the lemmas on the other hand go in 
  the "converse" direction in this process. This also means that an adaptor is not bidirectional,
  i.e.\ for transferring lemmas from and to both involved representations two adaptors are needed.
\<close>

section \<open>Graph-Theory and DDFS\<close>
text \<open>
  The first adaptor in \<^theory>\<open>Pair_Graph_Library_Adaptor\<close> implements both directions for 
  \<^theory>\<open>Graph_Theory.Digraph\<close>s  and \<^theory>\<open>AGF.DDFS\<close>.
\<close>
subsection \<open>Graph-Theory to DDFS\<close>
text \<open>
  The first part implements the adaptor from Noschinski's Graph-Theory digraphs to \<^theory>\<open>AGF.Pair_Graph\<close>
  graphs. Constructing the DDFS graph is relatively straightforward as \<^theory>\<open>Graph_Theory.Digraph\<close>
  already provides \<^term>\<open>arcs_ends\<close>. This definition maps the set of (abstract) arcs to a set of pairs
  which is a graph in the DDFS representation. As DDFS is not capable of representing multigraphs,
  multi-arcs are "lost".

  One obstacle arises from the fact that DDFS uses an implicit vertex set whereas Graph-Theory
  uses an explicit one. This entails that the set of vertices of the DDFS graph generally is only
  a subset of the set of vertices of the original graph.
\<close>
thm wf_digraph.dVs_subset_verts
text \<open>
  This manifests itself in that we sometimes have to explicitly assume a node to be in the implicit
  vertex set of our constructed graph, e.g.\ in
\<close>
thm wf_digraph.reachable_imp'

text \<open>
  The greater challenge, however, is posed by the aforementioned capability of Graph-Theory to
  represent multigraphs. Walks in a multigraph are accurately described by a list of arcs.
  An arc in Graph-Theory is simply an element of some type \<^typ>\<open>'b\<close> and a graph has to specify
  \<^typ>\<open>'b \<Rightarrow> 'a\<close> functions for mapping an arc to its tail and head vertex respectively. However,
  reconstructing an arc from its ends is not trivial. Arcs in Graph-Theory will be referred to as
  abstract arcs in the following.

  This leads to two possible ways of how to deal with the proof of equality of arc-walks:
    \<^enum> Start with an arc-walk in Graph-Theory, i.e.\ a list of abstract arcs. An arc-walk in DDFS
      can then be obtained by mapping each arc to its ends with \<^term>\<open>arc_to_ends\<close>.
    \<^enum> Start with an arc-walk in DDFS, i.e.\ a list of pairs. As mentioned above, reconstructing the
      abstract arcs directly is not possible, so we resorted to using the choice operator to obtain
      them, see \<^term>\<open>pre_digraph.arc_from_ends\<close>.

  Both of these approaches exhibit some problems which essentially force us to introduce (strong)
  assumptions to our lemmas. In both cases @{command nitpick} was a really helpful tool by finding 
  counter-examples to uncover these additionally necessary assumptions.
\<close>
subsubsection \<open>The \<^term>\<open>arc_to_ends\<close> approach\<close>
text \<open>
  When starting out with an arc-walk \<^term>\<open>p\<close> in a graph \<^term>\<open>G\<close> in Graph-Theory, it is relatively 
  straight-forward to prove that \<^term>\<open>map (arc_to_ends G) p\<close> is an arc-walk in the DDFS graph, see
\<close>
thm wf_digraph.awalk_imp_awalk_map_arc_to_ends
text \<open>
  For empty walks we have to ensure that the start (and in this case also end) vertex are in the
  implicit vertex set of the DDFS graph.

  When trying to prove the converse direction of this lemma, i.e.\ if
  \<^term>\<open>map (arc_to_ends G) p\<close> is an arc-walk in the DDFS graph then \<^term>\<open>p\<close> is an arc-walk in the
  original graph, @{command nitpick} quickly finds the following counter-example:
  \begin{align*}
    G &\equiv (\{a_1\}, \{b_1 \equiv (a_1, a_1)\})\\
    p &= [b_2 \equiv (a_1, a_1)]
  \end{align*}
  In this case the DDFS graph is simply $\{(a_1, a_1)\}$, so clearly after mapping $b_2$ to its ends
  the resulting list $[(a_1, a_1)]$ is a walk from $a_1$ to $a_1$. However, $b_2$ is not even part of
  the original graph $G$, thus $p$ is not an arc-walk in $G$. To alleviate this issue we have to add
  the assumption \<^term>\<open>set p \<subseteq> arcs G\<close>.
\<close>
thm wf_digraph.awalk_map_arc_to_ends_imp_awalk
thm wf_digraph.awalk_iff_awalk

subsubsection \<open>The \<^term>\<open>pre_digraph.arc_from_ends\<close> approach\<close>
text \<open>
  When choosing the "converse" approach of starting with an arc-walk \<^term>\<open>p\<close> in the DDFS graph, 
  again it is relatively straight-forward to prove that \<^term>\<open>map pre_digraph.arc_from_ends p\<close>
  is an arc-walk in the original graph. The reason being that in this case the choice operator
  is well-defined in the sense that for each pair in \<^term>\<open>p\<close> there is a corresponding abstract arc
  in Graph-Theory graph \<^term>\<open>G\<close>.
\<close>
thm wf_digraph.awalk_imp_awalk_map_arc_from_ends

text \<open>
  However, the other direction again requires additional care, in this case due to the involved
  choice operator. The goal is to prove that given \<^term>\<open>map pre_digraph.arc_from_ends p\<close> is an
  arc-walk in \<^term>\<open>G\<close>, \<^term>\<open>p\<close> is an arc-walk in the DDFS graph. Once more @{command nitpick}
  quickly gives a counter-example, which can be boiled down to the following:
  \begin{align*}
    G &\equiv (\{a_1\}, \{(b_1 \equiv (a_1, a_1)\}) \\
    p &= [(a_1, a_2)]
  \end{align*}
  Here, the pair $(a_1, a_2)$ does not correspond to an arc in \<^term>\<open>G\<close>, the choice
  operator in \<^term>\<open>pre_digraph.arc_from_ends\<close> will still map this pair to the only arc $b_1$.
  However, $[b_1]$ is a valid arc-walk in \<^term>\<open>G\<close>, while \<^term>\<open>p\<close> is clearly not an arc-walk in the
  DDFS graph $\{(a_1, a_1)\}$.

  The only way to fix this is to add an assumption \<^term>\<open>set p \<subseteq> E\<close> to make the choice operator
  "well-behaved".
\<close>

subsubsection \<open>Vertex walks\<close>
text \<open>
  Graph-Theory also offers a formalization of vertex-walks, i.e.\ a walk is a list of vertices, 
  which for multigraphs is not necessarily an accurate representation. For non-multigraphs this
  representation is absolutely fine, as an arc is uniquely identified by its ends. For this adaptor
  it is also easier to work with vertices, as we have already established a subset relation between
  the vertices of the DDFS graph and the vertices of the original graph.

  The only small nuisances are (once more) the implicit vertex set of DDFS and the fact that the
  definition of vertex walks differs on the treatment of empty lists.
\<close>
thm wf_digraph.vwalk_iff

subsubsection \<open>Conclusion\<close>
text \<open>
  We introduced two ways of dealing with the discrepancy between abstract arcs in Graph-Theory and
  pairs in DDFS with regard to arc-walks. In both cases the strictly greater expressiveness of 
  Graph-Theory became apparent and poses challenges. Both approaches required the introduction of
  (possibly unwieldy) "translation" functions between the types of arcs and strong additional
  assumptions to prove the relationship of arc-walks in both formalizations. The question remains
  how sensible it is to implement the adaptor in this direction (at least for arc-walks), as we
  cannot prove all the properties of arc-walks (for multigraphs) in DDFS anyways.

  For vertex walks a different picture is drawn, as they work conceptually the same way in both
  formalizations. It highlights the more nuanced differences, though. The most prominent being the
  implicit vs.\ explicit vertex set. While an explicit vertex set allows disconnected vertices, in
  general some kind of well-formedness condition on the arcs has to be imposed. An implicit vertex set
  on the other hand does not impose any additional conditions, but disconnected vertices are not 
  easily representable. If this trade-off is better the one way or the other has to be considered
  on a case by case basis. Similar reasoning can be applied to the question if an empty walk is
  considered a walk or not.
\<close>

subsection \<open>DDFS to Graph-Theory\<close>
text \<open>
  The second part of \<^theory>\<open>Adaptors.DDFS_Library_Adaptor\<close> implements the adaptor from DDFS graphs
  to Graph-Theory graphs. This direction works smoothly, as the more expressive Graph-Theory easily
  accommodates DDFS graphs. Constructing the graph and all the proofs for the fundamental concepts
  are straightforward. This adaptor can in some sense be seen as a special case of
  \<^theory>\<open>Graph_Theory.Pair_Digraph\<close> with a practically implicit vertex set.

  This direction appears to be more useful and straightforward, as it allows to easily reuse lemmas
  from a more powerful formalization. Hence, in a context where this additional expressiveness is
  not required, one can easily switch to a more manageable and conceptually simpler representation.
\<close>

section \<open>Berge to DDFS\<close>
text \<open>
  The second adaptor is between the undirected \<^theory>\<open>AGF.Berge\<close> representation (i.e.\ a graph is a
  set of sets) and DDFS. The main goal of this endeavour was to evaluate how feasible it is to derive
  lemmas about undirected graphs from lemmas about symmetric graphs. As before, building the (now 
  symmetric) DDFS graph from the undirected representation is straightforward. Proving fundamental
  relations between vertices, edges and walks also does not pose a challenge. Obtaining more advanced
  lemmas about these concepts for the undirected case afterwards works out nicely as well.

  However, big parts of the Berge formalization deal with the edges in a walk 
  (cf.\ \<^term>\<open>edges_of_path\<close>), which is essentially a list of two-element sets. When defining this
  for the DDFS case this becomes a list of pairs. While formulating (mostly) equivalent lemmas 
  in this form is possible, the relation between \<^term>\<open>edges_of_path\<close> and \<^term>\<open>edges_of_dpath\<close>
  already involves mapping each pair back to a two-element set.
\<close>
thm graph_abs.edges_of_path_eq
text \<open>
  Proving advanced lemmas in the set formulation from the ones in the pair formulation in some cases
  becomes somewhat of a hassle, e.g.;
\<close>
thm graph_abs.edges_of_path_for_inner'
text \<open>
  or straight-up impossible:
\<close>
thm graph_abs.distinct_edges_of_vpath'

subsection \<open>Conclusion\<close>
text \<open>
  Building an adaptor from an undirected to a (symmetric) directed representation for graphs is
  certainly possible and useful, depending on the concepts one wants to argue about. As long as
  the arguments mainly follow from whether two vertices are connected or not, the transition
  between an undirected graph and a symmetric directed graph works smoothly. On the other hand,
  when the argumentation is mainly done on the basis of concrete edges, working with the adaptor
  can become awkward rather quickly.
\<close>
end