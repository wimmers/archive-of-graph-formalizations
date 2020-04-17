# The Archive of Graph Formalizations

## Description
This informal `Archive of Graph Formalizations` collects different formalizations of graphs
from the Isabelle/HOL universe to compare them and to eventually unify the efforts.

## Index
- `TA_Graphs`: The graph formalization used in [Munta](https://github.com/wimmers/munta)
- `Graph_Theory`: Additional material for the graph library authored by Lars Noschinski,
which is part of the AFP (https://www.isa-afp.org/entries/Graph_Theory.html)
    * In particular, it contains the theory `Directed_Tree` which defines a directed tree complete with a custom induction rule.



## An (incomplete) list of Graph Formalizations

### Directed Graphs
- `digraph` of Noschinski's [`Graph_Theory` library](https://www.isa-afp.org/entries/Graph_Theory.html) models general directed graphs as a set of vertices (`verts`) and a set of abstract `arcs` with a `tail` and a `head`. It allows multi-arcs. 
  - [`Arc_Walk`](https://www.isa-afp.org/browser_info/current/AFP/Graph_Theory/Arc_Walk.html) defines `awalk`, `apath`, `trail`, `cycle`
  - [`Vertex_Walk`](https://www.isa-afp.org/browser_info/current/AFP/Graph_Theory/Vertex_Walk.html) defines `vwalk`, `vpath`
- `pair_digraph` of Noschinski's [`Graph_Theory` library](https://www.isa-afp.org/entries/Graph_Theory.html) is a simpler representation of directed graphs by a set of vertices (`pverts`) and arcs by a relation `parcs`. (no multi-arcs!)
  - provides a conversion `with_proj` from `pair_digraph` to `digraph`
- Lukas:
  - Extended Noschinski's theory with trees and shortest path trees and some theorems about these concepts.
  - Proves triangle ineq for weighted digraphs and how to compute a dominating set
- In [`Cava_Automata`](https://www.isa-afp.org/entries/CAVA_Automata.html) directed graphs ([`digraphs`](https://www.isa-afp.org/browser_info/current/AFP/CAVA_Automata/Digraph_Basic.html)) are defined as a set of tuples.
  - define paths `path`, 
  - is used by [`Gabow_SCC`](https://www.isa-afp.org/entries/Gabow_SCC.html), [`DFS_Framework`](https://www.isa-afp.org/entries/DFS_Framework.html), [`Formal_SSA`](https://www.isa-afp.org/browser_info/current/AFP/Formal_SSA/Graph_path.html) ...
- Wimmer defines directed graphs as a relation (`'v => 'v => bool`), see [TA_Graphs](https://github.com/wimmers/archive-of-graph-formalizations/blob/master/TA_Graphs/TA_Graphs.thy).
- Zhan defines directed Graphs as [set of pairs](https://www.isa-afp.org/browser_info/current/AFP/Auto2_Imperative_HOL/Connectivity.html) (`(nat × nat) set`) for verifying an algorithm for connectivity. 
  - defines vertex paths (`is_path`), connectivity (`connected_rel`), 
- [Koenigs lemma](https://www.isa-afp.org/browser_info/current/AFP/Coinductive/Koenigslemma.html) is proven by Lochbihler on a directed graph formalized as adjacency matrix (`nat => nat => bool`).
  - defines vertex paths (`paths`) as coinductive lists. 
- [Containers](https://www.isa-afp.org/browser_info/current/AFP/Containers/Containers_DFS_Ex.html) by Lochbihler define directed graphs as a set of pairs to verify a DFS algorithm.
- [InfPathElimination](https://www.isa-afp.org/entries/InfPathElimination.html) as [directed graphs](https://www.isa-afp.org/browser_info/current/AFP/InfPathElimination/Graph.html) as set of edges being essentially a pair.
- for [Max-Flow-Min-Cut-Theorem](https://www.isa-afp.org/entries/MFMC_Countable.html) directed graphs are represented as an [adjacency matrix]((https://www.isa-afp.org/browser_info/current/AFP/MFMC_Countable/Max_Flow_Min_Cut_Countable.html)) (`'v => 'v => bool`). interesting: paths are defined over relations and `rtrancl_path`.
- for [Menger's Theorem](https://www.isa-afp.org/entries/Menger.html) Dittmann defines [directed graphs](https://www.isa-afp.org/browser_info/current/AFP/Menger/Graph.html) as a set of pairs.
  - defines vertex paths (`walk`), distinct paths (`path`), `path_from_to`, 
  - defines lenth of shortest path (`distance`)
- for [`Tree_Decomposition`](https://www.isa-afp.org/entries/Tree_Decomposition.html) Dittmann defines [directed graphs](https://www.isa-afp.org/browser_info/current/AFP/Tree_Decomposition/Graph.html)  as a set of pairs.
  - code duplication with [graphs in Menger's Theorem](https://www.isa-afp.org/browser_info/current/AFP/Menger/Graph.html))
  - further defines `cycle`
- Mohammad:
  - A digraph is a set of pairs of vertices. The digraph's vertices are the union of vertices on which there are incident edges.


### Directed Weighted/Labeled Graphs
- In [`Flow_Networks`](https://www.isa-afp.org/entries/Flow_Networks.html) weighted directed [`graph`](https://www.isa-afp.org/browser_info/current/AFP/Flow_Networks/Graph.html)s are represented as functions `edge ⇒ 'capacity`.
  - Vertices `V` and arcs `E` are defined
  - arc paths (`isPath`) and distinct arc paths (`isSimplePath`) are defined
- In [`Dijkstra_Shortest_Path`](https://www.isa-afp.org/browser_info/current/AFP/Dijkstra_Shortest_Path/Graph.html) directed graphs (`graph`) are defined as a set of vertices (`nodes`) and set of labelled edges (`edges`) as tuples (`vertex * label * vertex`).
  - arc paths (`is_path`)
- [Bellman-Ford](https://www.isa-afp.org/browser_info/current/AFP/Monad_Memo_DP/Bellman_Ford.html) uses an implicit graph in a edge weight function `W :: nat ⇒ nat ⇒ int extended`
- [Floyd-Warshall](https://www.isa-afp.org/browser_info/current/AFP/Timed_Automata/Floyd_Warshall.html) (and also [here](https://www.isa-afp.org/browser_info/current/AFP/Floyd_Warshall/Floyd_Warshall.html)) uses a adjacency matrix `'c mat = "nat ⇒ nat ⇒ 'c"` to represent a weighted directed graph.
- Zhan defines weighted directed Graphs as [adjacency lists](https://www.isa-afp.org/browser_info/current/AFP/Auto2_Imperative_HOL/Dijkstra.html) (`nat list list`) for verifying Dijkstra. 
  - defines vertex paths (`is_path`), shortest path (`is_shortest_path`),   
- For [Dijkstra](https://www.isa-afp.org/entries/Prim_Dijkstra_Simple.html) Nipkow and Lammich define [directed graphs](https://www.isa-afp.org/browser_info/current/AFP/Prim_Dijkstra_Simple/Undirected_Graph.html) as an adjacency matrix (`('v * 'v) => enat`).
  - defines paths (`path`), distance (`δ`)
- [Graph Saturation](https://www.isa-afp.org/entries/Graph_Saturation.html) has [labeled directed graphs](https://www.isa-afp.org/browser_info/current/AFP/Graph_Saturation/LabeledGraphs.html)
- [Transition Systems and Automata](https://www.isa-afp.org/entries/Transition_Systems_and_Automata.html) has labeled transition systems and automata (`'a => 'q => 'q set`) aswell as design principles for a generic library with many different concrete representations.

### Undirected Graphs
- In Noschinski's [`Graph_Theory` library](https://www.isa-afp.org/entries/Graph_Theory.html) `graph` model undirected graphs as symmetric `digraphs`
- In [`Girth_Chromatic`](https://www.isa-afp.org/entries/Girth_Chromatic.html) Lars Noschinski defines undirected graphs [`ugraphs`](https://www.isa-afp.org/browser_info/current/AFP/Girth_Chromatic/Ugraphs.html) as a set of vertices and a set of undirected edges. Edges are represented as sets of vertices.
  - defines `uwalks`, `ucycles`, 
- In [`Kruskal`](https://www.isa-afp.org/browser_info/current/AFP/Kruskal/) Haslbeck defines [undirected graphs](https://www.isa-afp.org/browser_info/current/AFP/Kruskal/UGraph.html) with edges as a set of [`uprod`s](https://www.isa-afp.org/browser_info/current/AFP/Kruskal/Uprod.html):
  - defines edge paths (`epath`), distinct edge paths (`depath`)
  - defines `cycle`, `decycle`, `forest`, 
  - defines weighted undirected graphs (`uGraph`)
- In [`Kruskal`](https://www.isa-afp.org/browser_info/current/AFP/Kruskal/) Biendarra uses directed graphs from [`Dijkstra_Shortest_Path.Graph`](https://www.isa-afp.org/browser_info/current/AFP/Kruskal/Graph.html) and interprets them as [undirected graphs](https://www.isa-afp.org/browser_info/current/AFP/Kruskal/Graph_Definition.html).
  - defines edge paths (`is_path_undir`).  
  - defines trees, forests
  - is based on `Dijkstra_Shortest_Path.Graph`
- For [Prim](https://www.isa-afp.org/entries/Prim_Dijkstra_Simple.html) Nipkow and Lammich define [undirected graphs](https://www.isa-afp.org/browser_info/current/AFP/Prim_Dijkstra_Simple/Undirected_Graph.html) as a symetric directed graph, i.e. edges being pairs of vertices and E being symetric and irreflexiv.
  - defines paths (`path`), simple paths (`simple`)
  - defines cycle freedom (`cycle_free`), connectedness (`connected`), `tree`, `is_spanning_tree`
  - adds weight function (`w :: 'v set => nat`), then defines `is_MST`
- in [Koenigsberg_Friendship](https://www.isa-afp.org/entries/Koenigsberg_Friendship.html) uses the directed graph from  [`Dijkstra_Shortest_Path`](https://www.isa-afp.org/browser_info/current/AFP/Dijkstra_Shortest_Path/Graph.html) and define [undirected multigraphs](https://www.isa-afp.org/browser_info/current/AFP/Koenigsberg_Friendship/MoreGraph.html) (`valid_unMultigraph`) 
  - they define trails (`is_trail`), connectivity (`connected`), remove undirected path (`rem_unPath`)
  - Eulerian trails (`is_Eulerian_trail`), Eulerian circuits (`is_Eulerian_circuit`)
  - `euclerian_cycle_ex`, `euclerian_path_ex`, `eulerian_sufficient`
- Abdulaziz graphs in Blossom Algorithm:
  - A graph is a set of edges, each of which is a set of vertices.
  - A theory regarding connected components is defined in terms of edges and vertices, and their connection is developed.
  - An induction principle is defined on connected components.
  - Contraction operation is defined and some theory for that is developed.
  - A lot of theory about matchings, forest construction, odd set covers. Has a proof of Berge's lemma. Necessary for any efficient matching algorithm.
- Krebs graphs for diameter approximation algorithms
  - Based on Abdulaziz. Difference: a graph is defined wrt a set of vertices.
  - Extended with edges with enat weights.
  - Theory about paths, walks, costs, shortest paths, trees, BFS trees, neighbourhoods, triangle inequality, dominating sets. It was used to cleanly formalise/verify an algorithm that does vertex contraction.