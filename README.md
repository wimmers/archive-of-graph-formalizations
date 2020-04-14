# The Archive of Graph Formalizations

## Description
This informal `Archive of Graph Formalizations` collects different formalizations of graphs
from the Isabelle/HOL universe to compare them and to eventually unify the efforts.

## Index
- `TA_Graphs`: The graph formalization used in [Munta](https://github.com/wimmers/munta)
- `Graph_Theory`: Additional material for the graph library authored by Lars Noschinski,
which is part of the AFP (https://www.isa-afp.org/entries/Graph_Theory.html)



## An (incomplete) list of Graph Formalizations

### Directed Graphs
- `digraph` of Lars Noschinski's [`Graph_Theory` library](https://www.isa-afp.org/entries/Graph_Theory.html) models general directed graphs as a set of vertices (`verts`) and a set of `arcs` with a `tail` and a `head`. It allows multi-arcs. 
 - `Arc_Walk` defines `awalk`, `apath`, `trail`, `cycle`
 - `Vertex_Walk` defines `vwalk`, `vpath`
- `pair_digraph` of Lars Noschinski's [`Graph_Theory` library](https://www.isa-afp.org/entries/Graph_Theory.html) is a simpler representation of directed graphs by a set of vertices (`pverts`) and arcs by a relation `parcs`. (no multi-arcs!)
 - provides a conversion `with_proj` from `pair_digraph` to `digraph`
- In [`Flow_Networks`](https://www.isa-afp.org/entries/Flow_Networks.html) weighted directed [`graph`](https://www.isa-afp.org/browser_info/current/AFP/Flow_Networks/Graph.html)s are represented as functions `edge => 'capacity`.
 - Vertices `V` and arcs `E` are defined
 - arc paths (`isPath`) and distinct arc paths (`isSimplePath`) are defined
- In [`Dijkstra_Shortest_Path`](https://www.isa-afp.org/browser_info/current/AFP/Dijkstra_Shortest_Path/Graph.html) directed graphs (`graph`) are defined as a set of vertices (`nodes`) and set of labelled edges (`edges`) as tuples (`vertex * label * vertex`).
 - arc paths (`is_path`)



### Undirected Graphs
- In Lars Noschinski's [`Graph_Theory` library](https://www.isa-afp.org/entries/Graph_Theory.html) `graph` model undirected graphs as symmetric `digraphs`
- In [`Girth_Chromatic`](https://www.isa-afp.org/entries/Girth_Chromatic.html) Lars Noschinski defines undirected graphs [`ugraphs`](https://www.isa-afp.org/browser_info/current/AFP/Girth_Chromatic/Ugraphs.html) as a set of vertices and a set of undirected edges. Edges are represented as sets of vertices.
 - defines `uwalks`, `ucycles`, 
- In [`Kruskal`](https://www.isa-afp.org/browser_info/current/AFP/Kruskal/) Max P. L. Haslbeck defines [undirected graphs](https://www.isa-afp.org/browser_info/current/AFP/Kruskal/UGraph.html) with edges as a set of [`uprod`s](https://www.isa-afp.org/browser_info/current/AFP/Kruskal/Uprod.html):
 - defines edge paths (`epath`), distinct edge paths (`depath`)
 - defines `cycle`, `decycle`, `forest`, 
 - defines weighted undirected graphs (`uGraph`)
- In [`Kruskal`](https://www.isa-afp.org/browser_info/current/AFP/Kruskal/) Biendarra works with [undirected graphs](https://www.isa-afp.org/browser_info/current/AFP/Kruskal/Graph_Definition.html) as a symmetric directed graph
 - defines edge paths (`is_path_undir`), 
 - defines trees, forests
 - is based on `Dijkstra_Shortest_Path.Graph`


