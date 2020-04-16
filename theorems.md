# Interesting (Essential) Theorems

This provides a list of essential theorems on graphs whose proofs should be compared among different representations.
Pointers to existing formalizations should be added.

## DAGs
- The strongly connected components of any graph form a DAG
- Any DAG has a topological numbering

## Undirected
- Connectivity is an equivalence relation
- Characterizations of a spanning tree: "minimal connected", "maximal cycle-free"
- In a connected graph there exists a (minimum) spanning tree 
- Subforests form a matroid (e.g. for [UGraph](https://github.com/wimmers/archive-of-graph-formalizations/blob/0f236858175b0dbb895c0714a4e763010ab634c4/Undirected_Graphs/UGraph_More.thy#L282)) 

## Both
- Triangle inequality of path lengths (not quite but e.g. `triangle` in [Prim_Dijkstra_Simple.Directed_Graph](https://www.isa-afp.org/browser_info/current/AFP/Prim_Dijkstra_Simple/Directed_Graph.html))
- Vertices are connected iff there exists a path (e.g. `rtrancl_edges_iff_path` in [Prim_Dijkstra_Simple.Directed_Graph](https://www.isa-afp.org/browser_info/current/AFP/Prim_Dijkstra_Simple/Undirected_Graph.html) vs. Connectivity is the reflexive transitive closure of the edge relation.
