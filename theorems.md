# Interesting (Essential) Theorems

This provides a list of essential theorems on graphs whose proofs should be compared among different representations.
Pointers to existing formalizations should be added.

## Digraphs
- The strongly connected components of any graph form a DAG
- Any DAG has a topological numbering
- If every node has at least indegree one, then there is a cycle

## Undirected graphs
- Connectivity is an equivalence relation
- Characterizations of a spanning tree: "minimal connected", "maximal cycle-free", "n nodes and n - 1 edges", "unique walk from every node to every other node"
- In a connected graph there exists a (minimum) spanning tree 
- Subforests form a matroid (e.g. for [UGraph](https://github.com/wimmers/archive-of-graph-formalizations/blob/0f236858175b0dbb895c0714a4e763010ab634c4/Undirected_Graphs/UGraph_More.thy#L282)) 
- Kruskal's tree minor theorem: the finite trees are well-quasi-ordered by the topological minor relation 
    * Uses the definition of a graph minor (G is a minor of H if H can be formed by deleting edges and vertices and by contracting edges)
    * Implies that every property about trees that is preserved by deletion and edge contraction can be characterised with forbidden minors
    * Can be extended to general graphs using tree decompositions (harder)

## Both
- Fleury's algorithm to compute eulerian trails
    * Description:  Consider a graph known to have all edges in the same component and at most two vertices of odd degree. The algorithm starts at a vertex of odd degree, or, if the graph has none, it starts with an arbitrarily chosen vertex. At each step it chooses the next edge in the path to be one whose deletion would not disconnect the graph, unless there is no such edge, in which case it picks the remaining edge left at the current vertex. It then moves to the other endpoint of that edge and deletes the edge. At the end of the algorithm there are no edges left, and the sequence from which the edges were chosen forms an Eulerian cycle if the graph has no vertices of odd degree, or an Eulerian trail if there are exactly two vertices of odd degree. 
    * Tests: degress of vertices, edge deletion and connectivity
- Triangle inequality of path lengths (not quite but e.g. `triangle` in [Prim_Dijkstra_Simple.Directed_Graph](https://www.isa-afp.org/browser_info/current/AFP/Prim_Dijkstra_Simple/Directed_Graph.html))
- Vertices are connected iff there exists a path (e.g. `rtrancl_edges_iff_path` in [Prim_Dijkstra_Simple.Directed_Graph](https://www.isa-afp.org/browser_info/current/AFP/Prim_Dijkstra_Simple/Undirected_Graph.html) vs. Connectivity is the reflexive transitive closure of the edge relation.
- There exists a negative cycle iff there exists a walk with cost negative infinity
- A vertex u is reachable from v iff there exists a finite cost walk from v to u
