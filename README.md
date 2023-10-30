# Parallel Composition
A SAT-encoding for retrieving all paths at a given depth from the parallel composition of a graph in Python using z3Py.

## Constraints for a Individual Automata

Given an automata, we can find its underlying graph $G(V,E)$. Our aim is to generate SAT constraints to retrieve all paths from the graph such that depth is $k$. We consider *stutter transitions* which are essentially self-loops. By depth, we denote the number of transitions in the path.

### INIT Clause
For all initial states, must include either of the outgoing edges in depth 1. Let us assume that the function $T(X)$ returns the outgoing transitions from the locations in set $X \subseteq V$, $V_{init} \subseteq V$ is the set of initial locations, and subscript denotes the depth at that transition.

$\bigvee_{t \in T(V_{init})}{t_1}$

### EXCLUDE Clause
If one edge is active at a given depth, no other edge can be active at that depth.

$\bigwedge_{1 \leq n \leq k}{\bigwedge_{i \in E}(i_n \implies -\bigvee_{j \in E\setminus i}{j_n})}$

### NEXT Clause
If an edge is active at a given depth, must include either of the outgoing edges from that location in the next depth.

$\bigwedge_{1 \leq n \leq k-1}{\bigwedge_{i = (u,v) \in E}(i_n \implies \bigvee_{j \in T(v)}{j_{n+1}})}$

### DEST Clause
At depth $k$, the edge must be an incoming edge of the location. Let us assume that the function $S(X)$ returns the incoming transitions to the locations in set $X \subseteq V$, and $V_{dest} \subseteq V$ is the set of destination (forbidden) locations.

$\bigvee_{t \in S(V_{dest})}{t_k}$

## Negation Clause

If the solver has retrieved a path, then we negate the path and add that constraint to the solver to return the next path. In our setting, the path retrieved is in the form of an array of Boolean variables. Suppose $\Pi$ is the array of all Boolean variables that are true for the particular model that the SAT solver has returned. The constraint for path negation is as follows:

$-\bigwedge_{x \in \Pi}{x}$

## Flow
