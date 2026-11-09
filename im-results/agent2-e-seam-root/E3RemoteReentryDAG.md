# Original D E3 seam: remote-reentry cycle cuts

**Evidence class: exhaustive finite-graph computation, independently reproduced; 9 November 2026.** This new cycle classification is not Lean-kernel checked. The pre-existing 6,399-state safety invariant and original-source physical simulation are Lean certified. The result concerns the finite E3 overapproximation, not the actual blank-tape orbit or BB(6).

## Finite theorem

For the original D table 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---, the certified E3 graph has 6,399 nodes and 7,306 edges, including 128 initial right-seven-bit windows. It tracks tape coordinates [-10,7]. On departure beyond position 7, the abstract graph may reenter at position 7 in **any** of six live states A-F. Its marker and F first-event terminals have no outgoing edges.

For any set S of permitted remote reentry states, retain all ordinary edges and only remote reentry edges labeled by states in S. This restricted graph is **acyclic if and only if A is excluded and at least one of C, D, F is excluded**. The exact 64-subset classification is 28 acyclic and 36 cyclic. Its inclusion-maximal acyclic subsets have longest possible abstract directed paths:

| Allowed right reentries | Longest path in graph edges |
| --- | ---: |
| B,C,D,E | 128 |
| B,C,E,F | 137 |
| B,D,E,F | 82 |

The inclusion-minimal cyclic subsets are {A} and {C,D,F}. The unrestricted graph has 11 nontrivial cyclic components, each containing 78 nodes and abstract right-excursion edges. With no permitted remote reentries, the longest path has 65 edges; with C,D alone, it has 110.

## Radius robustness and bounded forcing

A second independently implemented C++ finite-cylinder builder reconstructs the graph from the literal D rule table for every tracked right radius R=7 through R=16, reclassifying all 64 possible reentry-state subsets. For **each** of these ten finite radii, the minimal cyclic subsets remain A and CDF, and the maximal acyclic subsets remain BCDE, BCEF, BDEF. At R=16 the graph has 1,387,814 states and 1,353,838 edges. The detailed state counts and maximal path lengths are reproducible with [E3RadiusCycleCensus.cpp](E3RadiusCycleCensus.cpp). This is numerical evidence of structural stability under wider windows, and **does not prove** a universal radius theorem.

At the source-certified R=7 graph, the acyclic path bounds give a local forcing statement: any abstract nonterminal path with **at least 138 edges** must contain an A-labeled right reentry or contain right reentries labeled C, D and F **all within that 138-edge window**. Otherwise the entire window would lie within at least one of the three maximum acyclic masks, each of whose longest paths is at most 137 edges. For the actual physical source, this is conditional on the preexisting simulation and counts *abstract* steps rather than primitive time.

## Mathematical implication and precise limits

By the already-certified original-source window simulation, an original E3 trajectory that avoids first events forever must either eventually depart beyond the tracked right boundary and never return, return in A infinitely often, or return in **each** of C, D, F infinitely often. This is a **necessary condition**, not a physical witness or nonhalting classification. An abstract remote edge can represent any finite number of primitive machine steps, so the finite path-length figures are not primitive time bounds.

Actual finite E3 input suffixes can reenter A and F. In direct original-source finite simulation, suffix Y=10101011 first reenters in A at coordinate 7 at core time 15, and suffix Y=1010101011 reenters in F at core time 25. A strategy assuming the problematic reentries never occur is invalid.

The reproducer E3RemoteReentryDAG.py reads Agent31's unmodified ESeamClosedStates.txt and reconstructs every edge from the literal machine table, checks all nodes and seeds, topologically sorts all 64 restrictions, and determines longest path lengths. A separate JavaScript implementation of the same graph gave the same classification. No new Lean proof of the cycle-cut computation is claimed.

**Remaining mathematical obstruction:** control right-excursion histories involving A or all C,D,F, or establish a source-certified authentic-root suffix invariant restricting them. Even the conjecture that every finite E3 suffix has a first event remains unproved. This belongs in im-results/ until formalization and relevance justify promotion.
