# Raw56 unary sweep leaf certificates

Four formerly unresolved leaves in the Raw56 E1=0RC children C1=0RD and C1=1LE are now original-source certified nonhalting for every compatible completion. The reusable UnarySweep.lean proves congruence under trailing zero padding of zipper lists, then proves nonhalting from a positive-duration macro invariant without requiring a unit-increment pumping family. The four table-specific proofs start at the actual blank configuration and give exhaustive arithmetic closure using parity, mod 3, or mod 5 invariants of the numbers of ones adjacent to the current symbol in state A.

| Child | DFS index | Theorem | Arithmetic invariant |
|---|---:|---|---|
| C1=0RD | 109 | BB6Coverage.Agent1Raw56RDM109.never | A0: b>=3, a+b even; A1: a odd, b even and >=6 |
| C1=0RD | 117 | BB6Coverage.Agent1Raw56RDM117.never | A0: b>=1, a+b mod5 in {0,4}; A1: a mod5 in {3,4}, b mod5=4, b>=4 |
| C1=1LE | 111 | BB6Coverage.Agent1Raw56LEM111.never | A0: b>=2, a+b mod3 !=2; A1: a mod3 !=0, b mod3=0, b>=3 |
| C1=1LE | 126 | BB6Coverage.Agent1Raw56LEM126.never | same mod5 invariant as M117 |

Here a is the number of consecutive ones left of the head; b is the number right of the head. All remaining tape cells are zero, and the head symbol is specified by A0 or A1. Every macro has a strictly positive exact primitive cost, verified using run0, join0 and the source bridge. All four never theorems locally compiled with Lean 4.36.0-rc2 against artifact 15160313745 (SHA256 6513147b3929ab6b707225b6592a882025e234d498ed8baca40216489b469b3d), and each uses [propext, Classical.choice, Quot.sound]. UnarySweep.never_of_macros uses [propext, Quot.sound]. No native_decide or sorryAx.

These are individual leaves, not parent Covers. Candidate discovery on C1=0RD and C1=1LE used the pinned Agent7 cut.cpp and Agent19 farbank.cpp, cap 1000/lookback 32/depth 6. 182 and 316 open leaves respectively; FAR5 closes 178 and 310, FAR6 closes one and four of the remaining; a sparse width-8 n-gram closes C1=0RD leaf 44 at candidate level (346 configurations). The four above complete the candidate coverage. Next: compile the sparse witness, generate exhaustive sharded canonical certificates and consume both child theorems in the E1=0RC frontier. No global decrement yet.
