# Incremental dependency-pruned FAR search for F421

**Computational exclusion, not a machine verdict or Lean theorem.** The existing canonical DFA size-six search is extended to all reachable canonical DFA sizes 1 through 8 in both orientations. No witness. The restriction is to the existing FAR proof system, whose opposite-side relation has states (l,q) and a single halt state H; this does not exclude arbitrary regular invariants or larger FAR witnesses.

## Search reduction

Let a partial DFA assign some transitions delta(j,b)=l. Keep only the push edges and pull composition rules whose required transition is assigned. Include the fixed halt edges and halt loops. Every DFA completion contains these rules. Their least NFA closure is therefore a lower bound on the closure for every completion. Let z be the least set containing H and closed under backwards 0-labelled edges. If the blank root (0,A) is in z, every completion fails the FAR checker.

For each inserted edge or zero-set fact, retain one sufficient dependency bitset of the assigned DFA transition positions. A base halt fact uses the empty set; push facts and pull rules use their one transition; compositions union the rule and both premise dependencies; backward zero propagation unions the edge and the downstream zero dependency. The resulting root fact remains derivable under any assignment agreeing on those positions. Thus if the returned failure mask omits the current position, backjump across that position without testing its other values. This is not a heuristic cutoff.

The solver incrementally saturates each new DFA assignment. Rules watch their first-premise row and, for each present intermediate vertex, the associated second-premise row. Newly inserted edges trigger both uses. Zero facts propagate on the same agenda. Rollback removes only edges, watches, rules and zero facts added after the parent checkpoint. Facts present at the checkpoint retain their original proofs. All edges are finite (2*N*N, N=6*d+1). Partial saturation may stop on the first root contradiction. The canonical DFS enumerates reachable DFA states in discovery order, with delta(0,0)=0 for the blank initial tape. A minimal reachable DFA can be numbered this way.

## Exhausted search (local C++20)

Build: `g++ -std=c++20 -O3 far_incremental.cpp -o far_incremental`.

For d=1..7 both orientations, and d=8 orientation 0, invoke `./far_incremental d rev 120`. All completed with found=0 and stop=0. For d=7, visited 17,334 and 303,897 DFS nodes respectively; d=8 orientation 0 visited 216,875.

For d=8 orientation 1 use the following mutually exclusive canonical prefixes with the fourth command argument. Each completed with found=0, stop=0:

    0102       76476
    0112       88658
    0120           7
    0121      420266
    0122      392110
    01230     148506
    01231     449765
    01232     448922
    01233     381858
    012340      4540
    012341     63542
    012342     20340
    012343    103869
    012344    401049
    0123450     8979
    0123451   392566
    0123452   463753
    0123453   419614
    0123454   429521
    0123455   436268
    01234560    3706
    01234561  173311
    01234562  158768
    01234563  191720
    01234564  156945
    01234565  190289
    01234566  166966
    01234567  210997

Counts are DFS nodes, not number of full tables. The prefixes exhaust all canonical reachable tables: for d>1 the initial row is 01, next row must discover 2, and each subdivided prefix is partitioned over all existing states and at most one newly discovered state. A stop=1 partial run is not an exhaustion. Initial large branches 0123, 01234, 012345, 0123456 were deliberately split after time limits; the completed child branches are the coverage ledger. Resume output is diagnostic only; use disjoint prefix partitions.

The implementation is currently limited to d<=10 (64-bit NFA rows and 32-bit dependency masks). A future found result must independently pass the existing FAR checker and be connected to the exact source machine.
