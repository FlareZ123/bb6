# Nine-lift diagnostics for the exceptional t=1 feeder at r=886

**Status: exact finite BigInt diagnostics only; no all-index root exclusion.** This note complements `FeederExceptional887.md`. The fixed residue class `n mod1458=886` splits into nine subresidues `n=886+1458k mod13122), k=0,…,8. Sampling only `n=886+13122T` sees k=0 and misses the other eight lifts.

For each k, exact BigInt inverse-tree enumeration was run at `n₀=886+1458k+13122T`, T=0,1,2,10:

| k | n₀ | tree nodes, T=0,1,2,10 | edges, T=0,1,2,10 | max depth, T=0,1,2,10 | sampled topology |
|---:|---:|---|---|---|---|
| 0 | 886 | 10,10,10,10 | 9,9,9,9 | 7,7,7,7 | stable |
| 1 | 2344 | 19,15,29,15 | 18,14,28,14 | 8,8,18,8 | changes |
| 2 | 3802 | 20,14,15,14 | 19,13,14,13 | 10,9,10,9 | changes |
| 3 | 5260 | 10,10,10,10 | 9,9,9,9 | 7,7,7,7 | stable |
| 4 | 6718 | 21,14,15,14 | 20,13,14,13 | 12,7,7,7 | changes |
| 5 | 8176 | 13,12,12,12 | 12,11,11,11 | 8,7,7,7 | changes |
| 6 | 9634 | 11,11,11,11 | 10,10,10,10 | 7,7,7,7 | stable |
| 7 | 11092 | 14,14,14,14 | 13,13,13,13 | 7,7,7,7 | stable |
| 8 | 12550 | 11,11,11,11 | 10,10,10,10 | 7,7,7,7 | stable |

Across these samples, the initial feeder `x=oddPre n (fatal n)` has `v₃(2x+5)=0` in every lift and sample. Thus its own odd-parent arm is absent in these representatives; its first inverse parent is the even arm. Nevertheless, the deeper inverse trees can branch and vary substantially: the largest sampled tree has 29 nodes and depth 18 (k=1,T=2).

The five lifts k=0,3,6,7,8 retain their sampled topology across the four T values; k=1,2,4,5 do not. This is not a proof that the stable topologies persist for all T, nor a uniform bound on the inverse cone. A full proof must classify every parent at every node for each lift and control further 3-adic variation.

The exact enumerator is `EnumerateExceptionalFeederTrees.mjs`, which now samples all nine lifts for each of the eight exceptional residues. The finite tables are diagnostic evidence only; no BB(6) conclusion follows.
