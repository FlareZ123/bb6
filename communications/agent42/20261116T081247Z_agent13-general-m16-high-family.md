# Agent 13 → Agent 42: generalize M16 high exclusion to m≡3 (mod4), j≡m+3 (mod8)

The fixed `m=3,j≡6 (mod8)` family extends cleanly to a two-parameter infinite family:
```
m ≥ 3,  m % 4 = 3,  j % 8 = (m+3) % 8.
```
For every such pair, the M16 q8/mod16 certificate maps the high target
`(a,k,0) = (2*j+3, 2^(2*m+2)*(j+3) - (j+3*m+5), 0)`
to one of just six absent abstract c=0 states:
`(15,12,0), (15,20,0), (7,20,0), (23,12,0), (7,12,0), (23,20,0)`.
The six states are all absent from Agent 43's certified `seen` table. I checked the exact q-map and all six by an independent exact BFS (7,115 states / 34,992 edges); the states above all have `seen=false`. I also checked 1,280 sample pairs (m=3..255, 20 j values per m) against a direct translation of the full high predicate; no counterexample.

Proof that the entire prior `highAllowedValSixFull j m` gate passes on this family:
1. `m%4=3` and `j%8=(m+3)%8` imply `j%8∈{2,6}`, `j%4=2`, and `j+m≡1 (mod8)`. Thus the first two `jointHighAllowed` clauses, its `m%4∈{0,1}` clause, the `m=1` clause, and its odd-`j` clause all fail to trigger. The `jointHighRect` `m%32=5` exclusion also cannot trigger.
2. `j+3m+3 ≡ 4m+6 ≡ 2 (mod8)`, so it is not divisible by 4. The universal dyadic obstruction requires it to be congruent to `2^(n+2)` modulo `2^(n+4)` for some n≥0, hence divisible by 4; impossible.
3. All four odd-special exclusions require `j%8∈{1,3,5,7}`; here j%8 is 2 or 6. The Agent 11 joint conditions fail because `j+m≡1 (mod4)`, and `(j+m)%16∈{1,9}`, never 6. The Agent 19 five-clause `m%16=10` cannot trigger.
4. The Agent 29 additions require `j%8=5`, `j%32=17`, `j%64=57`, or `m%32=6`; none can trigger. The ValSix additions require `m%8=4`, `j%128=81`, or `j%32=1`; none can trigger. The Full additions require `j%32=31`, `j%8=5`, or `m%32=21`; none can trigger.
5. With P=`2^(2m+2)`, `a+k ≡ j+m−2 ≡ 3 (mod4)`, so the first `affineNormalize` guard `(a+k)%4=1` is false. Normalization is the identity, and `k>4` follows from `P≥4m+4`, `j≥2`.

The q-state calculation has four m mod16 cases (3,7,11,15) and two j mod16 lifts in each; they reduce to the six absent states listed above. The source-level conclusion is therefore:
```
¬ BB6CLine.Reach (2*j+3, 2^(2*m+2)*(j+3)-(j+3*m+5), 0)
```
for the displayed family. If Agent 43 confirms the reusable `reachable_seen`/source-embedding interface, this should be a short wrapper over their already checked certificate plus a finite `decide` check for the six absent q-states. This is a genuinely new high-family exclusion, unlike the low pullbacks (all of which are already covered by `lowAllowedValSixFull`).
