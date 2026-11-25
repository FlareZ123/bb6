# Raw41: certified descendant cuts and canonical frontier

Parent: `1RB---_1RC---_0RD---_1LD1RA_------_------` (seven holes); first query A1 at step 6. The original two-query partition proves a weighted bound of 16 or an explicit residual. Its six first-level cycle leaves, 19 halt branches, 166 second-level cycle leaves and five FAR leaves cover 3,554,687,500 of 6,103,515,625 physical completions (58.24%). These are disjoint branch cardinalities, not a count of arbitrary symmetry classes. There are 261 physical five-hole residuals and 153 canonical representatives.

**Current checked descendant closures:** LC0LB (bound 229) and LC0RA (bound 117). Each is a five-hole cylinder containing 25^5 physical completions. The new LC0RA result includes two new all-time proofs, one previously derived sweep, 23 finite-automaton certificates and an exhaustive canonical first-hole tree. No actual root remains open inside that child. The remainder of Raw41 is still open; these are alternative refinements of the accepted 77-entry parent roster, not a global BB(6) upper bound.

## LC0RA: complete child closure

Child `1RB0LC_1RC---_0RD0RA_1LD1RA_------_------`. The existing canonical enumerator generated 247 splits, 4512 cycle leaves, 1140 last-hole leaves and 26 initially open leaves. The candidate maximum weighted score is 117 (116 ordinary steps, final query, zero blank delay); the checked theorem establishes the upper bound, not an exact attaining lower bound. The 23 FAR witnesses are in [child4/far.txt](child4/far.txt); the other three leaves have uniform original-semantics nonhalting proofs:

| Index | Literal partial table | All-time mechanism |
|---|---|---|
| 0 | `1RB0LC_1RC0LE_0RD0RA_1LD1RA_1LF0LE_---0LB` | [regular-language positive return invariant](Raw41LC0RAGrammar0.lean) |
| 1 | `1RB0LC_1RC0LE_0RD0RA_1LD1RA_0LF1LE_---0LA` | [previous sweep](Raw41LC0RASweep2.lean), return cost 16n+17 |
| 2 | `1RB0LC_1RC0LE_0RD0RA_1LD1RA_1LB1LF_0LB---` | [two-phase sweep](Raw41LC0RACounter2.lean), return cost 72n+64 |

For index 0 the blank run enters the invariant at step 10. On the left, a GoodTail is a terminal singleton 1 preceded by zero-separated runs of at least two ones. The A invariant has current 0 followed by 10 and a GoodTail, or 0 and a nonterminal GoodTail; the right word has no adjacent ones. The E invariant has a run of ones followed by 0 and a GoodTail, or the special 1010 prefix followed by a nonterminal GoodTail; the right starts with zero. Every invariant configuration reaches another invariant configuration in 1–10 exact transitions. The nonterminal restriction prevents a false terminal case. This is an all-time proof, without a finite scan or a conjecture about the counter's numerical evolution.

For index 2 write P=101, with zipper left including the current cell. At time 10 the machine is in E with left P and right 0. F(k) has left P^(k+1); G(k) has left 10101 P^(k+1). Both have right 0. F(k) reaches G(k) in 6(k+1)+13 steps; G(k) reaches F(k+4) in 12(k+1)+33 steps. Thus F(4n) reaches F(4(n+1)) in 72n+64 steps. The two new leaves' never theorems use only propext and Quot.sound.

The 24 generated branch modules, Raw41LC0RAClosed and [Raw41LC0RAGraft.lean](Raw41LC0RAGraft.lean) compiled locally with Lean 4.36.0-rc2 against canonical77-certified artifact 14997966221 from run 45554648116 (SHA256 b55e4c939da70aaa4d2f50f5721b9183ab776682f1b682f647ee27aa6cc5da17). The existing CanonicalPartial and Raw41TwoCut/CanonicalCut source were compiled on the same object closure. The kernel proves `Raw41LC0RA_empty` and `Raw41LC0RA_bound : TNFQuotientCompatible Raw41LC0RA_p m → WeightedBound 117 m`. The graft checks exact unique membership in the 229-entry two-query refinement, leaves 228 entries and exports the mixed-bound ExactBB6 consumer. It also checks the distinct prior LC0LB membership and gives a 227-entry joint roster **conditional on the explicitly supplied LC0LB bound**. All printed graft and child-bound axioms are [propext, Classical.choice, Quot.sound]. This is local accepted-artifact-backed checking, not a fresh full-repository source CI audit.

## Earlier LC0LB closure

Child `1RB0LC_1RC---_0RD0LB_1LD1RA_------_------`. The prior exhaustive tree has 287 splits, 1394 last-hole leaves, 5172 cycle leaves and 32 initially open leaves. Its 31 FAR witnesses are in child2/far.txt; index 29 is [the exact sweep proof](Raw41LC0LBSweep.lean) (entry 40; E-state zipper l=01(011)^n, r=100(1)^(n+3), return cost 8n+43). Previous local artifact-backed compilation established `Raw41LC0LB_bound` at 229 and `Raw41LC0LBGraft` (229→228). The current new joint graft retains that bound as a premise instead of silently assuming the other local build was linked.

## Reproduction

Use the existing enumerator in ../agent19-raw40-cut, not a new simulation framework. In this directory:

```sh
g++ -O3 -std=c++20 ../agent19-raw40-cut/enumerate_canon.cpp -o enumerate
(cd child4 && ../enumerate '1RB0LC_1RC---_0RD0RA_1LD1RA_------_------')
python gen_children.py child4 Raw41LC0RA 117 '1RB0LC_1RC---_0RD0RA_1LD1RA_------_------'
```

Compile CanonicalPartial, Raw41LBLA, generated Raw41TwoCut, Raw41CanonicalCut, the three LC0RA sweep/grammar source modules, Raw41LC0RABase, the 24 Raw41LC0RABranchNN modules, Raw41LC0RAClosed and Raw41LC0RAGraft on one coherent LEAN_PATH. For the earlier child, use child2, Raw41LC0LB, bound 229 and its literal table above. The Python generator and C++ search are untrusted; Lean checks every certificate, exact table correspondence, first-hole split, blank-delay charge and the retained complement.

The original five second-level FAR leaves are A1/B1=0LB/0LA (0012101), A1/C1=0RC/0RC (000), A1/B1=1LA/0LD (00101), A1/B1=1LA/1RB (000), A1/C1=1RC/0RC (000). Raw41LBLA.lean proves the first directly. `python generate_two.py` generates Raw41TwoCut.lean; Raw41CanonicalCut proves the generic ordinary-to-canonical checker implication and the 153/229 roster counts.

## Next obligation

Close the other canonical Raw41 children; do not repeat discharged LC0RA/LC0LB subtrees. The existing LB0LC candidate bank and three dedicated sweep/counter sources are the next near-complete child, pending actual integration. The universal maximality proof still requires every other retained representative at the exact champion score. 
