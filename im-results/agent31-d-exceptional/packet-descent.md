# D Cryptid arbitrary-tail packet transducer with a strict decreasing potential

**Intermediate source-derived mathematical result, 2026-11-03.** The B and E equations below directly specialize original-source Lean-certified universal raw-transition theorems. The abstract well-founded recurrence is locally kernel-checked with standard axioms. The entire combined source model is awaiting one end-to-end original-source import, and no new certified blank-root decision, lower bound, or BB(6) result follows.

## Infinite parameterized packet language

Use the original source machine `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`, physical F/0 section notation `I_a(y)`, and `P_q=(01)^q`. For arbitrary finite binary tail `Y`, and all natural q,p, define

```text
M(a,q,p;Y) := I_a(P_q 0 1^p Y).
```

The notation interprets every finite tail as followed by *physically implicit* blank zeros; trailing explicit zeros are observably equivalent (Agent32's source-certified `source_congr`).

Two existing original-machine source-certified macros yield **exact identities for ALL q,p,Y** in the stated guards:

| Input residue/guard | Original-machine next F/0 endpoint | Exact primitive transitions | Effect on rank q+p |
|---|---|---|---|
| `a=3k+2, q≥1` (B) | `M(8k+10,q-1,p;Y)` | `12k²+49k+40` | decreases by exactly 1 |
| `a=3k+4, p≥3` (E) | `M(8k+9,q+2,p-3;Y)` | `12k²+49k+58+6q` | decreases by exactly 1 |

**Derivation:** In the B case, `P_q=0(10)^(q-1)1`. Apply Agent31's universal `full_B`, remove the first zero, then absorb the leading one into the unary prefix, preserving the entire remaining right word. In the E case, `P_q 0 1^p Y = 0 (10)^q 111 1^(p-3)Y`. Apply Agent32's universal `full_E_triple_pairs k q (1^(p-3)Y)`. Its original-source proof has [successful CI 41413674846](https://github.com/FlareZ123/bb6/actions/runs/41413674846). Both transformations retain the *same arbitrary untouched Y*. Exact physical padding at the far right must be taken modulo the original/source-verified observation relation.

Thus, **any consecutive sequence containing only these guarded B/E packet transitions has at most q+p successful moves** from its initial packet parameters before it exits the guarded recurrence. This bounded phase assertion is purely symbolic and independent of the size of a, which may have millions of digits. The endpoint might be an A section, a B section with q=0, or an E section with p≤2. Exiting the packet recurrence is **not** equivalent to original Turing-machine halting.

[PacketRank.lean](./PacketRank.lean) encodes the exact B and E count changes, proves `advance_rank` that `rank(next)+1=rank(current)`, and defines `normalizeWithCount` by a well-founded recursive call accepted by Lean's termination checker using this strict decrease. Lean 4.36.0-rc2 audits for these two declarations contain only `[propext, Quot.sound]`; the original-source B/E raw machine identities remain separate imported proof obligations. [generic_packet.py](./generic_packet.py) independently simulates **1,440** random arbitrary-tail physical raw B/E cases with exact times and complete tapes, all passed (RNG seed 130057). This is an independent experimental crosscheck.

## Full small-tail boundary for Y = 0 1^6

The nonregular second-return exception of [two-return-classification.md](./two-return-classification.md) has exactly this M shape with `q=2`, `p=2Q-3≥3`, and `Y=0 1^6`. For this fixed Y, existing original-source A, B, and E theorems give a concise *boundary routing table*. Let n=3k+3 for A, set m=4k+3, r=floor(p/3), d=q+4r, `P=12k²+41k+32`, `C=2q+r(6(m+q)+41)+12r(r-1)`.

| Guard | Next F/0 endpoint | Exact primitive transitions | Class |
|---|---|---|---|
| B, q=0, any p | `I_(8k+9+p)(0 1^6)` | `12k²+49k+40` | L |
| A, p=3r | `I_(8k+17+2d)` | `P+C+2(m+d)+6` | pure L |
| A, p=3r+1 | `I_(8k+29+2d)` | `P+C+2+6(m+d+1)+41+6(m+d+5)+41+2(m+d+9)+6` | pure L |
| A, p=3r+2 | `I_(8k+11+2d)((01)^3 1^2)` | `P+C+2(m+d)+24` | L |
| E, p=0 | `I_(8k+5)(0 1^(2q+12))` | `12k²+49k+50+4q` | L |
| E, p=1 | `I_(8k+9)((01)^(q+4) 1^2)` | `12k²+49k+64+6q` | L |
| E, p=2 | `I_(8k+5)(0 1^(2q+6) 01010 111)` | `12k²+49k+68+4q` | new packet N, outside L |

The A entries use Agent35's arbitrary interleaved A-word code theorem with q initial `10` tokens and r following `111` tokens, plus the separately original-source-audited `110111` exceptional A completion for residue p≡2. The B and E low-p p=0/1 rows use original-source certified `full_B`, `full_E_pairs`, and `full_E_triple_pairs`.

**Important source caveat:** The E,p=2 row uses Agent37's general all-q `E110111Pairs`, locally Lean-verified against the literal raw table but awaiting the complete original `Boundary.lean` source-import CI. Earlier Agent32 q=0 is authenticated; the all-q original-source chain remains to be independently audited. The E,p=2 row should not be counted as a fully imported original-source theorem.

The independent raw-TM [packet_descent.py](./packet_descent.py) checks **1,980** exact physical *first* F/0 one-return cases for a=2..31, q=0..5, p=3..13 across B, A and E, all passed. [packet_boundary.py](./packet_boundary.py) separately checks the three E low-p cases for 396 parameter combinations k=0..11, q=0..10, p=0..2, all passed.

**Structural implication:** Starting with any fixed-Y=`0 1^6` M packet, the B/E inner phase can spend at most q+p guarded returns; any A or B(q=0) or E(p=0/1) exit returns to L, while the remaining E(p=2) exit produces a specific new packet class N. This reduces one difficult unbounded-return problem to a small handful of precisely described boundary cases, independently of the huge unary parameter. It does not prove a complete reachable-word invariant or exclude a future F-on-one halt.

## Relation to the four genuine D-root research programmes

Agent3's original-root theorem gives genuine physical unary seeds 5,9,15,39. The E exception after two exact source-return endpoints takes the form M(a,2,2q-3;0 1^6), so the potential is `2q-1`: a q=4 exceptional entry has rank 7, and q=8 rank 15. These bounds are conditional **per packet phase**; the actual blank root has not been formally connected to the long modeled section indices.

The independent three-/four-return hierarchy in [third-return-classification.md](./third-return-classification.md) consists of special cases of this larger packet transducer. A productive next target is the residual E,p=2 packet N with its embedded `01010` marker. Establish a source-certified reduction from N back to L or to another family with a decreasing measure. Avoid assuming a bounded packet phase proves total nonhalting of the original machine or any BB(6) upper bound.

The original-source-import workflow currently fails at GitHub runner initialization, without job logs; one should not equate the local Lean rank certificate or individual source-verified B/E lemmas with a fully imported proof of the entire combined case table. This entire directory belongs in `im-results/` pending a real frontier contribution and external novelty review.


### The exceptional E,p=2 output remains a generalized packet

The final E,p=2 word is *exactly* another member of the **arbitrary-tail** M grammar:
```text
I_(8k+5)(0 1^(2q+6) 01010 111)
  = M(8k+5, 0, 2q+6; 01010111).
```
The equality is a literal right-word identity (the new untouched tail is `(01)^3 11`). Hence the two universally source-certified B/E descent rules remain available after that E,p=2 boundary, now with a changed tail Y. Its new potential is `2q+6`, which may be *larger* than the old `q+2`; therefore the decrease proven for each guarded packet phase **cannot** be extended across this boundary without a stronger global invariant or amortized potential. A credible next step is a finite tail-state or 3-adic transformation controlling this reset. No global termination conclusion has been established.
