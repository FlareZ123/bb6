# Sevenfold tighter Sheep E exponent inverse cone

Agent 14, 2026-11-05. **Intermediate mathematical result.** The exact finite arithmetic certificate passes locally; the complete statement has a paper proof using the authentic Sheep first-even return equations of Agent16's source bridge (original source CI 41505950547). A single all-k source-integrated Lean `EvenReach` theorem for this new family is still missing. Sheep and BB(6) remain open.

## Statement and exact inverse graph

For every natural k, with j=648+17496*k, the genuine Sheep even-section blank entry 10 cannot reach 2^j. The previous certificate closed j=648+122472*k, so this improves that exponent-class density by factor 7, with incremental density 6/122472=1/20412. The new six classes are disjoint by exact gcd compatibility from the 15 other E progressions recorded in Agent14/Agent16 notes. External priority is not asserted.

Split k=7q+r, r=0,...,6, so j=J_r+122472q, J_r=648+17496r. Define exact rational-exponential nodes
```
R(j) = 2^j
X(j) = (2^(j+8)-1228)/2187
Z(j) = (2^(j+10)-16576)/3483
```
For r=0,1,3,4,5,6 the complete E inverse graph has R -> X labelled (hidden h=5, source valuation a=2), and X has no incoming E parent. For r=2, there is one further R -> Z edge labelled (h=3,a=6); X and Z both have no incoming parent. All nodes are distinct even positive integers above the actual blank-origin even seed 10. The arrows indicate possible incoming source as the next inverse-graph node; the E forward edges run in reverse. The finite inverse-DAG induction rules out reachability of all roots from 10.

## Verified complete-period certificate

| r | base J | nodes | edges | low valuations | full-period samples | special rows |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 648 | 2 | 1 | 57 | 194 | 7 |
| 1 | 18144 | 2 | 1 | 57 | 194 | 7 |
| 2 | 35640 | 3 | 2 | 74 | 307 | 8 |
| 3 | 53136 | 2 | 1 | 57 | 194 | 7 |
| 4 | 70632 | 2 | 1 | 57 | 194 | 7 |
| 5 | 88128 | 2 | 1 | 57 | 194 | 7 |
| 6 | 105624 | 2 | 1 | 57 | 194 | 7 |
| **Total** | | **15** | **8** | **416** | **1471** | **50** |

The largest exact multiplicative order was 74358. The standard-library certificate found 73 distinct low-valuation odd moduli; an independent SymPy `n_order(2,m)` check agreed for all 73. Seven literal five-step ordinary F-predecessor paths were verified, each with a=0 at the seven J bases. All inverse-graph edge formulas were tested against the actual first-even formula at q=0,1. The entire finite certificate passed.

For each node Y=(2^(j+s)+b)/d, the congruence 2^122472=1 modulo d*3^H, where H=v3(Y(J)-1)+1, and a nonzero numerator modulo the same modulus uniformly bound hidden h: H=6 at R, H=1 at X or Z. For each h, put D=d*3^h, C=D+2^h*(b-d), S=s+h. The generic predecessor congruence is
```
2^(j+S+1) = D*(2a-1)-2C (mod D*(2^(a+1)+1)).
```
For a beyond the exact row threshold A, the odd K(a)=D*(2a-1)-2C satisfies 1<K(a)<2^a, which persists because K(a+1)=K(a)+2D and 2^A>=2D. The published mathematical Lean lemma `SheepOddGap.no_power_signed_small_odd` excludes every such a. Every remaining 1<=a<A is checked over all o/gcd(o,122472) distinct periodic k residues, with o the exact multiplicative order of 2 mod D*(2^(a+1)+1). This proves each of 416 table classifications uniformly for all q.

For the exceptional odd-part-three source, the exact equation is 3D*2^a+D*(a+3)-C=2^(j+S). The checker verifies all three base exponential-gap inequalities from the earlier seven-cone proof for every of the 50 rows; they persist for all later j and exclude every source a. The original source inverse algebra covers generic and exceptional sources exhaustively. Thus the finite acyclic predecessor lists suffice for the genuine even entry 10.

## Reproduction and remaining formal work

This invocation locally ran the standalone Python 3 standard-library certificate `sheep648_tight_period.py`, SHA256 `8bd2fd495be48baea92e0fcb4a59ba04336370379398d980c0aea8a7171b3b53`. It is available as a separate user artifact and has not yet been added as repository source. A complete methodological report is also a separate user artifact `Sheep648TightPeriodResearch.md`. The source-connected finite-DAG theorem is `im-results/agent14-sheep-seven-cones/SheepSourceFiniteInverseDAG.lean`, previously certified in original-source CI 42083000740. The earlier 648 source-integration dossier is `im-results/agent14-sheep-seven-cones/SOURCE-648-INTEGRATION.md`.

New local Lean 4.36.0-rc2 modules `SheepGenericSourceHigh.lean`, `Sheep648AllHigh.lean`, `SheepSpecialSourceTransport.lean` compiled without sorry and only standard axioms, respectively proving the source-equation generic high-a transport, all seven previous 648 high-a cases, and exceptional equation normalization. The local sources await repository transfer and a full genuine-E `EvenReach` assembly. No complete Sheep or BB(6) result is claimed.
