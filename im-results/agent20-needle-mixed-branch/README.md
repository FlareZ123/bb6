# Space Needle: mixed-valuation inverse-branch resonance

**Agent 20, 28 November 2026.** Exact paper-level arithmetic establishes a directed incompatibility for all **42 ordered pairs** of distinct valuations in `{3,4,5,6,11,14,17}`, and sharper minimal resonance depths **11** (3→5) and **18** (5→3). These are restrictions on *prepared high-level inverse histories*, not decisions about the authentic blank-start Space Needle orbit or BB(6). The two immediate 3/5 exclusions and generic all-depth condition have Lean source modules and original-source adapters (`MixedValuationDisjoint.lean`, `NeedleMixedValuationSource.lean`); the original-source compilation is pending in manual run [46100959980](https://github.com/FlareZ123/bb6/actions/runs/46100959980). The complete 42-entry exact-period table, CRT existence, and explicit multiplicative orders are paper-level and computationally audited, not yet Lean-source certified.

## Mathematical statement

In the genuine high-level Space Needle map write the shifted counter as `B=d+2`. A valuation-`v` predecessor has shifted counter `P=2^v(2q+3)` and exact source edge
[
L_v B=D_v P+d_v,qquad
L_v=2^{v+1},quad D_v=L_v+3,quad d_v=2^v(2v-3).
]
For `v≥2` the exact incoming-`v` congruence is `D_v | 3B+d_v`, with the ordinary source lower-bound condition `B≥3·2^v+v+3`. This is the source equation already used in the certified all-valuation theorem [Agent20NeedlePotentialSource.allValuationsSource](../agent20-needle-unified-hensel/SpaceNeedlePotentialSource.lean).

**Cross-potential theorem.** Suppose a prepared target `B` admits a valuation-`w` parent and also admits a legal chain of `j` consecutive valuation-`v` reverse edges ending at `P_j`. If `P_j` admits a valuation-`w` parent as well, then
[
oxed{D_wmid(D_v^j-L_v^j)(d_w-d_v).}
]
The formula is over integers, so signed differences cause no ambiguity. Proof: the earlier source-certified chain potential implies
[
L_v^j(3B+d_v)=D_v^j(3P_j+d_v).
]
Subtracting the two `w`-potentials gives the **exact** identity
[
D_v^j(3P_j+d_w)-L_v^j(3B+d_w)
 =(D_v^j-L_v^j)(d_w-d_v).
]
Since both bracketed `w`-potentials are divisible by `D_w`, the necessary condition follows. No assumption about blank-root reachability is used.

At depth `j=1`, `D_v-L_v=3`, hence a mixed switch is impossible whenever
[
D_w
mid3(d_w-d_v).
]
The exact [audit](mixed_branch_audit.py) checks this nondivisibility for all 42 ordered `v≠w` with `v,w∈{3,4,5,6,11,14,17}`. This pairwise conditional applies even when an initial target has *all seven* incoming valuations, as in the existing [six-arm prepared-target construction](../agent20-needle-joint-towers/SIX-DEEP-ARMS.md). A target with both `v`- and `w`-parents cannot switch from its `v`-parent immediately to a `w`-parent for any of these ordered pairs.

## Complete all-depth return schedule for seven valuations

The cross-potential condition is not merely a one-step prohibition. For the seven valuations
\(W=\{3,4,5,6,11,14,17\}\), all seven moduli \(D_v\) are pairwise coprime, and every \(D_w\) is odd. If the target \(B\) already has a valuation-\(w\) parent and has \(k\) consecutive genuine valuation-\(v\) reverse steps to \(P_k\), then the exact potential identity implies
\[
D_w \mid (3P_k+d_w)
\quad\Longleftrightarrow\quad
D_w \mid (D_v^k-L_v^k)(d_w-d_v).
\]
The reverse implication uses \(\gcd(D_w,D_v)=1\) to cancel \(D_v^k\). Define \(M_{v,w}=D_w/\gcd(D_w,d_w-d_v)\). This condition is equivalent to
\[
\left(D_v L_v^{-1}\bmod M_{v,w}\right)^k=1\bmod M_{v,w},
\]
because the modulus is odd and both \(D_v,L_v\) are units. Therefore the **exact possible return depths** for the \(w\)-label along a monochromatic \(v\)-inverse chain are the positive multiples of its finite multiplicative order \(h_{v,w}\), apart from the separate requirement that the end counter is large enough for a positive legal parent.

The complete exact period matrix below is reproducible by the standard-library [audit](mixed_branch_audit.py). Rows are the label \(v\) repeated backwards, columns the alternate label \(w\) which the starting target already admits. An entry \(h\) means that a returned \(w\)-parent is arithmetically impossible at **every** depth \(k\) not divisible by \(h\).

| preceding valuation v / returned valuation w | 3 | 4 | 5 | 6 | 11 | 14 | 17 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | — | 2 | 11 | 130 | 683 | 16,385 | 262,146 |
| 4 | 18 | — | 2 | 130 | 2,049 | 16,385 | 262,146 |
| 5 | 18 | 12 | — | 2 | 683 | 3,277 | 43,691 |
| 6 | 6 | 4 | 66 | — | 2,049 | 16,385 | 131,073 |
| 11 | 18 | 6 | 66 | 65 | — | 16,385 | 131,073 |
| 14 | 9 | 3 | 11 | 130 | 683 | — | 131,073 |
| 17 | 9 | 12 | 22 | 65 | 1,366 | 16,385 | — |

The periods are **sharp as prepared-configuration existence statements**. Given any pair \(v\ne w\) and any finite \(k\) divisible by \(h_{v,w}\), the two simultaneous congruences \(D_v^k\mid3B+d_v\) and \(D_w\mid3B+d_w\) have arbitrarily large positive integer solutions \(B\), because \(D_v,D_w\) are coprime and both are coprime to 3. For sufficiently large solutions, the fixed-point inverse formula gives \(k\) genuine legal positive-\(q\) valuation-\(v\) reverse edges; the period identity then forces the final \(w\) congruence and a legal incoming \(w\)-edge. Hence the table cannot be strengthened to a universal prohibition of all mixed labels. This is a constructive **CRT + positivity** argument, not a claim of blank-root reachability or an all-k Lean theorem.

The most asymmetric entry is \(v=3,w=17\): a prepared target with both a valuation-3 and valuation-17 parent can have no valuation-17 parent along its valuation-3 ancestor chain until at least **262,146** reverse steps. The converse order \(v=17,w=3\) is only **9**. These are structural constraints on a family of high-level inverse branches, not numbers of primitive TM steps.

### Concrete sharp witnesses for the 3/5 pair

For \(v=3,w=5\), the ratio \(19/16\equiv-3\pmod{67}\) has order **11**. The positive shifted target \(B=6639944757198475\) satisfies \(B\equiv-8\pmod{19^{11}}\) and \(3B+224\equiv0\pmod{67}\). It admits both 3 and 5 first parents, 11 genuine valuation-3 reverse edges, no valuation-5 parent at depths 1–10, and a valuation-5 parent after the eleventh step at shifted counter \(1002754604531704\).

For \(v=5,w=3\), the ratio \(67/64\equiv-4\pmod{19}\) has order **18**. The positive target \(B=7155223300615540543431783171417079\) satisfies \(3B+224\equiv0\pmod{67^{18}}\) and \(3B+24\equiv0\pmod{19}\). Its 18 genuine valuation-5 reverse edges have no valuation-3 parent at depths 1–17, and regain one at depth 18 at shifted counter \(3137012685364791692237174865570400\). Both witnesses are audited with exact integers.

## Scope and next proof edge

This identifies an exact *return-time barrier* for two competing valuation labels on one inverse ray and a reusable necessary obstruction for 42 ordered label switches. It improves inverse-grammar pruning, but it cannot exclude an authentic terminal feeder: the resonance examples demonstrate that first-step incompatibility is not perpetual. The generic mixed-depth divisibility theorem has newly authored source-Lean modules but awaits successful CI; the 42 exact periods and their existential sharpness remain paper-level derivations with a reproducible exact Python audit. The pinned original-source CI acceptance of the two immediate 3/5 statements must be checked before claiming source certification. Future value comes from integrating these periodic constraints into actual-root inverse search, not enlarging a static modular table.

Reproduce: `python3 im-results/agent20-needle-mixed-branch/mixed_branch_audit.py` (standard library only). The two Lean files are compiled in the *existing* manually dispatched workflow `.github/workflows/agent20-needle-index-potential.yml`; no new workflow was created.
