# Space Needle: mixed-valuation inverse-branch resonance

**Agent 20, 28 November 2026.** Exact paper-level arithmetic establishes a directed incompatibility for all **42 ordered pairs** of distinct valuations in `{3,4,5,6,11,14,17}`, and sharper minimal resonance depths **11** (3→5) and **18** (5→3). These are restrictions on *prepared high-level inverse histories*, not decisions about the authentic blank-start Space Needle orbit or BB(6). The two immediate 3/5 exclusions have dedicated Lean proofs and original-source adapters (`MixedValuationDisjoint.lean`, `NeedleMixedValuationSource.lean`); the original-source compilation is pending in manual run [46100959980](https://github.com/FlareZ123/bb6/actions/runs/46100959980). Other 40 pair instances and unbounded-depth order equivalences are not yet Lean-source certified.

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

## Exact two-valuation resonance depths

For the pair `v=3,w=5`, `L_v=16,D_v=19,d_v=24`, `D_w=67,d_w=224`, and `gcd(67,200)=1`. Any cross-return after `j` consecutive `3`-edges requires
[
19^jequiv16^jpmod{67}
quadLongleftrightarrowquad
(-3)^jequiv1pmod{67}.
]
The multiplicative order of `-3` modulo 67 is **11** (the eleventh power is 1 and all powers 1 through 10 are not). Thus a `5`-parent of any `3`-ancestor can occur only at reverse depths divisible by 11. This is **sharp** for positive genuine prepared edges: the explicit target `B=6639944757198475` admits both 3 and 5 first parents, 11 consecutive legal 3-parents, no 5-parent at depths 1–10, and a legal 5-parent at depth 11. The final shifted counter is `1002754604531704`.

For `v=5,w=3`, `L_v=64,D_v=67,d_v=224`, and `D_w=19,d_w=24`. The corresponding necessary condition is
[
67^jequiv64^jpmod{19}
quadLongleftrightarrowquad
(-4)^jequiv1pmod{19}.
]
The multiplicative order of `-4` modulo 19 is **18**. The CRT-built target `B=7155223300615540543431783171417079` admits both 3 and 5 incoming edges, 18 legal reverse 5-edges, no 3-parent at depths 1–17, and a 3-parent at depth 18. The final shifted counter is `3137012685364791692237174865570400`.

The witnesses are obtained constructively: choose `B≡-8 (mod 19^11)` and `3B+224≡0 (mod67)` for the first direction; choose `3B+224≡0 (mod67^18)` and `3B+24≡0 (mod19)` for the second. CRT gives the displayed least nonnegative representatives, and direct positive-cofactor checks make every edge a legal original high-level prepared edge. The source transition formula is imported from the existing original-source proof, not a different simulator.

## Scope and next proof edge

This identifies an exact *return-time barrier* for two competing valuation labels on one inverse ray and a reusable necessary obstruction for 42 ordered label switches. It improves inverse-grammar pruning, but it cannot exclude an authentic terminal feeder: the resonance examples demonstrate that first-step incompatibility is not perpetual. The unbounded-depth statement and 42-case arithmetic table are mathematical derivations with a reproducible exact Python audit, not exported Lean theorems. The pinned original-source CI acceptance of the two immediate 3/5 statements must be checked before claiming source certification. Future value comes from integrating these periodic constraints into actual-root inverse search, not enlarging a static modular table.

Reproduce: `python3 im-results/agent20-needle-mixed-branch/mixed_branch_audit.py` (standard library only). The two Lean files are compiled in the *existing* manually dispatched workflow `.github/workflows/agent20-needle-index-potential.yml`; no new workflow was created.
