# Six exact expanding-return nonhalting cylinders

Lean 4.36.0-rc2, 2026-11-27. All six literal one-hole machines below have a locally kernel-checked `never` theorem for every compatible completion, and a `cover` theorem. The 86 theorem is additionally source-accepted in parent-cut CI 46041306854. The other five use the same original-source dependency closure reconstructed from artifacts 15219683851 and 15220415544; their reproducible family-generator CI is dispatched separately. No global canonical roster change is claimed.

All tables have codes [7,a,11,12,15,1,6,18,4,17,f,24], with 24 denoting an undefined slot (25 possible completions).

| Sibling ID | a | f | Primitive blank entry time | Entry | Triplet pump |
|---|---:|---:|---:|---|---|
|28|21|0|6896|A2(39)|single +5|
|39|21|6|7576|A2(41)|pair +12|
|77|23|1|7574|A2(41)|pair +12|
|81|23|17|6896|A2(39)|single +5|
|86|23|11|6892|A2(39)|single +5|
|88|23|19|6894|A2(39)|pair +10|

## Common return structure

A0, A2, B0 and D are the exact section configurations defined in the generated Lean files. The A2 return first enters D(p-4). The common bank routines collect triplets and rotate a six-element suffix cycle; next(s)=(s+1)%6, carry(s)=1 iff s=5. For D(k), put h=k+8, n=k/6, s=k%6. If h is odd, drain B at (2h+2,n,s); otherwise drain B at (2h+11,n+carry(s)-2,next(s)). A0(p) uses n=(p-5)/6,s=(p-5)%6: if p is even drain C at (2p+6,n,s), otherwise at (2p+15,n+carry(s)-2,next(s)). B0(p) uses n=(p-3)/6,s=(p-3)%6,n'=n+carry(s)-1,s'=next(s): if p odd drain A at (2p+6,n',s'), otherwise at (2p+15,n'+carry(s')-2,next(s')). All reached terminal suffix ranks are odd, a fact proved by arithmetic for each branch. Natural subtraction is used and non-underflow is justified where needed by p>=24.

For pair pumps, apply the pair law floor(n/2) times, adding g*floor(n/2) to the exponent, then consume the remaining r=n%2 triplets and terminal rank s. The exact terminal section and offset follow (columns s=1,r=0; s=1,r=1; s=3,r=0; s=3,r=1; s=5,r=0; s=5,r=1).

| bank | 39/77 endpoints |
|---|---|
| A | B0+7, A0+12, A0+6, B0+13, B0+11, A2+15 |
| B | A0+4, A2+9, D+1, B0+13, B0+7, A2+11 |
| C | B0+7, A0+12, A0+8, A2+13, D+3, A0+14 |

| bank | 88 endpoints |
|---|---|
| A | B0+5, A0+10, A2+13, B0+11, B0+9, D+7 |
| B | A0+2, A2+7, D-1, B0+11, A0+14, A2+9 |
| C | B0+5, A0+10, A0+6, A2+11, B0+17, A0+12 |

D-1 requires exponent >=25, guaranteed by the preceding return. This is why the invariant is over four sections, not three. The return exponent is at least 2p on the entire domain p>=24, even in the exceptional case. Sibling 81 needs three changes to reachable terminals from the 86 schema: b62542 -> A0(p+7), a5215 -> A2(p+6), c35221 -> B0(p+10). Sibling 28 has the same endpoints as 86.

## Reproduction and proof status

`Raw14086ThreePhase.md` gives the initial derivation. `generate_raw140_28.js <id>` generates local affine certificates, exact entry chunks, and specialized composition for 28,39,77,81,88 using `raw140_family_recipes.py`, `patch_raw140_81.py`, and `patch_raw140_paired.py`. The local rules are symbolically replayed without reading opaque suffixes, then Lean checks every primitive block exit and induction. Local compiled proofs for all six have the standard axiom profile [propext, Classical.choice, Quot.sound], no sorryAx. The `cutFamily` target regenerates and checks all six against the disjoint three-hole parent audit. The already-accepted `cut86` reduces the exact residual count from 20 to 19; if `cutFamily` succeeds it reduces that count to 14. The independently accepted upstream sibling36 bridge is not included in this target. Six distinct literals account for 150 compatible completed machines; this is not a canonical-parent closure or a BB(6) upper bound.
