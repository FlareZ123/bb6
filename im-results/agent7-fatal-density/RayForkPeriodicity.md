# Six-step inverse-fork periodicity along the canonical #746 even ray

**Agent 7, 2026-11-05.** A new uniform arithmetic obstruction for the original #746 source-C first-reset inverse search. This file contains an exact paper proof, with independently computed examples. The source-machine bridges and the odd-depth forced-parent theorem are already kernel-certified, but **the full six-step modular theorem has not yet been formalized in Lean**. It is an intermediate finding: no original blank-root halting or nonhalting decision follows.

## Definitions and exact identity

For all natural indices (n,j), define the symbolic deficit
[
D_0(n)=n+4,qquad D_{j+1}(n)=2D_j(n)+(n-1).
]
By induction (already Lean-proved in [OddRayDeep.lean](OddRayDeep.lean)),
[
D_j(n)=2^j(2n+3)-(n-1)
       =(2^{j+1}-1)n+(3cdot2^j+1).
]
For any (n,j), use the **signed** integer numerator
[
Z_j(n)=8cdot2^n-2D_j(n)+5.
]
At all levels for which (D_j(n)le4cdot2^n), this agrees with the true positive source first-reset numerator (2U_j(n)+5), with (U_j(n)=4cdot2^n-D_j(n)).

The closed deficit identity gives, **for every n and j without a cutoff**,
[
oxed{D_{j+2}-D_j=3cdot2^j(2n+3),quad
Z_{j+2}-Z_j=-6cdot2^j(2n+3).}	ag{1}
]
This is a direct symbolic identity over integers and does not presuppose reachability.

## The exact per-index period-six theorem

**Theorem (paper proof).** For every (nge4) satisfying (nmod6in{4,5}):

1. At every **odd** depth (j), (Z_j(n)
otequiv0pmod3).
2. At every **even** depth (j), (Z_j(n)equiv0pmod3).
3. For each even (j), the three integers
   [
   Z_j(n),quad Z_{j+2}(n),quad Z_{j+4}(n)
   ]
   have residues **0,3,6 modulo 9, in some order**. In particular, exactly **one** of every three consecutive even-depth ray nodes has a numerator divisible by nine. The other two have 3-adic valuation exactly one.
4. The residue sequence (Z_j(n)pmod9) for even (j) repeats every six depths, as a consequence of (3).

**Proof.** Put (a_j=2^{j+1}-1), (b_j=3cdot2^j+1), so (D_j=a_jn+b_j). For odd (j), (a_jequiv0pmod3), and (b_jequiv1pmod3), giving (Z_jequiv2cdot2^n
otequiv0pmod3). For even (j), (a_jequiv1), (b_jequiv1pmod3), so
[
Z_j(n)equiv 2(2^n-n)equiv0pmod3,
]
the last step using (nequiv4,5pmod6).

For even (j), the integer (Q_j=Z_j/3) exists. Divide (1) by three to obtain
[
Q_{j+2}-Q_j=-2^{j+1}(2n+3).
]
Because (j) is even, (2^{j+1}equiv-1pmod3), and therefore
[
oxed{Q_{j+2}equiv Q_j+(2n+3)pmod3.}	ag{2}
]
Since (nequiv4) or (5pmod6), the increment (2n+3) is congruent to (2) or (1pmod3), respectively. Iterating (2) three times therefore visits all three residues mod3 exactly once. Multiplying by three proves (3), (4), and the full assertion. Signed numerators make these claims valid even when the ray height has passed zero, so positivity is needed only for the subsequent source-Turing-machine interpretation.

## Source-authentic consequence: five forced inverse edges in every complete six-ray block

The original source-C reset predecessor grammar in [FirstInverseComplete.lean](../agent10-cascade/FirstInverseComplete.lean) is complete in both directions. An odd-branch predecessor of any nonnegative target (u) has (3^{t+1}mid 2u+5) for some (tge0). For **near-top targets** (3cdot2^nle ule4cdot2^n), Agent 10's [FourEven.lean](../agent10-cascade/FourEven.lean), theorem `near_top_no_odd_tzero`, excludes (t=0) for every (nge4). Thus an odd parent needs (9mid 2u+5).

For the explicit ray nodes (U_j(n)), a sufficient band condition is (D_j(n)le2^n), which implies (U_j(n)ge3cdot2^n), and (D_j(n)ge3) from the recurrence gives the high even-image band (6cdot2^{n-1}-1le U_j(n)le8cdot2^{n-1}-3). The scale is unique by the source-verified `even_band_scale_unique`. Consequently, under this condition **every source-genuine immediate reset parent of (U_j(n)) is the canonical (U_{j+1}(n)), unless (9mid Z_j(n))**.

By the period-six theorem, in every six-node block (j,j+1,ldots,j+5) with (j) even and **all six deficits (D_{j+i}(n)le2^n)**, *at least five* nodes have exactly one source-genuine immediate reset parent, namely the next ray node. There is exactly one level at which an odd-branch fork is arithmetically possible. This strengthens the earlier [OddRayForced.lean](OddRayForced.lean) theorem at even positions where the numerator has valuation exactly one.

The source-root reset-chain equivalence in [ResetChain.lean](../agent10-cascade/ResetChain.lean) transports each of those **forced** inverse edges into a true blank-derived (\operatorname{ReachC}(2,0)) iff for its two endpoints, exactly as done in [OddRayForced.lean](OddRayForced.lean). **This full five-of-six quantified consequence is a paper derivation and has not yet been source-Lean-compiled.** It is a property of the inverse graph, and does not assert that the actual blank-origin machine reaches any of the potential fatal gates.

For each fixed depth (j), as (n	oinfty) in either surviving sector, the dyadic band condition eventually holds. Moreover, at the unique (9)-divisible even level of a fixed six-block, the (t=1) odd candidate eventually lies in the admissible band, by the strict scaled dyadic inequality already analyzed in [README.md](README.md). Thus for sufficiently large (n) at a given fixed six-block, exactly one of the six nodes actually has two or more source-genuine predecessors. The block length cannot be held fixed while (j	oinfty) without increasing (n) to retain the high-band condition.


## First possible fork phase: an exact mod-18 table

The six surviving fatal-index classes modulo 18 completely determine the first possible 9-divisible *even* ray-depth phase. Direct modular reduction (a six-case hand check following (2)) gives:

| Fatal index `n mod 18` | `Z_0 mod9` | `Z_2 mod9` | `Z_4 mod9` | Unique potential odd-fork depth `j mod6` |
|---:|---:|---:|---:|---:|
| 4 | 0 | 6 | 3 | 0 |
| 5 | 0 | 3 | 6 | 0 |
| 10 | 6 | 3 | 0 | 4 |
| 11 | 6 | 0 | 3 | 2 |
| 16 | 3 | 0 | 6 | 2 |
| 17 | 3 | 6 | 0 | 4 |

The relative phases agree with the earlier exact source-parent arguments: n%18=10,17 have four forced even inverse predecessors (Agent10 `FourEven.lean`), and n%18=11,16 have two forced levels (Agent7 `SecondEven.lean`). Thus the six-step modular theorem **explains and extends** those earlier finite-depth arithmetic patterns in one formula. A potential odd fork at a phase is only an arithmetic *necessary* condition; actual parent existence still requires the dyadic band. No blank-root reachability conclusion follows from the phase table.

## Independent modular diagnostics

A direct integer calculation of (Z_j(n)mod9) (not a proof) for (j=0,2,4,6,8,10,12,ldots) gives:

| (n) | (nmod6) | First repeating three even-depth residues modulo 9 |
|---:|---:|---|
| 100 | 4 | 6, 3, 0 |
| 101 | 5 | 6, 0, 3 |
| 202 | 4 | 0, 6, 3 |
| 203 | 5 | 0, 3, 6 |
| 1000 | 4 | 6, 3, 0 |
| 1001 | 5 | 6, 0, 3 |

These correspond directly to the algebraic increment in (2).

## Why this matters

The earlier exact-index density theorem in [FatalHenselResidue.lean](FatalHenselResidue.lean) controls how rarely a **fixed level** has high 3-adic valuation as fatal index varies. This new fact controls all inverse depths **at any fixed fatal index** and shows a deterministic six-step alternation between one potential fork and five uniquely forced steps while the high band persists. It suggests treating compressed six-step inverse packets as the basic nodes of a root-sensitive backward-language argument.

**Next rigorous step:** formalize this integer modular theorem in Lean using `OddRayDeep.deficit_closed`, `OddRayForced.odd_ray_root_iff`, and the exact `ResetParent` grammar, then build a lossless six-packet inverse closure for *all* blank-genuine ancestors rather than assuming a ray only. The non-ray odd branches at allowed forks are the outstanding obstruction. The original #746 blank-root halting problem and BB(6) remain open; this is not an upper bound or whole-machine decision.
