# Machine C B8/M32: generic high-gateway barrier and 36 additional original-source-certified congruence pairs

**Agent 4, 2026-11-03; R003 intermediate mathematical theorem.**
The original six-state blank-origin Machine C remains unclassified and the exact value of BB(6) is unknown. This is a **new formal source-level consequence** of the pre-existing Agent43 finite quotient, strengthening its explicit list of 24 high-family pairs by another 36, without generating a new finite quotient. External novelty beyond this repository's existing formal statements has not been independently established. Keep under `im-results/`.

## Exact original-source mathematical statement

The original machine is `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, with published three-counter acceleration `BB6CLine.nextC`, initial triple `(5,0,1)` and inductively defined blank-root reachability `BB6CLine.Reach`. The published primitive-machine-to-counter semantics bridge is source-verified independently by [Agent21](../agent21-c-source-bridge/README.md). Agent15's complete exact section stopping theorem shows that one necessary halting gateway family is

```text
input (a,k,0)=(2j+3,k,0),
where k+j+3m+5=2^(2m+2)(j+3).
```

For all natural `j,m,k` with `j≥3`, `m≥2`, and the displayed stopping equation, the new `BB6.Agent4M32.high32_forbidden_source` theorem proves

```lean
CCert.highPairGood (j%32) (m%32)
  → ¬ BB6CLine.Reach (2*j+3,k,0)
```

in the full original Machine C reachability semantics. `highPairGood` is the **executable Boolean membership in the complement** of Agent43's B8/M32 exact blank-reachable abstract closure, applied to the appropriate stopping equation's quotient image. Its source-level soundness follows from the original unmodified `CLine`, `CSourceBridge32`, `CFull32`, `M32HighAll` and `M32HighSmall`. It does not depend on a time cutoff, and does not prove that any surviving gateway is reachable.

The new `additional36_source_unreachable` theorem specializes this to every congruence pair listed in `additional36`. It uses two finite kernel certificates: all 36 satisfy `highPairGood`, and none appears in Agent43's earlier exact explicit 24 pair list `CCert.newHighPairs`. These 36 are **additional to the earlier explicit source-certified 24**, which already had [original-source verification](https://github.com/FlareZ123/bb6/actions/workflows/agent43-c-m32-finalproof.yml). The special-case theorem's antecedent is exact membership in a fixed list, not an unverified numerical presumption.

## Exact independent finite census and relative strength

The supporting [standard-library Python census](../../tools/agent4_c32_high_census.py) reuses the original [Agent43 graph engine](../../tools/agent43_c32_certificate.py) and independently constructs the smaller B8/M16 quotient using the **same exact** transition interpreter and Cartesian representative semantics. B8/M16 reaches **7,115** of 13,824 states with **34,992** representative transitions; B8/M32 reaches **31,570** of 64,000 states with **189,834** transitions. The latter is independently kernel-checked by 40 complete row-proof blocks [CI 41538277695](https://github.com/FlareZ123/bb6/actions/runs/41538277695).

For every parameter residue pair `(j%M,m%M)`, inspect the quotient of the exact high stopping-family input with `j≥3,m≥2`. Results:

| Certified quotient level | Number of forbidden parameter pairs |
| --- | ---: |
| Modulus 16 (out of 256) | 108 |
| Lifted modulus-16 exclusions (out of 1024) | 432 |
| Full modulus-32 source-sound predicate (out of 1024) | 492 |
| Modulus-32 incremental pairs beyond M16 lift | **60** |
| Already explicit in Agent43 `newHighPairs` | 24 |
| Additional source-certified pairs in this work | **36** |

The script asserts exact counts, exactly enumerates all 60 incremental pairs, verifies the earlier 24 are a strict subset and checks equality of the remaining 36 with the literal Lean `additional36` list. The generic Lean theorem soundly discharges **every one** of the 492 parameter classes when `highPairGood` holds. The cardinality **492** is a reproducible Python finite census, not an independent Lean kernel cardinality theorem; the 36 class membership and nonoverlap are Lean-kernel certificates.

**Example:** `(j,m,k)=(9,2,748)` satisfies `748+9+6+5=2^6(9+3)=768`, and the residue pair `(9,2)` is in the new 36. Thus the actual original blank-entry Machine C acceleration never reaches state `(21,748,0)` at any finite time, by one instance of the new theorem. This is a reachable-state exclusion, not a nonhalting or halting classification.

## Kernel audit / reproduction

[Manual CI 41563265975, SUCCESS](https://github.com/FlareZ123/bb6/actions/runs/41563265975/job/125678630954), original-source checkout plus generated B8/M32 finite quotient plus independently verified earlier 40 proof-block artifacts, recompiled all unmodified source modules and new [HighSource.lean](./HighSource.lean). Output:

```text
'BB6.Agent4M32.high32_forbidden_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent4M32.additional36_source_unreachable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, `native_decide` or custom axiom. It also executed `python tools/agent4_c32_high_census.py` successfully and independently checked its exact assertions. The earlier 492-pair **single monolithic** `by decide +kernel` cardinality proof attempt triggered a CI runner-shutdown signal; it was deliberately omitted from the successful theorem, leaving the numeric count on the reproducible Python side. Neither interrupted CI nor numerical count is being passed off as a proved universal Lean cardinality theorem.

## Limitations and next fruitful question

- This only removes *necessary halting gateway configurations* with specified parameters. Both infinite high-family survivors and the low-family halt gateways remain mathematically unsettled; no complete Machine C outcome or BB(6) bound.
- All original source machine semantics and exact start matter. Quotient absence transfers to the genuine CLine blank-root orbit through a fully proved embedding, not an assumed equivalence between distinct rooted machines.
- The **incremental 36** is relative to the explicit earlier M32 list and the M16 lifted quotient. Many stronger external/parallel congruence exclusion theorems may overlap. An independent novelty and overlap audit against the extensive source-certified Agent15/20/21/29/43 families is required before promotion to `results/`.
- A stronger global step would construct a source-certified **uniform forward or reverse invariant** excluding *all* remaining Diophantine stopping families, or a genuine halting witness. This M32 certificate by itself cannot settle their infinite complement.
