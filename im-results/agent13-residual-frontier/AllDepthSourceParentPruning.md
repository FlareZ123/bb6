# Machine C: source-exact inverse-word sieve at every odd-bounce depth

**23 November 2026, Agent 13.** This module excludes selected individual original Machine C section parents at **arbitrarily large bounce depth**, with no finite-depth cutoff. It is a reusable source-level ingredient, not a decision of Machine C or BB(6). The **complementary complete original-source parent classifier** for the genuine low-stop ray is now [LowRayFullFan.md](LowRayFullFan.md).

## Scope and equations

The genuine original section four-step inverse of a necessary low stopping state `(1,256*u+51)` gives `R_u=(180*u+28,166*u+25)`. Every odd high-bounce parent candidate `(a,k)` at even depth `n` must satisfy the exact original-source equations

```
346*u+54 = 2^(n+1)*(a+3)
2*k+a+7+3*n = 512*u+78.
```

If `346*u+54=2^(n+4)*q` with `q>=1`, then `a+3=8*q`. This high-valuation quotient covers all unbounded depths for which the source factor `a+3` is a multiple of eight; the remaining maximal-depth odd cofactors require separate treatment. The new [all-valuation source classification and dyadic equivalence](LowRayFullFan.md) prevent those other branches from being mistaken for nonexistent.

## Uniform source-certified exclusions

Fix `u,a,k,n,q` with `80≤k`, `1≤q`, `a+3=8*q` and the exact source cost. Set `r=n/8`. Each row below is proved for **every** `r≥0` by applying a chain of unique **unchanged-source** inverse equivalences to a final state with odd right counter ≥5 and forbidden coordinate sum 1 or 2 modulo 4. The letters denote A (even-right affine), B (six-sector even-right), O (odd/odd low-valuation), E (even/odd valuation-three) and F (even/odd valuation-two).

| Depth phase | Sufficient quotient congruence | Exact inverse word | Terminal sum modulo 4 |
|---|---|---|---|
| `n=8r` | every `q` | none | 2 |
| `n=8r+2` | `(q+3r)%8=7` | B-B-A | 2 |
| `n=8r+2` | `(q+19r)%32=19` | B-B-A-O | 1 |
| `n=8r+4` | `(q+r)%8=4` | O-B | 1 |
| `n=8r+4` | `(q+r)%16=3` | O-F | 2 |
| `n=8r+4` | **`(q+9r)%32=14`** | **O-B-B-B** | 1 |
| `n=8r+6` | `(q+r)%2=1` | A | 2 |
| `n=8r+6` | `(q+7r)%8=0` | A-O | 1 |
| `n=8r+6` | **`(q+15r)%16=2`** | **A-O-B** | 1 |
| `n=8r+6` | **`(q+31r)%32=20`** | **A-O-E** | 2 |

All ten conditions are mutually disjoint within their own depth phase. For each fixed `r`, the proved source filter therefore covers:

| Depth phase | Covered q mod32 | Remaining q mod32 |
|---|---:|---:|
| `8r` | 32 | 0 |
| `8r+2` | 5 | 27 |
| `8r+4` | 7 | 25 |
| `8r+6` | 23 | 9 |
| **Total** | **67 of 128** | **61 of 128** |

These are **formal phase/quotient cells**, not fractions of genuine parents, stopping targets, unsolved machines or BB(6) halts. For fixed `u`, the quotients at distinct depths are arithmetically coupled; in particular, **67/128 does not imply 67/128 of a parent fan is excluded.** The merged predicate `sourceOddDepthPruned67` and theorem `source_odd_depth_pruned67_unreachable` work at unbounded `n`, and the high-valuation corollary takes the original source mass equation directly. No native decision oracle or finite-time simulation is used in these proofs.

## Trust and location

- [EvenOddAllDepthForbidden.lean](EvenOddAllDepthForbidden.lean), [EvenOddAllDepthPhaseFour.lean](EvenOddAllDepthPhaseFour.lean), [EvenOddAllDepthPhaseSix.lean](EvenOddAllDepthPhaseSix.lean), [EvenOddAllDepthPhaseTwoDeep.lean](EvenOddAllDepthPhaseTwoDeep.lean): established original-source letters and first seven inverse-word exclusions, certified in the earlier CI closures recorded in their modules and the prior Git history.
- [EvenOddAllDepthShortExtensions.lean](EvenOddAllDepthShortExtensions.lean): three disjoint OBBB / AOB / AOE arbitrary-depth additions; original-source Lean 4.36.0-rc2 closure **passed** [CI 45268317452](https://github.com/FlareZ123/bb6/actions/runs/45268317452).
- [EvenOddAllDepthSieve67.lean](EvenOddAllDepthSieve67.lean): the merged source-certified predicate, unbounded reachability exclusion and high-valuation parent corollary, **passed** [CI 45271905097](https://github.com/FlareZ123/bb6/actions/runs/45271905097).
- [LowRayFullFan.md](LowRayFullFan.md): the independent complete-source parent classification proves that for `m=512z+67`, any genuine parent depth is even, satisfies `2^n∣519z+73`, and hence is at most `log₂(519z+73)`. The exact 2-adic equivalence and power gap are proved in the linked Lean modules. This **does not** eliminate all remaining permitted depths.

## Unresolved mathematical obstacle

For phase `8r+2`, many candidates are in an original-source sector with several possible predecessors, so the exact B inverse is not unique. For phase `8r+4`, the O inverse fails at `q+r≡1 (mod4)`, requiring a different fan argument. The quotient `a+3=8q` also omits possible top depths with a smaller odd cofactor. Any complete blank-root nonreachability proof must handle these *actual remaining source parents*, not merely raise the phase coverage count. A definitive Machine C decision additionally needs an exact unbounded halt/nonhalt criterion for its high-stop family.

The previously proved low-stop 559/4096 target exclusion is a separate authentic blank-orbit theorem, [described here](../../results/2026-11-23-machine-c-low-559-source-exclusion-agent13.md). The new all-depth sieve should be used to help eliminate **entire** authentic stopping rays, not publicized as a percentage of BB(6) solved.
