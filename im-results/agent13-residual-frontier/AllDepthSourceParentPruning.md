# An unbounded original-source inverse-parent pruning sieve for Machine C

**Agent 13 · 23 November 2026.** This is reusable mathematical infrastructure, not a halt decision. The complementary source-complete parent theorem for every possible parent of a particular target still has to be applied separately. New Lean modules are in this directory.

## Exact source equations and the obstacle

The exact four-step inverse of a necessary low stopping target of the form `(1,256*u+51)` yields the original Machine C section state `R_u=(180*u+28,166*u+25)`. Every candidate parent from the odd-left bounce inverse has a bounce count `n` and natural coordinates `(a,k)` satisfying
```
346*u+54 = 2^(n+1)*(a+3)
2*k+a+7+3*n = 512*u+78.
```
These are exact source-derived equations, not approximate machine dynamics. The parent depth can be **arbitrarily large** as the 2-adic valuation of `346*u+54` grows. A per-residue finite depth census cannot exclude all possible original parents. If
```
346*u+54 = 2^(n+4)*q,   q>=1,
```
then canceling the strictly positive source factor `2^(n+1)` gives `a+3=8*q`. Combined with the exact source cost, this reduces all parity and finite residue phase guards to arithmetic in `n,q` (and the quotient `r=n/8`).

## Uniform forced original-source reductions

Let `k>=80`, `a+3=8q`, `q>=1`, and retain the exact source cost equation. The following bounded words are performed on the **original** section transitions; each arrow is a proven exact predecessor equivalence. All terminal states have right coordinate odd >=5 and total coordinate sum 1 or 2 (mod4), forbidden by `odd_forbidden_image` for the genuine blank-origin orbit:

| Arbitrary depth | Congruence sufficient for exclusion | Original-source inverse word | Final forbidden sum |
|---|---|---|---|
| `n=8*r` | all `q` | none | 2 mod4 |
| `n=8*r+2` | `(q+3*r)%8=7` | B-B-A | 2 mod4 |
| `n=8*r+4` | `(q+r)%8=4` | O-B | 1 mod4 |
| `n=8*r+4` | `(q+r)%16=3` | O-F | 2 mod4 |
| `n=8*r+6` | `(q+r)%2=1` | A | 2 mod4 |
| `n=8*r+6` | `(q+7*r)%8=0` | A-O | 1 mod4 (certified) |

Here B is the exact even-right six-source inverse, A the even-right affine inverse, O the exact odd/odd low-valuation inverse, and F the exact even/odd valuation-two inverse. There is **no restriction on r**, and no claim that any one listed parent actually exists. Any genuine source parent satisfying the hypotheses is proven blank-inaccessible.

In each fixed four-depth block `n in {8*r,8*r+2,8*r+4,8*r+6}`, the seven accepted source paths cover `32+(4+1)+(4+2)+(16+4)=63` of the `4*32=128` formal (phase, q-mod-32) cells, uniformly for every r. **This is a count of formal arithmetic phase cells, not a fraction of all original-machine predecessors, of stopping parameters, of halts, or of six-state machines.** For a fixed stopping target, q depends on n via its 2-adic factorization, so these formal counts cannot be substituted for a full source decision.

## Lean and source provenance

- [EvenOddAllDepthForbidden.lean](EvenOddAllDepthForbidden.lean): arbitrary depth n=8r odd-image and n=8r+6 affine cases, plus n=8r+2 BBA. First four theorems accepted in [CI 45257688863](https://github.com/FlareZ123/bb6/actions/runs/45257688863), and the BBA extension accepted in [CI 45259227220](https://github.com/FlareZ123/bb6/actions/runs/45259227220), each original-source 58-module closure with standard Lean axioms, no `sorryAx`.
- [EvenOddAllDepthPhaseFour.lean](EvenOddAllDepthPhaseFour.lean): source-exact O-B and O-F uniform n=8r+4 proofs, accepted [CI 45259818679](https://github.com/FlareZ123/bb6/actions/runs/45259818679), 59 modules, standard axioms.
- [EvenOddAllDepthSieve.lean](EvenOddAllDepthSieve.lean): combined `sourceOddDepthPruned` and `source_odd_depth_pruned_unreachable`, accepted [CI 45260157919](https://github.com/FlareZ123/bb6/actions/runs/45260157919), 60 modules, standard axioms. The more general dyadic-mass corollary and expanded A-O phase are **accepted** in [CI 45261057263](https://github.com/FlareZ123/bb6/actions/runs/45261057263), 61 original-source modules, standard axioms.
- [EvenOddAllDepthPhaseSix.lean](EvenOddAllDepthPhaseSix.lean): additional A-O phase **accepted** in [CI 45260562548](https://github.com/FlareZ123/bb6/actions/runs/45260562548), 60 original-source modules, standard axioms and no \`sorryAx\`.\n- [EvenOddAllDepthPhaseTwoDeep.lean](EvenOddAllDepthPhaseTwoDeep.lean): additional B-B-A-O phase **accepted** in [CI 45261440104](https://github.com/FlareZ123/bb6/actions/runs/45261440104), 59 source modules, standard axioms, no \`sorryAx\`.

## Open research obligation and next leverage

The **finite-list per-target parent fan may have arbitrarily many depth members as the source 2-adic valuation grows**. This theorem gives an explicit source-correct **uniform filter** on each potential parent that can be integrated with a complete original-section predecessor enumeration. It does not prove that all parents of any chosen whole ray are excluded, and does not decide Machine C. To advance toward a root decision, combine the phase filter with the exact inverse-parent grammar, analyze the remaining phase cells for *all depths* using a well-founded source-invariant or a recursively closed inverse cone, and separately handle the unrestricted high-stop family. Do not silently identify formal phase density with measure of halting witnesses.

The accepted [559/4096 low-stop source theorem](../../results/2026-11-23-machine-c-low-559-source-exclusion-agent13.md) is a separate all-time genuine target exclusion. The present all-depth lemma is an extensible technique for future **full-fan** exclusions rather than another finite index census.
