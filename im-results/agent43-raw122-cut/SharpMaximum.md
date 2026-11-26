# Raw122 sharp maximum candidate: 6,659,487

Status: source proofs staged; complete kernel check pending. The previously accepted child covers bound this exact parent family by 6,766,859. Do not treat the sharper theorem as source-accepted before a successful joint proof check.

Parent partial machine (canonical index 86): `1RB---_1RC---_0RD---_1LD1RE_---0LF_------`.

## Exact attaining computation

`1RB---_1RC0RA_0RD0LF_1LD1RE_0RB0LF_1LC0LF`

Complete A1 by a halt. From a blank tape, the machine executes 6,659,486 ordinary transitions before reaching A1. The halt is transition 6,659,487. An independent deque-tape C++ simulation returned:

```
halt_step=6659487 state=A read=1 head=382 visited=550
```

The original packed proof `BB6Coverage.Agent29PackedLate.M0.exact_run` establishes the exact ordinary-prefix length; this was already accepted as part of the branch05 closure. Its zero-read transitions all have non-A destinations, so the incoming zero-write delay list at A is precisely [0]. Thus the weighted attained score is also 6,659,487.

## Sharp upper-bound argument

For the 24 ordinary assignments of the first queried F1 hole:
- Twenty previously accepted child covers have bound 7,014.
- 0LA (00) and 1LF (17) have only nonhalting residual witnesses beyond their original 7,014 audits. Specialize those witness lists at 7,014.
- 0LF (05) has 19 nonhalting residual witnesses and M0. The exact packed run and zero-delay computation give 6,659,487.
- 1LE (16) has nonhalting residual witnesses and M1. Its exact prefix is 1,296,924, and possible delays at A are [0,1]; the bound is 1,296,926.

The halt assignment at F1 is handled by the root split, as before. Hence all 25^6 literal completions are bounded by the M0 score, conditional on the new source proof checking. This gives the sharp statement `(∀ m, compatible parent m → WeightedBound B m) ↔ 6659487 ≤ B`.

Proof sources:
- [Raw122SharpLate.lean](Raw122SharpLate.lean): exact query, delays, sharp bounds and attainment.
- [Raw122SharpWitnesses.lean](Raw122SharpWitnesses.lean): specialized child covers.
- [Raw122SharpParent.lean](Raw122SharpParent.lean): parent composition and equivalence.

This improves the restricted family maximum, not the global BB(6) maximum. Integration into the canonical residual roster should use the parent Cover only after acceptance.
