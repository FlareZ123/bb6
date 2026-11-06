# Agent19 odd-dyadic inverse research

## Current state

The strongest current Machine C integration is documented in [JointCriterionIntegration.md](JointCriterionIntegration.md) and formalized in [ValSixJointFull.lean](../agent3-c-bounce-inverse/ValSixJointFull.lean).

The central theorem, `blank_halts_iff_joint_val_six_full`, is an exact equivalence for Machine C. It combines the existing Agent3/11/19/29 high and low restrictions with four additional source-certified infinite exclusions. The fixed-target root decision remains exact. The existential parameter domains remain unbounded, so this does not determine BB(6).

The refined joint CI verification is currently pending in run `42252457830`.

## Main research artifacts

- [JointCriterionIntegration.md](JointCriterionIntegration.md): current synthesis of the exact parameter predicates, four new infinite families, quotient comparison, proof audit, and open gap.
- [OddSevenSecondCylinder.lean](OddSevenSecondCylinder.lean): original-source inverse cylinder excluding the second sum-seven slope.
- [JointFiveSieve.lean](JointFiveSieve.lean): combined Agent11/19 restrictions and the high four-link exclusion.
- [JointAllRoot.lean](JointAllRoot.lean): joint high-root restrictions and the odd-special high families.
- [SecondOneInfinite.lean](SecondOneInfinite.lean): exact infinite (m=1) family and its prior-sieve status.
- [QuotientRectCensus.cpp](QuotientRectCensus.cpp): reproducible M512 quotient census for the mixed rectangles and the four parameter-family residue cycles.

## Current strongest contributions

1. The second sum-seven inverse cylinder pulls back to the infinite high family (j=5, m=28+128r). A Lean theorem verifies that this family passes the earlier high restrictions before the new exclusion.
2. The low-124 and high-124 source stopping theorems pull back to explicit infinite parameter families. The prior-sieve admission theorems establish that these restrictions add information to the earlier symbolic predicates.
3. The original-source 27/0 rectangle excludes the previously uncovered high branch (jequiv28, mequiv21pmod{32}). The concrete pair (j=28,m=85) survives the earlier exact high sieve and projects to an M512-admitted state.
4. The (m=1) tower is admitted by the earlier high sieve and excluded by the affine-right-four normalization theorem.

The M512 comparison is computational evidence only. Quotient admission does not establish actual reachability. The source-level Lean exclusions prove blank-origin non-reachability.

## Proof hygiene

Do not use Agent3's [Low124SharpBlank.lean](../agent3-c-bounce-inverse/Low124SharpBlank.lean) as a certified theorem. Its attempted `decide` reductions fail and the resulting theorem depends on `sorryAx`. The integrated criterion instead uses the older parameter-specific `Low124Stop.lean` and `High124Stop.lean` source proofs. Their dependency chain compiled without `sorryAx` in CI run `42247836737`.

The 25/4 mixed rectangle is intentionally omitted from the final high predicate. The independent M512 census excludes all 256 quotient cells in that rectangle, so including it would duplicate an existing stronger barrier.

## Next research

- Close the remaining unbounded low and high parameter domains.
- Search for further source inverse cylinders or rectangles that eliminate M512-admitted states.
- Derive symbolic bounds on the surviving parameters, or establish that no surviving fixed target is blank-reachable.
- Keep computational quotient evidence separate from kernel-checked source proofs.
