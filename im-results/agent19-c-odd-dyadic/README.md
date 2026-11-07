# Agent19 odd-dyadic inverse research

## New all-depth Machine C source theorem (6 November 2026)

The strongest new contribution is an **all-natural, unbounded inverse-depth cone** over the authentic `secNext` section. See [DyadicLowTower.md](DyadicLowTower.md) for the mathematics, explicit recurrence, original-source CI evidence and prior-result comparison. The source modules are [DyadicSixCone.lean](DyadicSixCone.lean), [DyadicLowTower.lean](DyadicLowTower.lean), and [LowTowerFamilies.lean](LowTowerFamilies.lean). The first two passed [CI 42287741405](https://github.com/FlareZ123/bb6/actions/runs/42287741405); the explicit low-stopping bridge and n=6 recurrence passed [CI 42288780840](https://github.com/FlareZ123/bb6/actions/runs/42288780840).

The cone proves `¬CReach a b` whenever `u≥9, u%4=1, b+2=2^r*u, (a+2*b+4*r)%8=0`, for **arbitrary r**. Its first-family corollary proves `¬CReach 1 k` for every even n≥2 and `3k=2^(n+2)*u+1` with `u≥9,u%4=1`. The low stopping-index families use `m→64m+91` and `n→n+6` with bases `(n,m)=(2,11),(4,219),(6,539)`. Agent21 separately source-proved the n=2 and n=4 bases. The new n=6+ cases extend the method to arbitrary depth. Machine C remains unsolved.

Separately source-certified cylinders: [Low622Source.lean](Low622Source.lean) forbids every `(1,1024q+622)`, excluding low m≡474 (mod1024), [CI 42285708106](https://github.com/FlareZ123/bb6/actions/runs/42285708106). [Low427Source.lean](Low427Source.lean) forbids `(1,1024q+427)` for q≥1, excluding low m≡539 (mod1024), [CI 42286086424](https://github.com/FlareZ123/bb6/actions/runs/42286086424). Both M512 abstract low-target cells are admitted, so these proofs exceed direct nonmembership in that finite quotient. These findings remain in `im-results/` pending adversarial prior-result review.

## Source-certified high stopping obstruction at every dyadic depth (7 November 2026)

The former [high-cone candidate](HighDyadicConeCandidate.md) is **source-certified**. The depth-two theorem is [HighDyadicLowVal.lean](HighDyadicLowVal.lean), [successful CI 42333928553](https://github.com/FlareZ123/bb6/actions/runs/42333928553). Its more general successor, [HighDyadicAllDepth.lean](HighDyadicAllDepth.lean) with [HighDyadicAllDepthArithmetic.lean](HighDyadicAllDepthArithmetic.lean), was **successfully original-source checked in CI 42334843728** on 7 November 2026. Both final theorems print only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

For arbitrary `r,j,m` with `2≤r`, `3≤m`, `r+4≤2*m+2`, `m%4=(2*r+3)%4` and `(j+9*m+14)%2^(r+4)=3*2^(r+2)`, the exact original-source stopping target `(2*j+3, 2^(2*m+2)*(j+3)-(j+3*m+5))` is not reachable from Machine C's blank-derived section. The proof pulls the exact odd/odd inverse into the pre-existing all-depth `DyadicSixCone`. The quantification ranges over **every** compatible inverse depth, rather than a fixed finite enumeration.

A constructive parameter family and explicit cross-agent `ValSixC58AllDepth` merger are now being checked separately. Their source-verification status should be read from the corresponding CI runs rather than assumed from the original high theorem. This advance does not determine whether Machine C or BB(6) halts.


## New even-right high exclusion and independent C23 cross-check (7 November 2026)

See [HighEvenRight.md](HighEvenRight.md) for the proof synthesis.

The genuinely new result is the source-certified even-right inverse cylinder
\[
m\equiv3\pmod4,\quad m\geq3,\quad j\equiv m+3\pmod8.
\]
It survives the full previous Agent24 high sieve and is excluded by the exact unique even-right predecessor plus the odd-right image invariant. Its source proof passed [CI 42348489335](https://github.com/FlareZ123/bb6/actions/runs/42348489335); the prior-sieve admission and exact residual theorem passed [CI 42349021125](https://github.com/FlareZ123/bb6/actions/runs/42349021125). The final axiom audit contains no sorryAx.

The sum-seven congruence family \(m\geq5,\ m\equiv1\pmod4,\ j+8\equiv3m+1\pmod{32}\) is exactly Agent20's C23 high family, not a new exclusion. HighEvenRightSum7Arithmetic.lean and HighEvenRightSum7Source.lean independently reconstruct its target residues and complete preimage argument through Agent46.sectionPreimageAll. This is retained as a source-level cross-check of C23Rectangle/C23High/C23Strict/C23Integration. Its duplicate prior-sieve proof is in HighEvenRightSum7Residual.lean.

HighEvenRightC23Residual.lean appends the genuinely new even-right family to Agent20's strongest C70+C23 exact residual, retaining the low C70 restriction, both C70 high rectangles, and the C23 high exclusion. The combined original-source CI audit is pending [run 42351346417](https://github.com/FlareZ123/bb6/actions/runs/42351346417).

## Current state

The established ValSixFull integration is documented in [JointCriterionIntegration.md](JointCriterionIntegration.md) and formalized in [ValSixJointFull.lean](../agent3-c-bounce-inverse/ValSixJointFull.lean). The later exact C58 refinement is in [ValSixC58.lean](../agent11-c-low58/ValSixC58.lean), successful in [CI 42333769024](https://github.com/FlareZ123/bb6/actions/runs/42333769024). The proposed all-depth merge is [ValSixC58AllDepth.lean](../agent11-c-low58/ValSixC58AllDepth.lean), requiring its separate integration audit.

The central theorem, `blank_halts_iff_joint_val_six_full`, is an exact equivalence for Machine C. It combines the existing Agent3/11/19/29 high and low restrictions with four additional source-certified infinite exclusions. The fixed-target root decision remains exact. The existential parameter domains remain unbounded, so this does not determine BB(6).

The refined joint CI verification succeeded in [run `42252457830`](https://github.com/FlareZ123/bb6/actions/runs/42252457830).

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

- [HighDyadicConeCandidate.md](HighDyadicConeCandidate.md) now records the **completed source-certified** high stopping theorem, its proof structure, CI audit, and an **M512-admitted** sample `j=263,m=3`. The generalized arbitrary-depth proof and its source certification are linked above. Establish separate prior-sieve novelty and complete the strongest exact halting-iff integration.

- Close the remaining unbounded low and high parameter domains.
- Search for further source inverse cylinders or rectangles that eliminate M512-admitted states.
- Derive symbolic bounds on the surviving parameters, or establish that no surviving fixed target is blank-reachable.
- Keep computational quotient evidence separate from kernel-checked source proofs.
