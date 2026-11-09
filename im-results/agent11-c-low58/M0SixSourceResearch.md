# Machine C: a sixth exact source-inverse sector and three independent m=0 rays

**9 November 2026.** This is an intermediate research report for the original
blank-start six-state Machine C, not a solution to Machine C nonhalting or to
BB(6). The remaining low/high halting-target parameters are unbounded.

## What changed mathematically

Let `CReach x y` mean that the original Machine C section transition
`BB6.Agent46.secNext`, starting from the actual blank-derived section seed
`(5,1)`, reaches `(x,y)`. Write

`T(j,m) = (2*j+3, 2^(2*m+2)*(j+3) - (j+3*m+5))`

for the high stopping target and

`L(m) = (1,2^(2*m+3)-(3*m+4))`

for the low stopping target. The existing exact halting criterion is the
disjunction of root reachability of some `L(m)` and some `T(j,m)`, subject to
already-proven necessary parameter conditions.

A sixth **exact** original-source inverse rule applies whenever

`x%2=0, y%2=1, y>=5, (x+y+1)%8=4`.

Agent3's source theorem `evenodd_four_blank_reach_iff` shows without
termination bounds that

`CReach(x,y) <-> CReach((x+y-5)/2,(x+3*y-9)/4)`.

The predecessor's weighted rank `x+2*y` is lower by exactly **7**. This rule
was already available in
[EvenOddFourExact.lean](../agent3-c-bounce-inverse/EvenOddFourExact.lean),
but it was omitted from the previous five-region
[ValSixMixedNormalize.lean](../agent3-c-bounce-inverse/ValSixMixedNormalize.lean).

The new [SixForcedNormalize.lean](SixForcedNormalize.lean) combines this
additional rule with the five existing source-exact regions, in original
priority order. The recursive function has a structurally justified
termination measure. It contains proofs of:

- `sixForcedNormalize_reach_iff`: unrestricted original-blank reachability
  of the input iff reachability of its fully reduced ancestor;
- `sixForcedRootDecision_iff`: exact fixed-target blank reachability
  decision by reducing first, then using the source-verified half-rank
  backward decision;
- `sixForcedExcluded_sound`: any normalized odd-right state with right
  >=5 and coordinate sum congruent to 1 or 2 modulo 4 makes the original
  input entirely blank-unreachable.

These are mathematical source-level theorem statements. **Original-source
Lean compilation of this new module is still pending** at the time this note
was written; do not promote its theorems as certified before CI succeeds.

[CThreeSixCriterion.lean](CThreeSixCriterion.lean) adds the sixth-region
Boolean source gate to the entire existing strongest high stopping
criterion while retaining its previous conditions. The
[CThreeSixAllCriterion.lean](CThreeSixAllCriterion.lean) successor applies the
same gate to the low branch and replaces both old root decisions with
`sixForcedRootDecision`, proving a lossless original blank halting iff.
Both wrappers likewise await source certification.

## Three explicit infinite high m=0 exclusions

Set `j=7+32t` so that the m=0 high stopping targets have the form

`T(j,0)=(17+64t,28+96t)`.

The first four forced source inverses for every t divisible by four are

```text
(17+64t, 28+96t)
 -> (43+160t, 13+48t)
 -> (26+104t, 18+76t)
 -> (42+180t, 8+38t)
 -> (48+218t, 3+19t).
```

The reusable universal statement is
`BB6.Agent11M0Four.mzero_four_reach` in
[M0FourRoot.lean](M0FourRoot.lean). The root equivalence in each step uses
the actual original section, never a finite abstraction.

Three disjoint infinite families are blank-unreachable:

1. **`j=71+128q`** (`t=2+4q`): four forced parents terminate at
   `(484+872q,41+76q)`, an odd-right forbidden blank-image state;
   [M0OddRay.lean](M0OddRay.lean).
2. **`j=1159+2048q`** (`t=36+64q`): six forced parents terminate at
   `(3386+5992q,2935+5196q)`, whose odd-right, sum-mod-4 value is
   forbidden; [M0OddRayDeep.lean](M0OddRayDeep.lean).
3. **`j=1031+2048q`** (`t=32+64q`): six forced parents terminate at
   `(6025+11984q,1105+2200q)`, whose odd-right sum is 2 modulo 4.
   Its fifth link uses the omitted valuation-two even/odd source sector;
   [M0OddRayValTwo.lean](M0OddRayValTwo.lean).

The first two families passed the complete original-source Lean 4.36.0-rc2
workflow [42598779153](https://github.com/FlareZ123/bb6/actions/runs/42598779153)
with standard-only axiom reports. The third family and reusable
four-edge lemma likewise **compiled with standard-only axiom reports**
in [42600169664](https://github.com/FlareZ123/bb6/actions/runs/42600169664),
although that overall workflow failed at a separate, later integration
file due to a redundant rewrite. Source artifacts for the third ray
are therefore typechecked, but the complete integrated stopping theorem
remains to be checked.

The three ray classes jointly account for `18/64 = 28.125%` of all
nonnegative integers t in this parameterized high m=0 subsequence,
not 28.125% of all stopping parameter pairs. In each case arbitrary
q is proved, with no fixed inverse depth approximation or finite horizon.

## Full prior-sieve independence and the diagonal

[ CThreeDiagonalJoint.lean ](CThreeDiagonalJoint.lean) contains an exact
stopping criterion that removes the entire high diagonal

`m>=2, j%2=1, m%32=(j+25)%32`.

Agent4's original four-lattice genuine-source obstruction handles all
`m>=4`. The case `m=2` reduces to the previously source-certified
sector `(x%16,y%32)=(5,12)`. The new
`prior_high_admits_diagonal` proves **every** such parameter passes
all previous C58/ValSix high restrictions, including affine
normalization's right-counter-four exclusion. Its exact halting iff
and strictness compile with only standard axioms; the original m>=4
case passed complete [42595809240](https://github.com/FlareZ123/bb6/actions/runs/42595809240).

[CThreeDiagonalLateFull.lean](CThreeDiagonalLateFull.lean) extends this
result to both arbitrary-depth earlier dyadic/late-cone filters.
Its `prior_late_high_admits_diagonal` gives uniformly quantified
independence because the new diagonal has even m, whereas both
late-depth filters require odd m. This later exact criterion compiled
with standard-only source axiom reports in
[42597947513](https://github.com/FlareZ123/bb6/actions/runs/42597947513),
though that job failed afterward on an unrelated proof elaboration.

The first, second and third source ray restrictions are successively
integrated in
[CThreeDiagonalM0Full.lean](CThreeDiagonalM0Full.lean),
[CThreeDiagonalM0DeepFull.lean](CThreeDiagonalM0DeepFull.lean) and
[CThreeDiagonalM0ValTwoFull.lean](CThreeDiagonalM0ValTwoFull.lean).
Each file states a lossless original blank halting equivalence, along
with parameter families that survive the preceding filters. Full
source certification of the *combined* iff remains pending.

## Finite impact of adding the sixth region

[m0_six_sector_census.py](m0_six_sector_census.py) compares the
five- versus six-region forced normalizers on the first 8192 values
`t=0,...,8191` in high m=0 `j=7+32t`.

| Number of t values | Five-region excluded | Six-region excluded | Added |
| --- | ---: | ---: | ---: |
| 64 | 17 | 20 | 3 |
| 256 | 69 | 82 | 13 |
| 1024 | 279 | 334 | 55 |
| 8192 | 2228 | 2674 | 446 |

The comparison is reproducible arithmetic and applies only to the
stated finite prefix. The new source inverse rule itself is
all-parameter, provided its Lean proof checks. The finite density
must not be extrapolated into a theorem about all t.

## Frontier

The additional normalization does not settle the globally quantified
existence of an acceptable low or high stopping target. The next
research bottleneck is source-exact treatment of stopping targets whose
remaining predecessor graph branches at mixed 2-adic depths or
cannot be resolved by any of the currently forced sectors. Further
isolated modular-ray lemmas add less value than a generalized
multi-parent closure argument, a global invariant, or a valid
all-parameters branch-elimination proof.

The main source-check workflow is
[`agent11-c-diagonal-late.yml`](../../.github/workflows/agent11-c-diagonal-late.yml).
Its latest source run should be inspected for the final status rather
than relying on this dated snapshot.
