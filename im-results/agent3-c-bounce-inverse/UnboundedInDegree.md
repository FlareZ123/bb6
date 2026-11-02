# Agent 3: complete exact Machine C section inverse and unbounded in-degree

Date: 2026-11-02 23:28 UTC. All results here are **intermediate**: none proves that the original blank-start six-state machine halts or does not halt.

## Source and verification

Original Machine C RLE:
`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`.

The unmodified section map `BB6.Agent46.secNext` and original recursive `bounce` definitions reside in `im-results/agent46-c-jump/FastSectionDef.lean` and `BounceCalc.lean`; the original physical-machine-to-section correspondence is provided by the Agent 11/21/46 dependency chain in the manual workflow `.github/workflows/agent3-c-bounce-inverse.yml`.

Three files added in this incarnation:

- [SectionAllInverse.lean](./SectionAllInverse.lean), theorem `BB6.Agent46.section_preimage_all_iff`: for **all** natural source and target coordinates `a,k,x,y`, `secNext(a,k)=some(x,y) ↔ sectionPreimageAll a k x y`. This exhausts every exceptional and direct branch, all odd-bounce depths, all even-bounce depths, the even `y=3` special outcome, and all impossible `y` values. Every arithmetic witness constructs a **real** source edge.
- [PowerDegreeExact.lean](./PowerDegreeExact.lean), theorems `power_target_preimages_iff` and `power_target_parents_only`: complete source iff and exact `t+3` in-degree on `(0,16·4^t)` for every t, including all exceptional and recursive branches.
- [UnboundedInDegree.lean](./UnboundedInDegree.lean), theorems `BB6.Agent3.unbounded_source_parent`, `family_parent`, and `parent_neq`: a certified infinite set of unbounded direct-parent families and their pairwise distinctness.

**Original-source Lean 4.36.0-rc2 [manual CI 41545500938](https://github.com/FlareZ123/bb6/actions/runs/41545500938) SUCCEEDED**, source commit `93138d05c3264ae5fcdddf5feb603888a520c001`, with all three unbounded-in-degree theorem axiom audits containing only standard `[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. The first completed full-inverse verification alone was [41544188316](https://github.com/FlareZ123/bb6/actions/runs/41544188316). The intermediate first unbounded-in-degree run failed from an omitted import `FastSectionDef`, fixed in the successful run.

## Parametric theorem: unbounded actual section-map in-degree

Write `P=4^(r+s)`, `Q=4^s`, and let `r,s` be *arbitrary* naturals. Then:

```
secNext (4 Q - 2, 16 P - (2 Q + 3 r + 4)) = some (0, 16 P).
```

These are genuine original-map arrows for all parameters; the odd-bounce depth is exactly `2r+1`. For each fixed `t`, choose `r=t-s` and `s=0,1,...,t`. The target `(0,16·4^t)` has at least `t+1` **distinct** immediate predecessor configurations, since their first coordinates `4·4^s−2` strictly increase. The statement is **uniform over all t**, with no finite cutoff.

This rules out reasoning about the complete inverse section relation using a universally fixed number of parent alternatives. It does not imply that any of these targets or parents lie on the authentic blank orbit, hence it does not decide Machine C. It is a structural obstacle to fixed-branch inversion, and a useful test for future inverse graph algorithms.

### NEW: exact t+3 in-degree theorem (fully certified)

The conjectured exact degree has now been **proved for all t** by the original-source Lean theorem `BB6.Agent3.power_target_preimages_iff` in [PowerDegreeExact.lean](./PowerDegreeExact.lean), [manual CI 41546463512](https://github.com/FlareZ123/bb6/actions/runs/41546463512). The CI prints only the standard axioms `[propext, Classical.choice, Quot.sound]` for both `power_target_preimages_iff` and `power_target_parents_only`, and no `sorryAx`.

For arbitrary natural `t,a,k`, letting `Y=16·4^t`, `secNext (a,k)=some (0,Y)` **if and only if exactly one** of these alternatives holds:

1. `a=0`, `k=Y-(3t+6)` (a unique exceptional zero-first source);
2. `a=Y-2`, `k=Y/2-1` (a unique direct low-branch source);
3. `∃ r≤t, a=4·4^(t-r)-2, k=Y-(2·4^(t-r)+3r+4)` (exactly `t+1` distinct high even-first sources).

The unique first coordinate `0` excludes overlap with the high family, and the direct parent's first coordinate `Y-2` exceeds every high-family first coordinate, which is at most `4·4^t-2`. Distinct `r` have strictly different first coordinates by `parent_first_strict`. Thus the **original section relation has exactly t+3 predecessor pairs**, not merely at least `t+1`.

Mathematical argument: the complete all-output inverse grammar splits every predecessor into special, direct or high branches. Odd-first high branches have even-bounce output whose right counter cannot be even here. High even-first branches have odd-bounce power equation `Y=2^n(2a+4)` and cost equation `2k+a+7+3n=2Y`. The second forces odd `n=2r+1`; the first gives `r≤t` and `a=4·4^(t-r)-2`. This yields the full classification. The formal proof includes base-two exponent injectivity and cancellation over the naturals; the opposite implications are exact source edges. All indices and depths are unbounded.

This is a source-map structure theorem for **synthetic** target states. No claim is made that a blank-reachable target with these coordinates exists, or that Machine C / BB(6) has been decided.

## Universal even zero-first predecessor theorem (new, all y>=16)

[ZeroEvenUniversal.lean](./ZeroEvenUniversal.lean) proves the complete exact source relation `BB6.Agent3.zero_even_preimages_iff` for **every even natural y with 16≤y**, rather than only the dyadic subsequence. Its original-source **[Lean 4.36.0-rc2 CI 41548461859](https://github.com/FlareZ123/bb6/actions/runs/41548461859) succeeded**, auditing both `zero_even_preimages_iff` and `zero_even_parents_only` with axioms `[propext, Classical.choice, Quot.sound]` and **no sorryAx**. The generalized high-branch converse `general_zero_even_parent` was separately checked in successful CI [41547975533](https://github.com/FlareZ123/bb6/actions/runs/41547975533).

For arbitrary input `a,k` and even target second counter `y≥16`:

```
secNext(a,k) = some(0,y)
  ↔ (a=y-2 ∧ k=y/2-1)
    ∨ (∃ r u, u≥2 ∧ y=8·4^r·u ∧
               a=2u-2 ∧ k=y-(u+4+3r))
    ∨ (∃ r, y=16·4^r ∧ a=0 ∧ k=y-(3r+6)).
```

The three source sectors are pairwise distinct. Every listed source is a true original-section edge; exhaustive necessity includes arbitrary odd-bounce recursion depth, even-bounce obstruction by parity, and all exceptional cases. The dyadic theorem `power_target_preimages_iff` is an explicit in-degree special case. **This classifies synthetic inbound edges, with no assertion of reachability from the genuine blank start.**

## Finite, arithmetic-only inverse witness bound (original-source certified)

[BounceLogBound.lean](./BounceLogBound.lean) proves `bounce_full_log_bounded` with **[CI 41547236372](https://github.com/FlareZ123/bb6/actions/runs/41547236372)**. A successful output pair `(x,y)` of the *original total bounce* has a valid arithmetic inverse witness of recursion depth `n≤Nat.log2(x+y+6)`, irrespective of source counter magnitudes. The bound is sufficient for all odd, even and exceptional y=3 branches.

[SectionLogBound.lean](./SectionLogBound.lean) lifts this to `BB6.Agent3.section_bounded_exact`: for all `a,k,x,y`, `secNext(a,k)=some(x,y)` iff the finite arithmetic predicate `sectionBounded a k x y`, whose recursive witness depths are bounded logarithmically. It provides executable Bool `boundedEdge` and correctness `boundedEdge_correct`, which check a genuine section edge via arithmetic without executing the original recursive interpreter. Both passed **[full-source CI 41547542026](https://github.com/FlareZ123/bb6/actions/runs/41547542026)**. This is a certified finite per-edge checker, while the all-time blank-input halting problem remains open.

## Validation provenance

The local enumerator compares all 1,369 targets with `0≤x,y≤36` against brute force across all `a,k` with source mass `a+2k≤x+2y`, matching 1,223 direct edges. It independently checks each of 100,000 original-definition forward transitions against computed inverse lists, or halting earlier; these finite tests are supporting evidence only. Finite mass bound was previously source-proved as `section_mass_strict` by this identity.

## Next actions

1. Use the now-certified exact `t+3` in-degree theorem to derive a tight upper bound on arbitrary output in-degree, ideally `Θ(log(x+2y))` in the worst case.
2. Study whether any forward-closed blank-reachable region excludes the entire remaining Machine C Diophantine halt basin; avoid confusing synthetic inverse branches with true blank reachability.
3. Preserve original-source hashes and the successful CI links above; do not promote intermediate claims to `results/` until they materially settle a root or contribute a publishable general result.
