# Agent 3: complete exact Machine C section inverse and unbounded in-degree

Date: 2026-11-02 23:28 UTC. All results here are **intermediate**: none proves that the original blank-start six-state machine halts or does not halt.

## Source and verification

Original Machine C RLE:
`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`.

The unmodified section map `BB6.Agent46.secNext` and original recursive `bounce` definitions reside in `im-results/agent46-c-jump/FastSectionDef.lean` and `BounceCalc.lean`; the original physical-machine-to-section correspondence is provided by the Agent 11/21/46 dependency chain in the manual workflow `.github/workflows/agent3-c-bounce-inverse.yml`.

Two files added in this incarnation:

- [SectionAllInverse.lean](./SectionAllInverse.lean), theorem `BB6.Agent46.section_preimage_all_iff`: for **all** natural source and target coordinates `a,k,x,y`, `secNext(a,k)=some(x,y) ↔ sectionPreimageAll a k x y`. This exhausts every exceptional and direct branch, all odd-bounce depths, all even-bounce depths, the even `y=3` special outcome, and all impossible `y` values. Every arithmetic witness constructs a **real** source edge.
- [UnboundedInDegree.lean](./UnboundedInDegree.lean), theorems `BB6.Agent3.unbounded_source_parent`, `family_parent`, and `parent_neq`: a certified infinite set of unbounded direct-parent families and their pairwise distinctness.

**Original-source Lean 4.36.0-rc2 [manual CI 41545500938](https://github.com/FlareZ123/bb6/actions/runs/41545500938) SUCCEEDED**, source commit `93138d05c3264ae5fcdddf5feb603888a520c001`, with all three unbounded-in-degree theorem axiom audits containing only standard `[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. The first completed full-inverse verification alone was [41544188316](https://github.com/FlareZ123/bb6/actions/runs/41544188316). The intermediate first unbounded-in-degree run failed from an omitted import `FastSectionDef`, fixed in the successful run.

## Parametric theorem: unbounded actual section-map in-degree

Write `P=4^(r+s)`, `Q=4^s`, and let `r,s` be *arbitrary* naturals. Then:

```
secNext (4 Q - 2, 16 P - (2 Q + 3 r + 4)) = some (0, 16 P).
```

These are genuine original-map arrows for all parameters; the odd-bounce depth is exactly `2r+1`. For each fixed `t`, choose `r=t-s` and `s=0,1,...,t`. The target `(0,16·4^t)` has at least `t+1` **distinct** immediate predecessor configurations, since their first coordinates `4·4^s−2` strictly increase. The statement is **uniform over all t**, with no finite cutoff.

This rules out reasoning about the complete inverse section relation using a universally fixed number of parent alternatives. It does not imply that any of these targets or parents lie on the authentic blank orbit, hence it does not decide Machine C. It is a structural obstacle to fixed-branch inversion, and a useful test for future inverse graph algorithms.

### Sharper computational conjecture: exact t+3 in-degree

A separately written exact BigInt original-definition interpreter and arithmetic predecessor enumeration at local scratch file `/tmp/bb6agent3/section_predecessors.cjs` (not yet persisted) finds **exactly t+3** distinct parents for `(0,16·4^t)` for each t=0,...,100. Additional sources beyond the proven t+1 high even-first family appear to be:

```
(0, 16·4^t - 3t - 6)
(16·4^t - 2, 8·4^t - 1)
```

These formulas satisfy the original source map by direct arithmetic and were checked computationally, but the **exhaustiveness** of the t+3 list has not yet been Lean-certified. It remains a conjecture pending a universal inverse completeness proof specialized to this target. The all-output `section_preimage_all_iff` is the intended tool.

## Validation provenance

The local enumerator compares all 1,369 targets with `0≤x,y≤36` against brute force across all `a,k` with source mass `a+2k≤x+2y`, matching 1,223 direct edges. It independently checks each of 100,000 original-definition forward transitions against computed inverse lists, or halting earlier; these finite tests are supporting evidence only. Finite mass bound was previously source-proved as `section_mass_strict` by this identity.

## Next actions

1. Prove the **exact** `t+3` source in-degree theorem using `section_preimage_all_iff`, and use it to derive tight asymptotic maximum in-degree `Θ(log(x+2y))` (or correct the conjectured bound if contradicted).
2. Study whether any forward-closed blank-reachable region excludes the entire remaining Machine C Diophantine halt basin; avoid confusing synthetic inverse branches with true blank reachability.
3. Preserve original-source hashes and the successful CI links above; do not promote intermediate claims to `results/` until they materially settle a root or contribute a publishable general result.
