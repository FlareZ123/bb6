# Agent 34: whole-sector exact Machine C inverse and the m=8 reverse-cone pilot

**Status (2026-11-03):** one original-source Lean-certified universal structural theorem, one **computational-only** finite candidate certificate, and a documented prior-art correction. Neither Machine C nor BB(6) has been decided. All material remains in `im-results/`.

## Verified universal original-machine section theorem

Source `OddFourExactOriginal.lean` imports unchanged Agent46 `FastSectionDef` through the original Agent38 `ThirdStageOddDepth` chain. For **all** `a,k,x,y:Nat` with `x%2=1`, `y%2=1`, `5≤y`, and `(x+y)%8=4`, we prove the exact two-way equivalence

```text
secNext (a,k) = some (x,y)  ↔  2*a+4=x+y ∧ 2*k+3=a+y
```

All exceptional source branches and all successful recursive bounces are covered, without a depth cutoff. The forward direction uses Agent38's original `bounce_odd_one_sum0_mod8`, `bounce_even_sum_odd`, and `bounce_odd_four_direct` lemmas. The converse constructs the genuine odd-middle bounce terminal branch, including natural-subtraction and region guards. Consequently **every** output in this infinite odd/odd sum-four region has at most one possible incoming edge, and its existence is exactly determined by the two equations. The **third** theorem `odd_four_unique_parent` constructs the predecessor explicitly as `a=(x+y-4)/2`, `k=(a+y-3)/2`, proving **existence and uniqueness** for every target satisfying the sector guards. Its full-source Lean CI [41576226376](https://github.com/FlareZ123/bb6/actions/runs/41576226376) **SUCCEEDED** at commit `2f999045c6e09cb199eb844122094afe77c16997`; the axiom audit is `[propext, Classical.choice, Quot.sound]`. The second theorem `odd_four_reach_iff` proves genuine arbitrary-time blank-origin reachability of the output iff the uniquely defined affine ancestor is blank-reachable, expressed with existential `a,k` satisfying those equations.

**Full original-source Lean verification:** [successful manual CI run 41574890387](https://github.com/FlareZ123/bb6/actions/runs/41574890387) at commit `ffaf3682204ccc07794f8cf4b32e81e05c819200`, Lean 4.36.0-rc2. It compiles the original unmodified Agent11 CLine accelerator, Agent21 semantic bridge, Agent8 section framework, Agent46 bounce and return definitions, the packed SHA-pinned Agent38 third-stage proof, then `OddFourExactOriginal.lean`. Both `#print axioms` outputs are `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, `native_decide`, or hypothesis placeholders. The theorem is a general structural specialization of the prior complete all-output source grammar `SectionAllInverse.lean`, but differs from Agent3's earlier *different residue sector* `odd_sliver_parent_iff` where `x+y ≡ 0 (mod 8)`.

**Scope and novelty caution:** the result combines source-certified ingredients into a new explicitly solved sector. The special application to the two-step low `(1,16t+4)` feeder is already covered by the older `FeederOrbitGeneric.lean`; the new contribution is the all-output odd/odd sum-four source iff, its exact existence-and-uniqueness theorem, and its whole-sector blank-origin iff. A Machine C halting decision or a machine-wide bound does not follow.

## Exact finite reverse-cone computation for m=8

The full original-source low halting criterion is `(1,K_m)`, with `K_m + 3m+4 = 2^(2m+3)`. At `m=8`, `K_8=524260`; the section input `(1,524260)` is an **actual halting input**, but its reachability from the genuine start `(5,1)` is the open question.

`m8_reverse_certificate.py` executes the original bounce and section transition independently of its closed-form inversion. It solves all source cases of Agent3's exact Lean-certified `section_preimage_all_iff` by enumerating the finite powers-of-two divisors of each fixed output. A 62,500-input forward regression validates that every successful tested original edge is present in the inverse list; *every* enumerated backward edge is replayed against the exact original section transition, so the computational edge test is sound. It recursively explores backward ancestors until hitting one of the *already source-certified blank-orbit forbidden sets*:

- right counter 0 (Agent38);
- first counter 0 mod4 with right counter 1 mod4 (Agent38);
- odd right counter and sum 2 mod4, except the true start (Agent38);
- odd right counter at least 5 and sum 1 mod4 (Agent3);
- first counter 1 mod4 and right counter 0 mod8 (Agent38);
- Agent38's odd-special mod8/mod16 obstruction.

The result, checked in [successful manual GitHub Actions CI run 41575364079](https://github.com/FlareZ123/bb6/actions/runs/41575364079), was **41 distinct surviving backward states, 40 internal original edges, and 15 incoming edges stopped by source-certified forbidden predicates**. The true blank start `(5,1)` is absent; all 15 boundary ancestors satisfy an existing formal invariant. Each predecessor is a genuine transition as confirmed by the exact simulator and independent closed-form arithmetic.

The canonical SHA256 of the script's sorted `(states,internal edges,excluded edges)` JSON output is:

```text
1dfb11cc792e4ff627fbfd7430b5f0e35bfec7164afc3ccae6b86813014a10ad
```

The CI job also ran the source theorem above and recorded `62,399` live forward-edges across `62,500` tested input pairs. The Python script writes no files and requires only the standard library.

**CRITICAL verification boundary:** source proof `section_preimage_all_iff` proves the inverse *equations*, but the 41-state graph enumeration and the absence of omitted ancestors have not yet been translated into a Lean kernel-checked finite closure certificate. This is a **reproducible, compelling computational candidate for the all-time nonreachability of this one fixed m=8 target**, and must never be advertised as a formally proved Machine C exclusion. A Python assertion or successful CI process is not a formal proof of symbolic completeness of the enumeration.

## Scale test: a small residue class has nonuniform reverse-cone complexity

A separately reproducible exploratory scan in `low_m8_class_scan.py` checked the first **256 distinct parameters** `m=8+32t` for `0≤t<256`, using the same complete arithmetic parent oracle, existing certified forbidden predicates, and a per-input cap of 200,000 states. In this finite sample all 256 cases fully closed before the cap. However, the deepest backward predecessor chain required **1,551 levels**, and the largest surviving cone contained **144,023 distinct states**, both at `m=3400`. This warns against extrapolating the tiny `m=8` 41-state cone to a bounded-depth all-parameter proof. It is **empirical evidence**, not a quantified exclusion or an a priori bound on future parameters. Future source-certified global arguments should use symbolic parameter reductions or forward invariants, not assume that 20 backward steps suffice for every member of the congruence class.

## Next mathematical task

Convert the 41-state graph to a kernel-checked finite backwards-closed obstruction by combining unchanged `SectionAllInverse.lean` / `SectionLogBound.lean` (each inverse depth is logarithmically bounded by output), `SectionMassStrict.lean` (each successful return raises mass `a+2k` by at least 2), and existing source-checked forbidden-set reachability lemmas. The proof should establish **for all natural source counters** that the exact preimages of each graph node are precisely the enumerated internal and boundary nodes, then induct on the blank section time. Do not rely solely on bounded tests, a search cutoff, or an unproved assumption that the generated parent list is exhaustive. An executable reflection theorem for the full source grammar would make this reusable for many other fixed halting targets.

An alternative source-certified finite-trace route may be possible: the exact blank-section forward run first exceeds the target mass `1+2*524260=1048521` at section index `150052`, reaching `(621619,213453)` with mass `1048525`. A kernel-checked live endpoint plus source-level strict mass monotonicity and the fact that `secNext (1,524260)=none` would exclude this target at all section times. This milestone is currently **Python-computed only**, with no source-verified Lean trace certificate. A local kernel experiment successfully checked a 1024-return segment with source-matched definitions using `simp [run,secNext,exactSection,bounce]`; expansion of 150052 returns has not been completed. The 41-node inverse proof would be considerably smaller.

## Redundant prior results corrected

`ModImageOriginal.lean` independently reproduces only a weaker subset of Agent3's `Agent3CImage.lean` and `Agent3COneFamily.lean`. Original-source [CI 41572861177](https://github.com/FlareZ123/bb6/actions/runs/41572861177) passed, but this is **not new mathematics**.

`Mod24Original.lean` is a draft composition for low `m≡24(mod32)`; no source CI was dispatched for it. The entire parameter family was **already proved unreachable** by Agent6's source-certified `COneFiveDepth.lean`: stopping depth `2m≡48(mod64)`. See previous CI 41463963447 and the explicit correction `communications/agent3/2026-11-03T0341Z_agent34-correction-m24-prior-art.md`. Treat both files as superseded independent regressions, not research novelties. The temporary redundant CI workflow branches were reverted; the existing shared manual workflow is reused.

### Research boundary

No reachable halting Machine C input was discovered, no Machine C nonhalting proof has been established, and the exact six-state Busy Beaver function remains unknown. The only new completed original-source theorem here is the general odd/odd sum-four inverse equivalence and its all-time reachability lift; the m=8 inverse graph requires a final mathematical certificate.
