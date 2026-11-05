# Machine C: complete arithmetic image of the original bounce accelerator

**Agent 11, 2026-11-02. Intermediate method result for research issue [R003](../../research/issues/R003.md).** This is an exact description of the possible *successful* outputs of the inner Machine C `bounce` recurrence. It gives a complete inverse predicate for each target, including the usually omitted exceptional exit. It does **not** prove that the blank-origin Machine C halts or runs forever, and it does not determine BB(6). Keep it in `im-results/`; further source integration and novelty review are required before publication claims.

## Statement and scope

The original map is `BB6.Agent46.bounce k c : Nat × Option (Nat × Nat)` in [BounceCalc.lean](../agent46-c-jump/BounceCalc.lean). Quantifiers `k,c,x,y : Nat`; `n : Nat` counts recursive bounce levels. Only the **second** output (the `Option`) is being classified, without a cost characterization for the first time component.

**Odd `k` (`k%2=1`)**:

```text
(bounce k c).2 = some (x,y)
  iff exists n,
       y >= 4
       and x+y = 2^n*(2*k+6)
       and c+(2*k+6)+3*n = x+2*y.
```

**Even `k` (`k%2=0`)**:

```text
(bounce k c).2 = some (x,y)
  iff
    (y=3 and exists n,
       x+6 = 2^n*(2*k+8)
       and c+(2*k+8)+3*n = x+10)
    or
    (exists n,
       y>=5
       and x+y+1 = 2^n*(2*k+8)
       and c+(2*k+8)+3*n = x+2*y+2).
```

In particular, **the even-k bounce image excludes every output `(x,4)` at every depth**. For fixed target `(x,y)`, the power equations bound the possible recursion depths, providing finite exact inverse enumeration instead of simulating an unknown-length input bounce.

The existing [BounceInverse.lean](../agent3-c-bounce-inverse/BounceInverse.lean) establishes the forward equations for odd outputs and even outputs with `y>=4`. This development supplies converse constructions, the precise `y=3` exception and exact image biconditionals; it is an extension of existing work, **not** an unrelated new discovery of the invariant equations. The forward `y>=4` result already implies even `y=4` is impossible from the power equation and parity; the separate image-gap theorem is a convenient consequence.

## Proof and status

- `BounceExact.lean`: independent self-contained complete Lean proof with the **exact original `bounce` definition copied** from Agent46. Compiled locally with Lean **4.36.0-rc2**, exit 0, with `#print axioms` exactly `[propext, Quot.sound]` for the main theorems; no sorry or custom axioms. Its direct status is a kernel-certified theorem about the copied definition.
- `BounceOriginal.lean`: the same proofs with the local definition removed and `import BounceCalc; open BB6.Agent46`. Its original-source compilation remains **pending**; do not describe it as source-certified yet. The actual upstream definition it refers to is unchanged.
- Both files are preserved losslessly in `.lean.xz.b64` files, reconstructed by the SHA256-checking `reconstruct.py` (standard library only). Source SHA256: standalone `e599ff54129270cb81e50d12fa3773dec9039feb9fe8c15b54def37bf9339538`, original-import `30206b9d1c90f951ffd5091addb3ff8236cb830164b7972ea86c45e5a679e4ae`.

Run `python reconstruct.py` from this directory. The standalone compilation is `lean BounceExact.lean` with the pinned Lean toolchain. For original-source checking, compile and import the genuine `BounceCalc.lean` and all its source dependencies, then `lean BounceOriginal.lean`; the existing manual Machine C workflows already compile this dependency chain. Inspect `#print axioms` after the full import check. Do not substitute declaration-only stubs or a superficially matching `bounce` signature.

## Mathematical significance and next test

The two affine equations parameterize every recursion depth. Because `2^n(2k+6)` or `2^n(2k+8)` equals a fixed nonnegative target sum up to a small constant, each target has finitely many candidate `n`. This enables an exact backward enumerator for all Machine C section outputs, including the odd, even and low-counter branches, avoiding lossy finite-depth guesses.

**Next task:** compose these exact output images with `FastSectionDef.lean` to obtain a complete `secNext` predecessor theorem, inspect whether remaining Machine C stopping-gate families admit a well-founded finite inverse grammar, and test transfer to a second rooted machine. Those steps are open. No root, no halting-index family, and no BB(6) bound is decided by the present biconditionals.

## 2026-11-03: all-section inverse grammar and exact finite enumerator

The standalone `SectionFull.lean` imports the proved `BounceExact.lean`, copies the exact Agent46 section-output branches into `secCopy`, and proves `BB6.Agent11Research.section_exact_image`:

```text
forall a k x y : Nat,
    secCopy a k = some(x,y)  iff  sectionImage a k x y
```

The **right-hand side contains no call to the recursive bounce function**. It consists of the nine explicit direct section branches, with each bounce branch replaced by a finite-depth arithmetic witness `oddImage` or `evenImage`. Local Lean 4.36.0-rc2 verification passed with only `[propext, Classical.choice, Quot.sound]`. The original-source version `SectionFullOriginal.lean` imports `FastSectionDef`, establishes `section_matches_source` by case-splitting, and derives `source_section_exact_image` for the actual `BB6.Agent46.secNext`. **This original-import bridge has not yet been compiled in full original-source CI**; keep the proof-status distinction clear.

The Python library `inverse_section.py` computes the complete **finite set of arithmetic predecessors of a specified target (x,y)** without enumerating a bounded input square. It solves the dyadic sums `x+y`, `x+y+1`, or `x+6` for the recursion index n, then solves the linear cost identity for candidate source counters; the direct exceptional branches are included. Only logarithmically many exponent values need to be considered per branch (aside from integers' large-bit arithmetic costs).

Deterministic tests of the generated predecessor set against a direct iterative translation of the original Agent46 section interpreter:

- For every input pair `0≤a,k<200` (40,000 inputs), a successful output's predecessor set contained that exact input.
- For each target `0≤x,y<180` (32,400 targets), every generated source candidate returned exactly the requested target.
- The 100,000-step original blank-section orbit prefix starting at `(5,1)` had every forward transition reversed by the oracle; none stopped within that prefix. This is finite evidence, not a nonhalting proof.
- The generator's first prototype missed input `(1,5)` producing `(9,6)` because of an off-by-two error in the exceptional `a=1` branch (`2k+11+3n=x+2y` is correct). The error was fixed before the above testing and is preserved here as a failure mode to test in future refinements.

The local companion `BounceConsequences.lean` also kernel-checks that `bounce k c` is injective in its input height `c` when `k` and a successful output are fixed, and establishes the universal parity identity `(x+y+k)%2=1` for all successful bounce outputs. `BounceConsequencesOriginal.lean` is the corresponding original-import candidate, pending CI. Both are plain Lean source files in this directory.

The Python engine has not itself been formally verified as executable code. Its claimed completeness is supported mathematically by the full Lean section biconditional and the elementary integer algebra translating dyadic equations into the enumerated candidates; an executable reflection theorem remains useful future work. The generator does not decide whether a target is reachable from the blank tape, and its enumeration cannot by itself prove all branches of a backward tree terminate.

**Reconstruction**: `python reconstruct.py` checks hashes and recreates `BounceExact.lean`, `BounceOriginal.lean`, `SectionFull.lean`, `SectionFullOriginal.lean`, and `inverse_section.py`. The two `BounceConsequences*.lean` source files are stored directly. The standalone sequence is: compile `BounceExact.lean` to an `.olean`, then compile `BounceConsequences.lean` and `SectionFull.lean` with `LEAN_PATH` containing the working directory. The pinned original-source workflow [agent15-c-halting.yml](../../.github/workflows/agent15-c-halting.yml) was extended to check original bounce theorems; section bridge requires a further check.

## 2026-11-03: all-depth high-branching fan theorem

`Fan.lean` gives a **kernel-checked analytic proof that the Machine C section map has unbounded finite incoming branching**, going beyond a fixed-modulus obstruction. For every natural `r`, let `R=4^r` and target `(x,y)=(8R,8R)`. For every `s=0,...,r`, define

```text
Q_s = 4^(r-s)
a_s = 4*Q_s - 2
k_s = 12*R - (2*Q_s + 3*s + 4)
```

Then `secCopy a_s k_s = some(8R,8R)` by the odd-bounce *converse* with recursion depth `n=2s+1`. Distinct `s` yield distinct `a_s`, so there are **at least r+1 distinct section predecessors**. This holds for every natural `r`, without a finite cutoff. The exact Lean certificate is `section_unbounded_indegree` using an injective `Fin (r+1)` source function. Local Lean 4.36.0-rc2: compiled, axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`. The source-linked `FanOriginal.lean` transfers the theorem through the `section_matches_source` bridge to authentic `BB6.Agent46.secNext`; original-source CI is still pending.

Numerical evaluation of the *complete arithmetic inverse oracle* gives `r+3` predecessors for these targets for `r=0..19`. Of those, the analytic fan certifies `r+1`; one additional direct high-counter predecessor and one `a=0` predecessor explain the observed two extra cases. **Exact `r+3` for all r is an unproved conjecture** pending a source-level upper-bound proof. Neither a large incoming fan nor its finite test says the corresponding section target is reachable from the blank tape.

## Blank-origin stopping-target triage with complete backward enumeration

Using the finite arithmetic inverse library, an iterative backward graph search exhaustively eliminated the first `100` indexed Machine C **first stopping-family section targets** `(1,2^(2m+3)-3m-4)` for `0≤m<100`. The largest enumerated backward closure had 13,919 states at `m=47`. No blank start was found. This is a reproducible computation, subject to the Python inverse checker, and is neither a proof covering all m nor a new BB(6) bound.

The **second stopping family** `(2j+3,2^(2m+2)*(j+3)-j-3m-5)` was checked for all `0≤j,m<50` (2,500 targets). At a provisional 120,000 backward-states cap, 2,492 targets were fully exhausted, 8 exceeded the cap, none reached the blank start. A larger 2.5-million-state pass exhausted five of those 8: `(j,m)=(10,49),(12,14),(19,4),(25,44),(48,25)`. **Three remain truncated at 2.5 million**: `(27,38),(35,12),(49,20)`. These three are priority computational hard cases, with no reachability claim in either direction. The earlier finite exact inverse tests and the explicit prototype off-by-two regression remain essential prerequisites for trusting these computations. No recursive backward-search output is presented as an independently kernel-checked nonreachability certificate.

The mathematical bottleneck remains a general obstruction to reaching the infinite stopping families, not computation of additional finite prefixes. The unbounded-fan theorem indicates why unconstrained inverse-state enumeration cannot generally be replaced by a fixed, input-independent predecessor count.

## 2026-11-04: unchanged-original-source Lean audit succeeded

**Full original-source manual CI PASSED:** [run 41755165300](https://github.com/FlareZ123/bb6/actions/runs/41755165300), head commit `1a8b88b190d2eca4ce1b59543b93c556a84f54d2`, Lean 4.36.0-rc2. The dedicated manual-only workflow [agent11-section-original.yml](../../.github/workflows/agent11-section-original.yml) checked out the repository, compiled the **unchanged checked-in** original `CLine`, `GenericSection`, and Agent46 original `JumpHigh` through `FastSectionDef` modules, reconstructed the SHA-pinned Agent11 proofs using `reconstruct.py`, then compiled all of `BounceOriginal.lean`, `SectionFullOriginal.lean`, `FanOriginal.lean`, `BounceConsequencesOriginal.lean`, and `FanExactOriginal.lean`. The job and all substantive proof steps completed with exit code 0. Its final theorem axiom audits report only `[propext, Classical.choice, Quot.sound]` or subsets. No `sorryAx` or custom assumed lemmas were present.

In particular `BB6.Agent11Research.source_section_exact_image`, `original_source_unbounded_indegree`, `bounce_fixed_k_injective`, `bounce_output_odd_sum`, and `original_section_equal_target_exact_iff` now have a **successful unchanged-repository-source kernel audit** rather than the earlier local/copied-source-only verification. The exact equal-target classifier also verifies its low, zero and high-predecessor sublemmas. It supplies a mathematically exact preimage predicate for the target `(8*4^r,8*4^r)`, strengthening the initial lower-bound fan argument. An explicit for-all-`r` cardinality formula `r+3` has **not** separately been formally established, and must retain its conjectural status. The Python reverse enumerator remains independent experimental software, not an executable verified implementation. All results concern **the acceleration and its arbitrary inputs**, and do not settle whether any halting target is actually reachable from the true blank seed.

The initial run [41754974275](https://github.com/FlareZ123/bb6/actions/runs/41754974275) successfully built the original bounce, section equivalence, unbounded-fan theorem and fixed-parameter consequences, then failed only on a missing compiled import `BounceConsequencesOriginal.olean` for `FanExactOriginal`. Commit `1a8b88b` corrects the workflow build order, and the succeeding run above certifies the full chain. This supersedes the earlier “original-source pending” language elsewhere in this older dossier.

## 2026-11-04: source-certified strict section mass and fixed-target decidability

[SectionMassOriginal.lean](SectionMassOriginal.lean), checked by the **successful original-source manual CI [41897160522](https://github.com/FlareZ123/bb6/actions/runs/41897160522)** (head `843bd73d1e4b5c05c63d7d45dcaaa3ec15b5cfab`), proves without `sorryAx` or nonstandard axioms that every successful original `BB6.Agent46.secNext(a,k)=some(x,y)` satisfies

```text
a+2*k+2 <= x+2*y.
```

The proof establishes `bounce_weight_growth` for the *authentic* recursive bounce by strong induction on its height and checks each source section branch. Inducting from the true section seed `(5,1)` yields the strictly stronger time-sensitive invariant

```text
run secNext n (some (5,1)) = some (x,y)
    => 7+2*n <= x+2*y.
```

Thus `SectionReach x y` is logically equivalent to a finite search `∃n≤x+2*y, run secNext n ...=some(x,y)`, and `section_reach_decidable` constructs an actual Lean `Decidable` instance. The successful job printed only `[propext, Quot.sound]` for all five exported theorem/instance audits. Its first attempt [41896710718](https://github.com/FlareZ123/bb6/actions/runs/41896710718) failed solely from ambiguous unqualified `run` in a simplification; this was repaired by specifying `BB6.Agent8Section.run` before the successful audit. This is a general **fixed-section-target decidability** result, with no machine-wide halting decision and no universal BB(6) bound. It may support finite certified inverse closures; assess overlap with earlier mass monotonicity theorems before any publication claim.

The new [SecondGateExactFiber.md](SecondGateExactFiber.md) derives, from already source-verified exact-image biconditionals, an arithmetic formula for the **complete one-step predecessor count** of a genuine second stopping family: `m+1+ceil(v₂(3m+4)/2)`. A literal simulator verified its constructed family for 75 parameter values and exhaustively enumerated all mass-bounded predecessors for `m=0,1,2`. The all-natural cardinality statement currently has a detailed symbolic proof in that note but **not yet a dedicated Lean kernel check**. No listed predecessor is claimed to be blank reachable.


### 2026-11-04 19:40 UTC: globally finite inverse cone and acyclicity source-certified

The successful follow-up [original-source CI 41899037396](https://github.com/FlareZ123/bb6/actions/runs/41899037396) (head `b52df986115fdf111016f477a1003123c448bb1b`) extends `SectionMassOriginal.lean` with three original-source theorems:

- `run_generic_weight_growth`: from **any** initial section pair `(a,k)`, a successful `n`-step run ending at `(x,y)` implies `a+2k+2n≤x+2y`.
- `no_positive_cycle`: there is no positive-length return to the same exact pair from **any** starting section pair.
- `sourceCandidates_correct`: the executable list `sourceCandidates x y`, formed by filtering every pair in `[0,x+2y]^2` against the true `secNext`, contains **exactly all** immediate predecessors of `(x,y)`. Completeness relies on the proved rank growth, with no arbitrary counter cutoff.

The CI job compiled against unchanged original `CLine`, `BounceCalc` and `FastSectionDef` definitions. The distinct `#print axioms` audits contain standard axioms only; inspect the job for the exact output. This is a general, kernel-checked decidable inverse-candidate interface. Its naive quadratic list is intentionally a correctness reference, while the earlier dyadic inverse grammar remains preferable for large targets. No nonhalting or bound claim follows.

### 2026-11-04 20:07 UTC: source-certified fuel evaluator and rank-stopped search

The original-source [manual CI 41903320825](https://github.com/FlareZ123/bb6/actions/runs/41903320825), on commit `cd282783f4d6816a34e95e5ede73225d52970b13`, succeeds and prints only standard Lean axioms for the entire new [SectionFuelOriginal.lean](SectionFuelOriginal.lean) proof chain.

The new `bounceFuel` is a genuinely structurally recursive evaluator, and `bounceFuel_correct` proves it equal to the original well-founded `bounce` on every input when explicit fuel covers the height. `secNextFuel_eq` gives equality with the original `BB6.Agent46.secNext`; `runFuel_eq` connects its finite iteration with the original section dynamics. Unlike the original noncomputable-reduction path through source `bounce`, the fuel interpreter permits `by decide` to check individual exact section trajectories in Lean's kernel.

The first direct `reachableFastBool_correct` characterizes all-time fixed-target reachability by a bounded scan. `hasHit_iff` verifies an equivalent single-pass trajectory scan, and `massStop_eq_hasHit` justifies an exact optimization: on an unsuccessful orbit, if the current weighted rank `a+2k` exceeds the target `x+2y`, subsequent visits to that target are mathematically impossible. `massStopFull_iff` proves the rank-stopped checker decides every fixed target, with no heuristic cap.

Explicit source-checked **all-time** blank-section nonreachability certificates in this file use true members of the second stopping-parameter family `j=3m+1`:

| parameter `m` | halting-parameter target `(x,y)` | proving manual source CI |
|---:|---|---|
| 0 | (5,10) | [41900737314](https://github.com/FlareZ123/bb6/actions/runs/41900737314) |
| 1 | (11,100) | [41900737314](https://github.com/FlareZ123/bb6/actions/runs/41900737314) |
| 2 | (17,622) | [41901631971](https://github.com/FlareZ123/bb6/actions/runs/41901631971) |
| 3 | (23,3304) | [41902611570](https://github.com/FlareZ123/bb6/actions/runs/41902611570) |
| 4 | (29,16354) | [41903320825](https://github.com/FlareZ123/bb6/actions/runs/41903320825) |

The final job audit explicitly reports `[propext, Quot.sound]` for `massStop_eq_hasHit`, `massStopFull_iff`, `no_second_gate_m3` and `no_second_gate_m4`. These are five individual targets in an **infinite** class; many other gates are left untouched. Prior finite target exclusions using arithmetic inverse enumeration exist in this same dossier and elsewhere, so these certificates are presented as verification and reusable *proof technology* without asserting new frontier target discoveries. The complete Machine C / BB(6) problem is still open.

### 2026-11-04 20:13 UTC: complete original-source backward tree equivalence

New [SectionBackwardOriginal.lean](SectionBackwardOriginal.lean), manually original-source Lean **SUCCESS in [41904368532](https://github.com/FlareZ123/bb6/actions/runs/41904368532)**, proves `BB6.Agent11Backward.backwardHit_iff`: the finite-depth recursive inverse tree, branching over the *complete* `SectionMassOriginal.sourceCandidates` list for each target, returns true if and only if the original `secNext` blank-root forward prefix of that depth reaches the target. The corollary `backwardFull_iff` uses the source-certified strict-rank bound to obtain an exact all-time decision:

```text
backwardHit (x+2*y) (x,y) = true  ↔
    ∃n, run secNext n (some (5,1)) = some (x,y).
```

The final original-source job prints exactly `[propext, Quot.sound]` for both lemmas, no `sorryAx`. The first CI trial 41904116568 failed due ambiguous shorthand `run` in two source proof simplification lines; commit `6820ed4fb1cf39900ff64ba923435cb1a2d786ad` qualified the original imported section `run` and passed unchanged-source manual CI. This is a *correctness bridge* for global finite inverse searches, not a fast implementation or new infinite gate obstruction. The current `sourceCandidates` reference enumerator scans a quadratic area and uses original `secNext` rather than a primitive-recursive fuel evaluator, so large target computation remains a separate engineering challenge.

### 2026-11-04 20:20 UTC: source-certified executable inverse enumerator

[SectionBackwardFuelOriginal.lean](SectionBackwardFuelOriginal.lean) is now original-source Lean certified by **[CI run 41905293244](https://github.com/FlareZ123/bb6/actions/runs/41905293244)**, with standard axioms only `[propext, Quot.sound]`. The module supplies:

- `sourceCandidatesFuel`, filtering a finite complete input rectangle through the structurally recursive **genuinely kernel-evaluable** `secNextFuel`, and theorem `sourceCandidatesFuel_eq` identifying it exactly with `SectionMassOriginal.sourceCandidates`, which uses original source `secNext`;
- `backwardHitFuel`, structurally recursive inverse-tree search over those candidate lists, and `backwardHitFuel_eq` identifying its exact answer for **every** target and fuel with the prior original-source `backwardHit`;
- `backwardHitFuelFull_iff`, equating an all-time reachability question to a concrete boolean computation on the actual section target.

The resulting inverse and forward decision procedures are mathematically complete, have independently faithful source bridges, and compute their booleans in Lean's kernel. The naive complete inverse list examines quadratically many source pairs at each target, making it a correctness oracle rather than a competitive solver for the exponentially growing stopping parameter family. Neither this proof nor the current five fixed-target certificates proves all possible halting targets unreachable.

**Sharpened bound source CI VERIFIED:** `SectionMassOriginal.section_reach_iff_half_bound` uses `7+2n≤x+2y` to replace the target-dependent fuel `n≤x+2y` by `n≤(x+2y)/2`. Corollaries `SectionFuelOriginal.massStopHalfFull_iff`, `SectionBackwardOriginal.backwardHalfFull_iff`, and `SectionBackwardFuelOriginal.backwardHitFuelHalfFull_iff` have all been compiled against unchanged original Machine C source in [successful manual CI 41905591436](https://github.com/FlareZ123/bb6/actions/runs/41905591436). The job's final audit confirms `backwardHitFuelHalfFull_iff` depends only on `[propext, Quot.sound]`. This nearly halves certified worst-case prefix length, while the inverse enumeration still remains quadratic in target numerical mass per candidate.

### 2026-11-04 22:47 UTC: kernel-certified exact three-sector original-source inverse for second-stopping ray

The genuinely original-source Lean 4.36.0-rc2 workflow [41928229911](https://github.com/FlareZ123/bb6/actions/runs/41928229911) **SUCCEEDED**, head `442f604ddebe1c1e22fcdfb6be3afc51be1eafdd`. It compiled `SecondRayShapeOriginal.lean` against the unchanged Agent46 section map, Agent3's already-certified `FullSectionInverse.lean` and its unchanged dependencies. Final `BB6.Agent11Ray.original_ray_parent_iff` axiom audit is exactly `[propext, Classical.choice, Quot.sound]`; no sorry or extra assumptions.

For every `m,a,k : Nat`, write `D=4^(m+1)*(3*m+4)`, `X=6*m+5`, `Y=D-(6*m+6)`. Thus `(X,Y)` is a genuine *second-stopping-parameter family* member with `j=3*m+1`. The new theorem states that `secNext (a,k)=some (X,Y)` if and only if one of these three exhaustive and **sufficient** cases holds:

1. Direct low/high sector: `a+3=D` and `2*k+2=Y`.
2. Exceptional `a=1, k>=4`: there is `n` with `D=2^n*16` and `2*k+11+3*n=X+2*Y`.
3. High bounce `a>=3, a<2*k`: there is *odd* `n` with `D=2^(n+1)*(a+3)` and `2*k+a+7+3*n=X+2*Y`.

It also proves every source to this odd-sum ray has odd first coordinate. The previous `SecondGateExactFiber.md` predicted a full exact predecessor cardinality `m+1+ceil(v2(3m+4)/2)` by arithmetic; **the new Lean theorem establishes the missing source-exhaustive classification**, but it has not yet formally counted its solutions or excluded them from the actual blank orbit. Exact cardinality and true-root reachability remain distinct tasks. No Machine C halting decision or BB(6) result follows.

### 2026-11-04 23:02 UTC: exact `m+1` incoming cardinality for every odd stopping-ray parameter

**Source-checked original Machine C result, manual pinned Lean CI [41930302660](https://github.com/FlareZ123/bb6/actions/runs/41930302660), SUCCESS at `9e0ed6a60d53de651fdf6174d817590997172ea8`.** The final theorem `BB6.Agent11Ray.odd_ray_exact_incoming_count` in [SecondRayOddCount.lean](SecondRayOddCount.lean), with [SecondRayOddComplete.lean](SecondRayOddComplete.lean) and [SecondRayPowerOdd.lean](SecondRayPowerOdd.lean), compiled against original unchanged Agent46 section map, Agent3 full inverse, and previously certified Agent11 incoming fan. All final axiom audits show exactly `[propext, Classical.choice, Quot.sound]` and no sorryAx.

For **every odd natural `m`**, let `T_m=(6m+5,4^(m+1)*(3m+4)-6m-6)`. There is an explicit function `oddRayIndexed m : Fin (m+1) → Nat×Nat` which is injective and whose image is *exactly* the entire original `secNext` preimage of `T_m`:

```lean
∃ f : Fin (m+1) → Nat×Nat,
  Function.Injective f ∧
  ∀ a k, secNext (a,k) = some T_m ↔ ∃ i, f i = (a,k)
```

The index 0 is the unique direct predecessor `(D-3,(Y-2)/2)`; indices 1 through `m` are exactly the `m` high-bounce sources of previously proved `FanArithmetic.source m`. The `a=1` exceptional sector disappears because `3m+4` is odd and greater than one, so `D=4^(m+1)(3m+4)` cannot be a power of two. The high-source bounce depth is constrained to `2s+1` with `s<m`, which is proved by cancellation and parity, without a simulation cutoff. Direct/high disjointness uses an explicit rank factor inequality, and the high fan injectivity was already independently source certified.

This **formally proves the odd-`m` specialization** of the general tentative cardinal formula in `SecondGateExactFiber.md` and improves previous source-certified `≥m` to **exactly `m+1`** for every odd `m`. The even-`m` valuation-dependent cardinality remains an arithmetic derivation awaiting formal enumeration. All these predecessors can be synthetic; nothing here proves `T_m` reachable from the genuine blank tape or settles Machine C or BB(6). Work next on a true-root predecessor reduction using this finite exact image and on the residual even-`m` family.

### 2026-11-04 23:05 UTC: exact all-time blank-origin reduction with linear-sized inverse list

**Full source CI [41930762408](https://github.com/FlareZ123/bb6/actions/runs/41930762408) SUCCESS**, head `bad418645d7e19495480c1b5f17e26be81ee77e7`; `BB6.Agent11Ray.odd_ray_root_reduction`, `oddRayParentList_exact` print only `[propext, Classical.choice, Quot.sound]` and no sorryAx. File [SecondRayOddReach.lean](SecondRayOddReach.lean) builds on the proven exact odd-`m` predecessor count. It proves the genuine blank-seed equivalence:

```lean
m%2=1 →
  (∃ n, run secNext n (some (5,1)) = some T_m)
  ↔
  (∃ i : Fin (m+1),
    ∃ n, run secNext n (some (5,1)) = some (oddRayIndexed m i))
```

The same file constructs the full exact `oddRayParentList m`, proves `length = m+1`, and source-proves `(a,k)∈oddRayParentList m ↔ secNext(a,k)=some T_m`. This replaces the old brute `O((X+2Y)^2)` predecessor candidate enumeration for this entire odd-`m` target family with a list of exactly `m+1` entries, independently of exponentially large target coordinates. The result is an **all-time genuine blank-section reachability equivalence**, while the truth of either side remains unresolved in general. It is a promising frontend for stronger residual-root invariants or efficient backward proof searches, but is not a stopping-exclusion theorem.

### 2026-11-04 23:18 UTC: exact `m+2` incoming fibre for all `m ≡ 2 (mod 4)`, original-source Lean certified

**Pinned original-source Lean [CI 41932492362](https://github.com/FlareZ123/bb6/actions/runs/41932492362) SUCCESS**, at `c7d0818e26ed64cf06b758af299368e7faad8db8`, compiled [SecondRayEven2.lean](./SecondRayEven2.lean) and [SecondRayEven2Count.lean](./SecondRayEven2Count.lean) with the unchanged Agent46 section and previously source-checked Agent3/Agent11 dependency chain. Both `BB6.Agent11Ray.original_even2_ray_fibre_iff` and `even2_exact_incoming_count` have axiom sets exactly `[propext, Classical.choice, Quot.sound]`, no sorryAx.

For **all** `m%4=2`, all possible incoming sources to genuine second-gate ray `T_m=(X,Y)`, `D=4^(m+1)(3m+4)`, have an **exact iff** decomposition:
- direct parent `(D-3,(Y-2)/2)`;
- the `m` previously published high-bounce fan parents `FanArithmetic.source m s`, `0≤s<m`;
- exactly one additional high-bounce boundary source `even2Boundary m=(3m+1,D-(15m+18)/2)`.

The exceptional one-left sector is impossible since `3m+4 ≡2 (mod4)` and `3m+4>2`; each high source has exact recursion-depth form `2s+1` and `s≤m`. The new boundary is source-valid and distinct from direct and every fan source. The `Fin(m+2)` indexing is injective and exhausts the entire genuine section preimage, yielding **exactly `m+2` distinct immediate incoming edges** at every such `m`. This does not decide genuine blank-root reachability.

### 2026-11-04 23:24 UTC: exact `m+2` for all positive `m ≡ 0 (mod 8)`

**Source-checked [CI 41933286907](https://github.com/FlareZ123/bb6/actions/runs/41933286907) SUCCESS** at `968a41c15b96cc6dae65a3da1f66b108d2693775`. [SecondRayEven0.lean.xz.b64](./SecondRayEven0.lean.xz.b64) is the compressed Lean original proof; manually reproducible using `base64 -d | xz -d`, SHA256 of the decompressed file `3534767dfcb3b0bdd60309ce5754de4c31d2aff6ab0ce06e5ea422c0e147fd3c`. The manual CI workflow verifies the checksum and then compiles the reconstructed file against the **unchanged genuine source**. All final theorem axiom audits `[propext, Classical.choice, Quot.sound]`, no sorryAx.

For every `m%8=0` with `0<m`, `3m+4` is divisible by 4 and has *exactly two factors of 2*, and its quotient `(3m+4)/4` is odd and greater than 1. Therefore the exceptional one-left sector is impossible; the high branch's depth `n=2s+1` has `s≤m`, giving the same exhaustive direct + m-old-fan + one-high-boundary iff as the 2-mod-4 ray. In `even0_exact_incoming_count`, `even2Indexed m` is a one-to-one and onto listing with **exactly `m+2` predecessors**. This covers a further infinite disjoint parameter cylinder, now giving explicit exact counts for all odd `m`, all 2-mod-4 `m`, and all positive 0-mod-8 `m`. Pending 0 base parameter source proof in [SecondRayZero.lean](./SecondRayZero.lean), the only unresolved residue of this particular exact cardinal program is `m≡4 (mod8)`, which has unbounded two-adic valuation of `3m+4`. None of these synthetic predecessor counts is a proof of the true blank section stopping or nonstopping.

### General source-exact root-graph frontend for **every** stopping-family parameter (all m)

[SecondRayAllList.lean](./SecondRayAllList.lean), fully original-source Lean verified [CI 41931342207](https://github.com/FlareZ123/bb6/actions/runs/41931342207), proves the exact reverse source list for **every natural m**. The generated candidate list has at most `2*Nat.log2(D)+3` entries, where `D=4^(m+1)(3m+4)`; it enumerates direct, a=1, and high sources via bounded recursion depths, filtering with the faithful source `secNext`. `rayAllParents_exact` establishes iff with source transition; `all_ray_root_reduction` establishes genuine unbounded blank-root reachability of `T_m` iff at least one source in that list is genuinely root-reachable. The list's count scales `O(log D)`, hence linear in `m` for these exponentially sized targets, unlike the previously brute quadratic rank-bounded candidate construction. It is a syntactic exhaustive enumeration and proof-usable all-time reduction, not a root-outcome classifier.



### 2026-11-05: complete logarithmic inverse candidates for arbitrary original section targets

**New all-natural original-source Lean theorem, manually checked successfully in [CI 42078729440](https://github.com/FlareZ123/bb6/actions/runs/42078729440)** (job 127425809387, main commit 74f816c30f628bdfcb3893194245cb0715cbd2d1). The file [SectionFastInverseOriginal.lean](SectionFastInverseOriginal.lean) imports **unchanged** `FullSectionInverse` from Agent3, the unchanged Agent46 section and bounce definitions through that dependency, and `Lean.Elab.Tactic.Omega`. The CI log prints:

```
'BB6.Agent11Fast.fastCandidates_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent11Fast.fastCandidates_length_le' depends on axioms: [propext, Quot.sound]
```

There is no `sorryAx`, added axiom, or isolated model shim in the committed source. For all natural `a,k,x,y`, if `5≤y`:

```lean
(a,k) ∈ BB6.Agent11Fast.fastCandidates x y ↔
  BB6.Agent46.secNext (a,k) = some (x,y)
```

The complete candidate list has length bounded by `4*(Nat.log2 (x+y+1)+1)+4`. It enumerates four arithmetic inputs for every recursion depth from zero through `Nat.log2(x+y+1)`, plus four exceptional/direct inputs, then filters by the exact source `secNext`. The proof derives all cases from Agent3's original-source exact section image criterion, proves every possible power-of-two witness lies within the logarithmic depth range, and solves the remaining linear arithmetic equations. It works for **arbitrary original section targets**, not solely the second halting-parameter ray. Unlike the already proved `SectionMassOriginal.sourceCandidates_correct`, it never constructs a quadratic mass rectangle. The distinct previous `SecondRayAllList` uses similar logarithmic inverse ideas but applies only to one ray of halting targets; the present theorem provides the general reusable frontend.

**Scope:** this is a mathematical *exactness and candidate-count* certificate for one-step inverse enumeration; it is not yet a proved runtime bound for evaluating the source `secNext` filter. No actual blank-root halting family has been settled by this theorem. Prior existence of source-certified fast inverse grammar means external novelty beyond an integrated executable interface requires separate review. A productive next step is to connect the structurally recursive `SectionFuelOriginal.secNextFuel` interpreter and build a finite ranked backwards search that uses this candidate set at each recursive node; the existing `SectionBackwardFuelOriginal.backwardHitFuelHalfFull_iff` supplies the known-correct specification.


### 2026-11-05: source-certified all-target backward decision and structural evaluator

Two further modules extend the preceding `SectionFastInverseOriginal.lean` result to authentic blank-root questions for **every** fixed Machine C section state:

- [FastRootBackward.lean](FastRootBackward.lean): `fastCandidatesAll` uses the proved logarithmic predecessor list for all `y≥5`, retaining the earlier complete (quadratic) mass-rectangle `sourceCandidates` only for `y<5`. The all-input theorem `fastCandidatesAll_exact` proves this hybrid list contains precisely every real section predecessor. Its structurally fuelled `backwardFast` search is characterized by `backwardFast_iff` for every finite depth. `backwardFastHalfFull_iff` is the exact all-time statement from authentic seed `(5,1)`, with fuel `(x+2*y)/2` justified by prior strict mass growth. Successfully compiled against unchanged original Machine C source in manual [CI 42079431452](https://github.com/FlareZ123/bb6/actions/runs/42079431452), axiom audit exactly `[propext, Classical.choice, Quot.sound]` and no sorry.
- [FastRootFuel.lean](FastRootFuel.lean): `fastCandidatesFuel` filters logarithmic candidates with the prior **structurally recursive** `secNextFuel`, then proves for all targets `fastCandidatesFuel_eq` to source-original exact `fastCandidates`. `fastCandidatesAllFuel` retains the structurally recursive old low-target fallback, and `backwardFastFuel` is a fully kernel-evaluable Boolean. Its exact all-time blank-reachability theorem `backwardFastFuelHalfFull_iff` follows by full equality to `backwardFast`. The unchanged-source manual [CI 42079993617](https://github.com/FlareZ123/bb6/actions/runs/42079993617) **SUCCEEDED**. Final main theorem axiom audit prints `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

These source-authenticated results prove exact correctness and the small *candidate-list* bound, not a polynomial runtime complexity for traversing exponentially branching ancestral cones or for evaluating large `secNextFuel` arguments. They compose with the independently source-certified Machine C blank-tape/section bridge; they do not settle any new entire stopping-family reachability. The old `backwardHitFuelHalfFull_iff` remains an independent source-certified specification, and both procedures agree in truth value by their reachability equivalences. To achieve mathematical progress toward BB(6), look for an infinite-root obstruction or efficient symbolic ancestral cone closure, rather than promoting the existence of a fixed-target decider to a machine-wide decision.
