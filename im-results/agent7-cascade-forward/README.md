# Exact first-reset forward certificate for six-state #746

**Agent 7, 2026-11-04.** Intermediate machine-specific progress, not a resolved BB(6) holdout or a Busy Beaver bound. No claim of external academic novelty.

## Problem and prior source

The original six-state, two-symbol machine is `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`. The true blank-derived original Cryptids high-level orbit enters the source-indexed C episode model at reset `C(2,0)`. Every possible halt in that model passes through a fatal reset height

`fatal(n) = 4*2^n - n - 4`.

Agent 10's original-source theorem `Agent10Raw746.original_machine_halts_iff_surviving_257` (upstream CI [41772098475](https://github.com/FlareZ123/bb6/actions/runs/41772098475)) states that the **original raw machine halts if and only if** one of the fatal resets is reached from the genuine source-C root with `n>=257` and `n mod 6 in {4,5}`. The remaining infinite reachability problem is open.

Agent 10 subsequently proved a complete source-model first-reset inverse `CascadeResetInverse.reset_parent_iff`, rooted reset-chain equivalence `root_reset_chain_iff`, and strict increasing reset height `reset_parent_strict`. These established statements are reused here, without rederiving them. In particular, `ResetParent h u` means a **genuine first reset**, and the relation is deterministic from any given `h`. The older finite cutoff was `n<=256` under `CascadeFastShield.blank_excludes_surviving_through_256`.

## New finite certificate and exact result

[ForwardGeneric.lean](ForwardGeneric.lean) proves an abstract, fully quantified principle: for any functional, strictly increasing reset relation, if a list of edges forms a verified finite prefix from root `s`, avoids a specified Boolean bad predicate throughout, and ends strictly above a target cap, then no target inside that predicate and below the cap is reachable along any future finite chain. `segment_append` permits independently checked chunks to be composed by rewriting.

[ForwardProof.lean](ForwardProof.lean) defines the Boolean `stepOk h edge` directly from both cases of Agent 10's **exact** `ResetParent` grammar, with edge parameters `k,t,odd`. It proves:

- `stepOk_sound`: every Boolean-accepted edge has an actual exact first-reset semantics proof.
- `parent_functional`: determinism derived from the proven `Outcome.outcome_unique`.
- `certified_survivor_exclusion`: any complete accepted prefix reaching above `fatal(N)` excludes every reachable `fatal(n)` for `4<=n<=N`, `n%6 in {4,5}`, from the authentic blank-derived `C(2,0)` source model.

[generate_forward_certificate.py](generate_forward_certificate.py) deterministically computes a candidate finite root prefix, emits one Lean module partitioned into independently kernel-checked chunks, and emits the final exclusion theorem. **The Python computation is outside the trust base**: every numerical witness is checked by ordinary Lean `decide` against the imported, proved source reset relation, without `native_decide` or trusted external traces.

For `N=1024`, the generator emits **1,329 first-reset edges**, split into **nine** chunks of at most 150 edges. The final reset has **1,027 binary digits**, strictly above `fatal(1024)`. The fully checked source-model theorem is:

```lean
CascadeForwardCert.no_fatal_survivors_through_1024 :
  ∀ i, 4 ≤ i → i ≤ 1024 → (i%6=4 ∨ i%6=5) →
  ¬CascadeSweep.ReachC (2,0) (CascadeManyShield.fatal i,0)
```

**Successful original checked-in source-module CI:** [run 41894708560](https://github.com/FlareZ123/bb6/actions/runs/41894708560), GitHub Actions Lean 4.36.0-rc2. The workflow compiled all unchanged dependency files including `SourceMacro`, `FirstInverseComplete`, `ResetChain`, `FastShield`, then compiled both new proof files and dynamically generated the full 1024-index module. Audited final Lean axioms: **[propext, Classical.choice, Quot.sound]**, without `sorryAx`. The raw finite Boolean checker itself depends only on `propext`.

## Original raw-machine theorem: separate check

[OriginalForwardGate.lean](OriginalForwardGate.lean) composes the previous authenticated raw-machine `n>=257` equivalence with the new `n<=1024` reset exclusion. It targets:

```lean
Agent7OriginalForward746.original_machine_halts_iff_surviving_1025 :
  IsHalt target ↔
    ∃ n, 1025 ≤ n ∧ (n%6=4 ∨ n%6=5) ∧
      CascadeSweep.ReachC (2,0) (CascadeManyShield.fatal n,0)
```

The [manual pinned-upstream workflow](../../.github/workflows/agent7-746-original-forward.yml) imports unchanged original Cryptids machine source at revision `c86f15861709b76042998c5211c7b2f83991621b` and composes the complete original-to-source-C proof. **Treat this last theorem as pending until the separate pinned-upstream CI run passes.** The source-model `n<=1024` theorem is independently established as above.

## Reproduction and limits

Run the **manual-only** workflow [agent7-746-forward-cert.yml](../../.github/workflows/agent7-746-forward-cert.yml). It installs Lean 4.36.0-rc2, compiles the source dependency files and invokes the Python generator with `--index 1024 --chunk-size 150`; its generated source and all proof obligations are checked in that same CI job. The generator uses atomic replacement under a cross-platform file lock for its output.

The improvement is a genuine fourfold extension of the finite source-model cutoff from 256 to 1024 indices, using forward evidence of length 1,329 rather than a separate inverse search for each fatal index. It is a **bounded family exclusion** and does not establish nonhalting for #746: infinitely many surviving `n>=1025` candidates remain. No global upper bound or exact value of BB(6) is obtained.

A useful continuation is a memory-bounded multi-module certificate for `N>=2048`, or a uniform symbolic invariant that excludes the entire infinite surviving fatal family. Independent Python inverse cones are useful diagnostics but cannot replace a universal result or source-connected Lean proof.


## 2026-11-04 19:27 UTC: modular 2048-index source-C cutoff certified

**Verified:** [manual GitHub Lean 4.36.0-rc2 source-C CI 41896638169](https://github.com/FlareZ123/bb6/actions/runs/41896638169) **success**, compiling the entire unchanged checked-in first-reset proof chain and the new [ForwardSafe.lean](ForwardSafe.lean). The generator [generate_forward_modules.py](generate_forward_modules.py) produced **2,665 exact first-reset edges**, split into **167 independently compiled kernel-checked modules** at 16 edges each. These modules export source-proved `SafePath` proof values, composed using the general `SafePath.trans`, without constructing or reducing a huge combined trace.

The important new all-time theorem checked in the generated `Forward2048Final.lean` is:

```lean
CascadeForwardCert.no_fatal_survivors_through_2048 :
  ∀ n, 4 ≤ n → n ≤ 2048 → (n%6=4 ∨ n%6=5) →
  ¬CascadeSweep.ReachC (2,0) (CascadeManyShield.fatal n,0)
```

The kernel's printed axioms for the completed theorem are **[propext, Classical.choice, Quot.sound]**, with no sorry or unsafe native evaluation. The exact path itself uses only `propext`. The predicate `badHeight` is source-linked to Agent10's already-proved `Nat.log2` characterization of the fatal family.

[ForwardSafe.lean](ForwardSafe.lean) is a reusable proof interface: `SafePath` records a strictly chronological checked path that avoids a target predicate at every pre-terminal node; `segment_safe` produces such a path from a checked segment, `SafePath.trans` composes arbitrarily many modules, and `SafePath.excludes` proves a universal all-future exclusion once the final height exceeds the cap. `safePath_survivor_exclusion` specializes the general theorem to genuine source-C blank-reset reachability. This proof-carrying modular scheme fixes the original one-file Lean memory growth for very large finite reset traces.

**Physical raw-machine transfer:** [OriginalForward2048Gate.lean](OriginalForward2048Gate.lean) is prepared to compose the previously **original pinned-source CI-proved raw iff n>=1025** ([41895284713](https://github.com/FlareZ123/bb6/actions/runs/41895284713)) with the newly source-verified n<=2048 exclusion, giving `IsHalt target ↔ ∃ n≥2049, n%6∈{4,5}, ReachC (2,0) (fatal n,0)`. The distinct [original Cryptids pinned-source CI](../../.github/workflows/agent7-746-original-2048.yml) was dispatched; **do not present the physical n>=2049 theorem as kernel-certified until that exact CI passes**. The source-C n<=2048 statement itself is already fully kernel checked.

The infinite family n>=2049 remains unresolved; no nonhalting, global six-state upper bound, or exact BB(6) value is asserted. Further repeated finite cutoffs have diminishing scientific value compared with a uniform all-index root-sensitive invariant or an authentic halting witness.


## 2026-11-04 19:40 UTC: uniform all-index first-parent obstruction

**Entire unchanged repository source-C dependency chain and two new quantified Lean proofs PASSED** in manual [Lean CI 41898993932](https://github.com/FlareZ123/bb6/actions/runs/41898993932). The more primitive all-index theorem had already separately passed [CI 41898336470](https://github.com/FlareZ123/bb6/actions/runs/41898336470). All of the final theorems use standard Lean axioms only, with no sorry or native_decide.

[UniformFatalParent.lean](UniformFatalParent.lean) proves, for **every natural n≥4** and any genuine exact first-reset parent of `fatal(n)`, the following complete disjunction:

- The even branch has the **unique explicit** predecessor height `h = 4*2^n - 3*n - 7`, with dyadic exponent exactly `k=n-1`.
- Every odd branch has **positive** 2-adic valuation exponent `t≥1`. An odd inverse with `t=0` is ruled out for every fatal height.

[UniformFatalMod9.lean](UniformFatalMod9.lean) strengthens this to a **single possible first-reset parent** whenever `n mod18 ∈ {10,11,16,17}`: the even height above. Indeed the odd inverse with `t≥1` would force `9 | (2*fatal(n)+5)`, but the exact modulo9 computation contradicts this for all four index classes. These four index classes cover two-thirds of the six surviving mod18 classes of `n mod6 ∈ {4,5}` (the other two classes are n%18=4,5). The quantified theorem is `CascadeUniformFatal.fatal_only_even_parent`. The proof is source-indexed to the **complete** first-reset grammar already certified by Agent10; it does not rely on finite prefixes or guessed inverse edges.

This structural result does **not** imply exclusion from the blank-derived root. The unique immediate even predecessor may itself be reachable by an earlier chain of resets, and the remaining two modulo18 classes admit genuine synthetic odd ancestors. Its value is a uniform, exact all-index restriction that can simplify a future induction on entire inverse cones. External novelty and subsumption against Agent7's older synthetic inverse grammar must still be reviewed. It remains in `im-results/` for that reason.


## Final original-machine verification, 2026-11-04 19:41 UTC

**Pinned original Cryptids source CI [41897279486](https://github.com/FlareZ123/bb6/actions/runs/41897279486) SUCCEEDED.** Original upstream project pin `c86f15861709b76042998c5211c7b2f83991621b` was built unchanged under Lean 4.35.0-rc4, while the repository's independently verified source-C finite 167-module certificate was checked against its exact source-linked raw-machine transport. Original [OriginalForward2048Gate.lean](OriginalForward2048Gate.lean) compiled and the audited theorem `Agent7OriginalForward746.original_machine_halts_iff_surviving_2049` uses only `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

The **actual blank-tape six-state Turing machine** `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA` now has the proved exact conditional characterization:

```text
IsHalt target ↔
  ∃ n, 2049 ≤ n ∧ (n%6 = 4 ∨ n%6 = 5)
     ∧ CascadeSweep.ReachC (2,0) (4*2^n-n-4,0)
```

This is a universally certified **finite gate exclusion strengthening** from the previous (n≥257) raw iff; it **does not assert that the machine halts or fails to halt**, because infinitely many index candidates remain and their authentic reachability has not been decided. All evidence and source scripts stay in `im-results/` pending external novelty review and stronger all-index progress.


## 2026-11-04 19:49 UTC: an all-index authentic-root iff in four index classes

**Source-C Lean 4.36.0-rc2 manual [CI run 41900314347](https://github.com/FlareZ123/bb6/actions/runs/41900314347) SUCCESS.** [UniformRootGate.lean](UniformRootGate.lean) proves a strict exact predecessor existence and the following *uniform* equivalence for all n≥4 with n mod18∈{10,11,16,17}:

```lean
CascadeUniformFatal.genuine_fatal_iff_unique_even_parent :
  ReachC (2,0) (fatal n,0) ↔
  ReachC (2,0) (4*2^n-3*n-7,0)
```

The proof invokes the **complete first-reset source-C relation**, the universal unique-parent theorem, and the rooted reset-chain equivalence, so both implications concern the *actual* blank-derived C orbit, rather than merely algebraic paths from synthetic resets. The unique-parent predecessor is itself a source-certified first-reset edge. This is an all-index necessary-and-sufficient reduction of the remaining fatal question in four classes, and does not assert that the predecessor is unreachable. The Lean `#print axioms` check reported standard axioms only, with no sorry or native_decide.

An extension `UniqueEvenBand.lean` plus `SecondEven.lean` is being tested to force an additional even step uniformly. **These extensions are provisional until their separate updated CI succeeds**. Earlier successful CI 41900314347 independently certifies the above root iff regardless of later attempts.
