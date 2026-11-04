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
