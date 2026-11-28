# A Lean-kernel bridge from the original six-state F321 blank-tape machine to restricted authentic counter-map halting gates

**28 November 2026 — Agent 31; accepted in [GitHub Actions 46126917968](https://github.com/FlareZ123/bb6/actions/runs/46126917968).** This is a new **formal composition** of the upstream original Turing-machine-level halting reduction and our independently source-kernel-certified parity-aware finite quotient. The resulting theorem is about the **original six-state binary Turing machine**, not merely a restatement of the abstract counter recurrence. It does **not** prove original-machine nonhalting.

## Statement

The original machine is precisely `BusyBeaver.BB6.M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD.target` from [pinned DeepMind Cryptids commit c86f1586](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD.lean).

The kernel has accepted (in the original upstream module environment, unchanged pinned source):

```lean
BB6.Agent31F321Physical.original_blank_halt_implies_mod384_terminal
  (hh : BusyBeaver.IsHalt target) :
  ∃ (d n : Nat),
    BB6.Agent31F321Density.CounterReach 1 1 n (d+1) d ∧
    d % 384 ∈
      [37,61,115,133,139,157,181,211,229,235,253,277,325,331,349]
```

Consequently, **any real original-machine halt implies a finite authentic source-counter derivation** from the actual seed `(1,1)` to `(d+1,d)`, where `d` lies in one of exactly fifteen arithmetic congruence classes modulo 384. The source-side complement of 369 classes, density `123/128`, is unreachable **at all times**, but this does **not** mean there is a finite upper bound on halting time or eliminate any of the fifteen surviving classes.

The `#print axioms` log for the main bridge theorem is exactly `[propext, Classical.choice, Quot.sound]` (standard Lean axioms only), with zero `sorryAx` and `native_decide`. The proof was compiled using the pinned upstream version `leanprover/lean4:v4.35.0-rc4` in the [shared original-source audit workflow](../.github/workflows/shared-cryptids-source-audit.yml). Exact reproducibility parameters: `original_module=BusyBeaver.BB6.M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD`, `upstream_sha=c86f15861709b76042998c5211c7b2f83991621b`, `bridge_path=im-results/agent31-f321-mod384/UpstreamPhysicalBridge.lean`, `dependency_manifest=im-results/agent31-f321-mod384/upstream-manifest.txt`, `dependency_path=im-results/agent31-f321-bulk/DensityOneCore.lean`.

## Proof architecture

1. The **upstream Cryptids** module constructs an acceleration equivalent to actual blank-tape halting, yielding `isHalt_iff_highLevel_acceleration : BusyBeaver.IsHalt target ↔ CollatzHalts highLevelNext highLevelStart`.
2. The **source representation** is the literal local five-branch `SourceCounter.CounterMove` recurrence and `sourceNext`, with source seed `(1,1)`; no replacement of the target with a similar-looking or simulated machine.
3. The exact pointwise `source_next_upstream` proves `pairSourceNext (decodeUpstream s) = (highLevelNext s).map decodeUpstream`. This resolves the different but equivalent High/Far guards with Presburger arithmetic, including upstream `d+1<a` versus source `a≥d+2`, and upstream `3a<d` versus source `3a+1≤d`. The branch equivalence was kernel-checked, not simply asserted.
4. A generic `OptTrace` and a finite `eventually_none_has_terminal` lemma extract a **particular reachable halting terminal** from any iterated-Option upstream halt. The `upstream_trace_to_source` induction transports each actual accelerated transition, and `source_trace_counter` converts the exact `Option` trace to `CounterReach 1 1 n a d`.
5. The previously accepted `sourceNext_none_iff` reduces the final source terminal to `a=d+1`, and [`terminal_mod384_candidates`](2026-11-28-f321-parity-aware-mod384-source-gate-exclusion-agent31.md) from [CI 46124258798](https://github.com/FlareZ123/bb6/actions/runs/46124258798) restricts the actual terminal parameter to the fifteen surviving congruence classes.

See the [exact bridge source](../im-results/agent31-f321-mod384/UpstreamPhysicalBridge.lean), [generic source trace module](../im-results/agent31-f321-mod384/HaltingBridgeCore.lean), [authentic source-side parity quotient](../im-results/agent31-f321-mod384/Mod384Source.lean), and [successful full pinned-original-machine CI](https://github.com/FlareZ123/bb6/actions/runs/46126917968).

## Limits and next mathematical obligations

This theorem is a **conditional necessary restriction**, not a decision on `BusyBeaver.IsHalt target`; none of the fifteen infinite residue classes is shown globally unreachable by this bridge theorem alone. Independently proved finer [affine inverse-ray nonreachability](2026-11-28-f321-affine-predecessor-cones-agent31.md) and [twelve additional affine source rays](2026-11-28-f321-twelve-new-affine-source-rays-mod49152-agent31.md) can be logically composed to make the original-machine halting necessary condition more restrictive, and a combined Lean file `im-results/agent31-f321-mod384/UpstreamPhysicalCRT.lean` was prepared for a future full upstream compile. Its CRT dependencies remain unaccepted until the heavier modulo512 graph has completed Lean CI.

Determining **original F321 nonhalting** requires eliminating the *actual* source orbit's still-permitted terminal gates; determining **BB(6)** additionally requires the global candidate classification, all remaining six-state holdouts, and a sharp universal upper bound. Neither conclusion is claimed here. The significance of this result is that sound finite-source arithmetic certificates can now be transported through the **unchanged original-machine halting equivalence** under ordinary kernel checking.
