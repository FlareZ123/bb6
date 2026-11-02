# Source-derived universal asynchronous skip-cone separation

Agent 9, 2026-11-02. **Intermediate exact Lean arithmetic for published Cryptids S counter; no six-state machine decision and no Busy Beaver bound.**

For any `q>=16`, define `f(q)` by the three published shifted S branches: residue zero gives `4*(q/3)`, residue one gives `4*(q/3)-3`, residue two gives `4*(q/3)+1`. Its q-only total extension is defined after S-to-T transfers too, so actual machine application is conditional on both trajectories still being in S.

## General parametric theorem

Suppose `x>=16`, and a second synthetic S starting counter `y` lies in a gap crossed by one step of the first orbit:

```
f^[k](x)+14 <= y
y+14 <= f^[k+1](x).
```

Then, for **all independent epoch indices** a,b, their counters differ in one direction by at least `14+min(a,b)`. In particular `f^[a](x)≠f^[b](y)` for every a,b.

This is the Lean theorem `BB6.Agent9SSkipCone.skip_cone` in [`SSkipCone.lean`](./SSkipCone.lean). The proof uses the universal one-step arithmetic gap-growth lemma already established in [`SQuantitative.lean`](./SQuantitative.lean), global strict counter growth, and time-shift alignment. Its hypotheses require a verified *finite* forward jump; its conclusion holds at **all** future epochs.

## Two explicit consequences

1. The authentic mirrored T-root has q=17. Its eighth and ninth q values are 125 and 165, so **all 13 synthetic starting counters from 139 through 151**, inclusive, have q-only orbits asynchronously disjoint from the q17 orbit. This interval contains the other authentic S-root q=141. The Lean theorem `root17_interval` proves the full interval uniformly.
2. The first q17 orbit grows monotonically, and from iteration 9 onward every step jumps at least 28: `f^9(17)=165`, and for q>=97 the elementary lower inequality `4q≤3f(q)+13` forces `f(q)≥q+28`. Therefore for every k>=0 the explicit synthetic starting counter `Y(k)=f^[k+9](17)+14` lies in a valid skip cone. Lean verifies `escaped_ne` for every a,b,k and `escaped_injective`, proving infinitely many distinct synthetic S counters whose q-only orbits never coalesce with q17.

The original S-root q141 is genuinely attached to a different blank-state Turing machine; the other 12 interval counters and the explicit Y(k) family are **synthetic inputs only** and have no established original blank-machine entry. The theorem is structurally reusable for any authenticated root where the accelerated S branch is the same, yet it does **not** prove S survives indefinitely, exclude eventual transfers to T, decide a rooted holdout, or resolve BB(6).

## Reproducibility

This module imports `SExponentialGap`, which imports prior locally Lean-checked agent9 S proofs. `Lean 4.36.0-rc2` compiled every theorem (including the explicit infinite injective family) with only `[propext, Quot.sound]` axioms and no `sorryAx`. The exact Cryptids four-branch S macro was independently matched and Lean-proved in [`SSourceBranch.lean`](./SSourceBranch.lean), using original upstream source from the pinned cryptids commit `c86f15861709b76042998c5211c7b2f83991621b`. These are local standalone proofs; the original Cryptids module is not directly imported. Keep this generalization in `im-results/` until it closes a genuine rooted decision gate.
