# Source-lift of Agent45's thirteen period-256 P1 shadow cylinders

Agent8, 2026-11-05. These thirteen period-256 arithmetic classes (q0 = 61, 73, 77, 106, 138, 173, 217, 218, 221, 233, 238, 250, 254) were previously identified in the Agent45 arithmetic research at `im-results/agent45-p1-q61-cylinder/`. Reproducible arithmetic proof modules `BatchQ*.lean` establish explicit finite affine graph closure and uniform inverse cost m≤10, depth ≤8, for the original source shadow recurrence. The `BatchQ*Final.lean` modules invoke `BB6.Agent8Generic.critical_unreachable_of_shadow` to close all original-source inverse exits.

**Original-source Lean verification pending:** workflow `.github/workflows/agent8-p1-q256-batch-source.yml` must finish successfully on unchanged original dependencies. If verified, each q0 yields a genuine blank-orbit critical target exclusion for all r≥0 at n=16*q0+2+4096r. Existing original-root theorems may cover individual classes; check novelty and avoid double-counting. Even a full proof would exclude necessary gateways within P1, without resolving machine P1 or BB(6).

## Full genuine-source certification, 2026-11-05 21:14 UTC

**Success:** [original-source Lean 4.36.0-rc2 CI run 42110442046](https://github.com/FlareZ123/bb6/actions/runs/42110442046). Every one of thirteen `BatchQ{q0}Final.lean` theorems finished with precisely the standard axioms `[propext, Classical.choice, Quot.sound]`; no `sorryAx`. Thus all thirteen period-256 families are **now true P1 Reach critical-gateway exclusions**, for all natural r. The source result synthesis and Agent45 arithmetic-origin attribution are [here](../../results/2026-11-05-p1-thirteen-period256-source-lift.md). No P1 machine decision or BB(6) exact value follows.
