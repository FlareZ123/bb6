# Candidate F321 699-source-ray certificate batch: mathematical accounting (pending full CI)

28 November 2026, Agent 31. This is **intermediate, not yet a publishable theorem**, until all 12 independent jobs in [GitHub Actions run 46127345679](https://github.com/FlareZ123/bb6/actions/runs/46127345679) succeed. The independently accepted initial 15-ray batch is already recorded in `results/2026-11-28-f321-twelve-new-affine-source-rays-mod49152-agent31.md`.

The generated manifest `mod49152-affine-bulk.json` contains exactly **699 distinct** residues `r∈[0,49151]`. Every requested proof has the exact type:

```lean
BB6.Agent31F321RayR.gateR_mod49152_never (k n : Nat):
  ¬ CounterReach 1 1 n (49152*k+R+1) (49152*k+R)
```

where each `R` is literally one of the 699 decimal entries; the code-producing search is *not* a proof oracle. Each emitted source file is separately type-checked and its axiom list verified under Lean 4.36.0-rc2. A successful 12-job matrix would certify all **699 unbounded nonreaching terminal arithmetic progressions**, no cutoff.

All 699 are within the 15 accepted possible terminal indices modulo384 (indeed inside the finer proposed 39-class CRT necessary list mod1536), so they do not overlap the 369/384 already-excluded counter-gate classes. Their raw additional excluded natural density relative to mod384 is `699/49152≈1.422119%`. The **paper arithmetic combination** with the published source-mod384 theorem alone would then give `15977/16384=97.515869140625%` terminal-index density excluded at every finite time, without relying on heavy modulo512-graph CI.

A stronger *independent-from-CRT* combination with the older published no-cutoff source inverse families has the following exact overlap analysis, derived by explicit enumeration of the 699 classes and the fixed low base-four digits of `(d−3)/8`:

- 12 of the 699 rays already belong to the earlier two broad affine terminal progressions `d≡3787(mod6144)` or `d≡7933(mod12288)`;
- 20 further disjoint rays lie entirely in the older odd-depth/zero-digit base-four inverse families (first five low digits in the progression are fixed because `49152/8=6144` is divisible by `4^5=1024`); these twenty do not intersect the previous broad two;
- no ray among the 699 has a partially excluded old base-four tail with positive probability strictly between 0 and1;
- **667 ray classes are entirely new and pairwise disjoint from all the older source-kernel no-cutoff excluded families**.

Consequently, if all 699 are Lean accepted, the exact natural density of source-counter terminal indices forbidden by the **union of these particular proven families**, including base-four and broad affine rays, is at least

```text
35497/36864 + 667/49152
  = 141988/147456 + 2001/147456
  = 143989/147456
  ≈ 97.64879014757%.
```

The complement density `3467/147456≈2.35121%` is a *remaining set of hypothetical terminal parameters*, not a probability of halting or a decision of F321. Adding a separate sound modulo512/1536 CRT certificate, if/when accepted, will improve this further; do not assume CRT Lean success yet.

The source-side theorem is **not** a proof that the original six-state machine is nonhalting. The pinned original blank-halt-to-`CounterReach` bridge *was* kernel-accepted independently in [GitHub Actions run 46126917968](https://github.com/FlareZ123/bb6/actions/runs/46126917968); therefore any accepted individual ray exclusion can also be used as a necessary restriction on an original six-state halt witness, but the original machine may still reach an unexcluded gate.

Most important next step: complete all 12 Lean matrix shards, inspect any failures without papering over, then promote the 699-ray result to `results/`, update `results/README.md`, and convey it to root-invariant researchers. Do **not** describe 699 as a theorem while CI is pending.
