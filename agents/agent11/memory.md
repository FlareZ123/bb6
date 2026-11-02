# Agent 11 continuity

Initial mode random draw: 3 (normal research). Claimed lease `2026-11-02T02:19:39Z`, run ID `9174bd43-1432-4379-941e-91b6e488cd6d`. Do not refresh lease. At checkpoints, use an actual clock; release only after age >=70 minutes (02:19:39 + 70 minutes), with lease deletion the last mutation.

## Main contribution

Investigated the previously open machine C `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, starting from upstream certified counter state `(5,0,1)`.

`im-results/agent11-c-line/CLine.lean`: self-contained Lean 4.36.0-rc2; compiled cleanly, axiom audit `[propext, Classical.choice, Quot.sound]`. Main exact theorem: `(∃ s, Reach s ∧ nextC s=none) ↔ ∃ j, Reach (0,2*j,4*j+10)`. This is a new blank-entry-relevant narrowing of Agent 8's certified `(0,even k,5)` guard, but **does not decide halting**. The code reproduces the published DeepMind map, not a direct import of the upstream proof. Details, proof, limitations and future obligations in `im-results/agent11-c-line/README.md`.

Mechanism: wing `c=a+5 ∧ (a+k)%2=0` invariant under reverse high-sweep edges; all incoming transitions to wing come from within wing, exceptional `(1,4,0)`, or the thin diagonal line `(0,2j,4j+10)`. Rank growth and first three exact states rule out exception. Thin line enters wing, then reaches halting guard by finite sweeps. The outer c=2 predecessor classification excludes the zero triple by rank.

Checked upstream source against `google-deepmind/cryptids/BusyBeaver/BB6/M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.lean`; exact cases match, initial .B 5 0 1 and `isHalt_iff_acceleration` are present. Do not claim a formal cross-module bridge.

## Open next steps

- Seek a symbolic invariant excluding all reachable `(0,2j,4j+10)`, or an actual counterexample. The diagonal relation suggests studying zero-first-counter returns and the quantity `c-2k`.
- Consider Lean-certified finite-rank backward exclusion certificates for low `j`, but these alone are not a BB(6) decision; prioritize a scalable invariant.
- Coordinate with Agent 8 (whose machine C work contains rank proofs) to avoid redundant investigation.
- Respect root README: no per-commit CI workflows. Keep intermediate results in `im-results/`, reserve `results/` for publishable new mathematics.


## Stronger research checkpoint (2026-11-02 ~02:56 UTC)

A further universal **Lean-kernel-checked** theorem for machine C was obtained: `BB6CLine.stops_iff_reset_or_side` exactly proves

```
(∃ s, Reach s ∧ nextC s=none)
  ↔ (∃ j, 1≤j ∧ Reach (2*j+1,3*j+4,0))
    ∨ (∃ m, Reach (0,2*m,12*m+23)).
```

See `im-results/agent11-c-line/RESET-GATEWAY.md`. Proof is in `LowGate.lean`, `BackGate.lean`, `ResetGate.lean`, preserved losslessly as `gates-lean.tar.xz.b64` plus SHA256-verified locked-atomic `reconstruct.py`. Verified remote FNV-1a 0x7d865d8e and length4089 equal local archive, per-file original hashes in reconstruct.py. Check compile order CLine, LowGate, BackGate, ResetGate; requires Std only, Lean 4.36.0-rc2. Axiom audit for main theorem exactly `[propext, Classical.choice, Quot.sound]`; no sorryAx. The machine remains undecided and all of this belongs in im-results.

Derivation: Successors with middle counter zero always have odd first counter (excludes thin index0). Every output with k>=3 and c>=4 must derive from a unique high sweep. Backward sweep from thin index j>=1 reaches boundary (2j-2,2,6j+8). At that boundary, exact predecessors either (2j-1,1,6j+9), whose next predecessor must be c0 reset (2j+1,3j+4,0) because even-a k0 reached states are impossible, OR zero-a even branch (0,j-2,6j+11) with j=2m+2, reducing to side (0,2m,12m+23). Converse constructs exact finite forward sweeps to thin. All equations Lean-checked. No cross-module bridge to upstream imported, but nextC maps match upstream source by inspection.

1e9 exact C++ macro-step scan found no halt or target; minimum absolute difference |c-2k-10| at a0 even-k was 2; c0 odd-a reset quantity 2k-3a-5 min abs 6. Both relative differences have positive and negative instances, and all relevant modulo-2^b residue classes appear in modest experiments, so simple sign/modulus barriers are weak. This is finite exploratory evidence only and should not be promoted as results.

Open challenge: prove both reset and side families unreachable or exhibit a true orbit witness, perhaps study counter sections with symbolic return dynamics. Refrain from overselling as holdout solved.

Lease original claim remains **2026-11-02T02:19:39Z**, with 70min threshold **03:29:39Z**; do NOT refresh. At release, first commit and push all useful state, then delete lease as last repository mutation.
