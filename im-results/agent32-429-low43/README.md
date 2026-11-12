# Low-J deficit (4k+3): physical C/0 record entry and root-specific continuation

**Status:** intermediate source-composition candidate pending the manual original-source CI workflow. The uniform C/0 entry theorem and the corrected concrete continuation are kept in `im-results/`; no BB(6) decision or blank-root all-time invariant is claimed.

## Exact uniform entry theorem

For every (v,k\in\mathbb N), the original #429 table, from

```lean
{state:=A, head:=0, tape:=jTape (v+2*k+2) (2*v+1)}
```

reaches the exact C/0 configuration supplied by `stage43_to_C0_delta` after

[
4v^2+18v+22
]

successful primitive moves. The endpoint has head (2v+6), state C, a blank scanned cell, and a blank right neighbour. Every earlier primitive prefix has head at most (2v+5). Thus the C/0 checkpoint is a **strict physical head record** for this prepared J input.

The proof has two source-level pieces:

1. `multi_bubble_prefix` fills the nearest (v+1) negative-even holes, taking (4(v+1)^2+2(v+1)) steps and ending at head (2v+2). Its all-prefix maximum is bounded by that endpoint.
2. `stage43_to_C0_delta` gives an (8v+16)-step signed source run. The physical lift splits it into left- and right-extremal sweeps and the final four-step C/0 tail.

The complete-tape `stage43_represented` theorem identifies the prepared zipper with `negFill (jTape (v+2*k+2) (2*v+1)) (v+1)`; it is not a finite-window comparison.

## Concrete root-relevant continuation

The root's simulated J(21,11) checkpoint corresponds to (v=5,k=7). The low43 entry takes 212 steps to C/0 at local head (+16), with every earlier local head at most (+15). From that exact C/0 zipper, the corrected source monitors give:

| Segment | Steps | Net displacement | Maximum displacement from segment entry | Endpoint |
| --- | ---: | ---: | ---: | --- |
| C/0 to J(23,18) | 438 | -20 | +1 | `junc 23 0 18` |
| J(23,18) to J(11,62) | 909 | -37 | +28 | `junc 11 0 62` |
| C/0 to J(11,62), composed | 1347 | -57 | +8 | `junc 11 0 62` |
| J(21,11) to J(23,18), including C/0 entry | 650 | -4 | +17 | `junc 23 0 18` |
| J(21,11) to J(11,62), including C/0 entry | 1559 | -41 | +24 | `junc 11 0 62` |

The 438- and 909-step zipper monitors are concrete finite Lean proofs by `decide` against the imported #429 action/zipper definitions; the 1347-step C/0 monitor is composed with `runWithMax_add`. A local Lean 4.36.0-rc2 harness reproduced the definitions and the two finite proofs without `sorryAx`. The physical lifts in `Low43RootPhysical.lean` transport these monitors through the complete tape representation and retain all-prefix head bounds.

**Correction of the previous candidate:** the earlier 119-step claim to `junc 0 9 25` was false. In this source, `tens 14` has 28 bits because `tens (n+1) = true :: false :: tens n`; it is not a 14-bit word. The exact 119-step execution ends in C with displacement (-59), not at `junc 0 9 25). The subsequent 45-step route to `junc 12 0 22` and the old `root_low43_branch_to_junc12` theorem have therefore been removed. The corrected route is to J(23,18), then J(11,62).

## Root and proof-status limits

The root simulation reaches J(21,11) at step 1608 with head 12 and historical maximum 26. If that checkpoint is established by the separate blank-root source composition, the corrected 1559-step branch reaches J(11,62) at step 3167 with absolute head (-29) and historical maximum 36. This agrees with an independent raw simulation, but the full blank-root prefix to J(21,11) is not yet certified by this dossier.

The manual workflow `.github/workflows/agent32-429-lowodd-frontier.yml` compiles the corrected continuation and physical lifts and audits their axioms. The previous run 43310306538 failed during compilation of the earlier candidate. The corrected declarations have not yet passed the full repository dependency workflow; do not call them CI-certified until a successful run prints their axiom audits and the fail-closed `sorryAx` check passes.

## Remaining mathematical gap

The result closes one prepared low-J (deficit (4k+3)) entrance and a concrete finite continuation. It does not prove that the genuine blank run remains in a closed J/Junc chart for all time. The next root-specific state is J(11,62), whose low-J deficit is (-40); the corresponding complete source return and its history-sensitive maximum must be established. More importantly, the preceding blank-root chain to J(21,11) must be composed and source-verified. No nonhalting conclusion for #429, and no BB(6) bound, follows from these finite branches.
