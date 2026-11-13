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

## Concrete low-even r=96 root-route case

A further finite source theorem now covers the next prepared low-even state
in the simulated root itinerary. For (u=49,w=2), the deficit is
(2u-w=96=4\cdot24), and the exact original-table zipper monitor proves

```lean
runWithMax 719 (junc 49 0 2) =
  some (junc 11 0 98, -89, 12)
```

The physical lift `root_low_even_r96_physical` transports this to the
complete original infinite tape: 719 primitive moves, endpoint J(11,98),
head displacement (-89), and every intermediate head at most 12 cells
to the right of the J(49,2) entry head. The proof is a concrete Lean
`by decide` certificate over the exact source zipper transition table,
with a separate signed-source-to-physical lift; it is not an extrapolation
from the finite Python table.

This is one exact instance of the conjectural (r=4k) row in
[Agent 18's low-J chart](../agent18-429-low-j/README.md), not an
all-parameter proof of that residue class. The independent blank-root
simulation places J(49,2) at step 8524 (head 34, historical maximum 39)
and J(11,98) at step 9243 (head -55, historical maximum 46). The
prepared-tape theorem proves the local 719-step transition; the preceding
blank-root composition to J(49,2) is still a separate obligation.

## Continuation beyond J(11,62)

The prepared J(11,62) state has also been advanced through the next
high-three and low-odd return:
- J(11,62) -> J(25,37): 621 steps, displacement +25, maximum +25.
- J(25,37) -> J(10,74): 1836 steps, displacement -34, maximum +43.
- Composed J(11,62) -> J(10,74): 2457 steps, displacement -9, maximum +68.

The 1836-step monitor is a concrete Lean `by decide` certificate for the
(v=18,n=2) low-odd row; it tracks the *entire* return prefix, beyond the
first C/0 frontier. `root_junc11_to_junc10_physical` lifts the composed
2457-step monitor to the complete physical tape. When composed with the
candidate blank-root step-3167 J(11,62) checkpoint, the resulting
`root_after_5624_junc10_frontier` theorem claims J(10,74) at step 5624,
head -38, rightmost mark 39, and exact historical head maximum 39.

The concrete J(49,2) -> J(11,98) r=96 return above is a separate prepared
branch. The high-three ladder connects J(10,74) to J(49,2), but the full
root composition through that ladder and the low-even return has not yet
been written. All root-chain physical declarations remain pending the
manual CI workflow.



The continuation now goes one cycle farther. The two high-three branches
J(10,74) -> J(23,51) (527 steps, +23) and J(23,51) -> J(49,2)
(2373 steps, +49) compose to 2900 steps, displacement +72, maximum +72.
The prepared low-even r=96 return J(49,2) -> J(11,98) then adds 719
steps, displacement -89, maximum +12. The combined physical theorem
`root_junc10_to_junc11_r96_physical` gives J(10,74) -> J(11,98) in
3619 steps, displacement -17, maximum +84. Composed with the candidate
blank-root step-5624 checkpoint, this gives the new
`root_after_9243_junc11_98_frontier`: step 9243, J(11,98), head -55,
rightmost mark 46, exact historical head maximum 46.

The 2900-step high-three monitor was intentionally split into two
smaller `by decide` certificates because the monolithic decision exceeded
the local recursion/compute budget. These are still prepared-source
finite proofs; the blank-root physical composition remains pending the
manual workflow.

## Root and proof-status limits

The root simulation reaches J(21,11) at step 1608 with head 12 and historical maximum 26. If that checkpoint is established by the separate blank-root source composition, the corrected 1559-step branch reaches J(11,62) at step 3167 with absolute head (-29) and historical maximum 36. This agrees with an independent raw simulation, but the full blank-root prefix to J(21,11) is not yet certified by this dossier.

The manual workflow `.github/workflows/agent32-429-lowodd-frontier.yml` compiles the corrected continuation and physical lifts and audits their axioms. The previous run 43310306538 failed during compilation of the earlier candidate. The corrected declarations have not yet passed the full repository dependency workflow; do not call them CI-certified until a successful run prints their axiom audits and the fail-closed `sorryAx` check passes.

## Remaining mathematical gap

The result closes one prepared low-J (deficit (4k+3)) entrance and a concrete finite continuation. It does not prove that the genuine blank run remains in a closed J/Junc chart for all time. The next root-specific state is J(11,62), whose low-J deficit is (-40); the corresponding complete source return and its history-sensitive maximum must be established. More importantly, the preceding blank-root chain to J(21,11) must be composed and source-verified. No nonhalting conclusion for #429, and no BB(6) bound, follows from these finite branches.


### Parity-shifted J(93,173) branch (simulation only)

The proposed `(86,3)` low43 match was off by one. The corrected parameter audit, alternate C/0 tape, and full 134,235-step observed path to J(0,408) are documented in [parity-shifted-junc93-173.md](parity-shifted-junc93-173.md). This is not yet a Lean theorem; the three partial returns and the shifted entry remain open.
