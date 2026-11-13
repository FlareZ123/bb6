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


## Root-relevant prepared return J(119,35) -> J(109,66)

A new source-level candidate covers the next low-43 parameter pair on the root chart: `v=17,k=50`, so the prepared input is `J(v+2k+2,2v+1)=J(119,35)`.

The new file `Low43RootNext.lean` packages the exact branch:

| Segment | Steps | Endpoint | Head displacement | Prefix maximum |
| --- | ---: | --- | ---: | ---: |
| J(119,35) to its C/0 frontier | 1,484 | `low43_C0_zipper 17 50` | +40 | +40 |
| C/0 frontier continuation | 2,120 | J(109,66) | -68 | +1 |
| Composed prepared return | 3,604 | J(109,66) | -28 | +41 |

The source-level `runNoFatal` certificates guard both pieces and their composition, including the harmless initial C/0 checkpoint. The continuation's source run has no further C/0 visit before J(109,66). The physical theorem lifts the composed endpoint and all-prefix head bound to every complete tape represented by J(119,35).

The C/0 entry at local head +40 is a strict record: the existing uniform `low43_C0_record` theorem bounds every earlier head by +39 and proves the right neighbour at the C/0 checkpoint is blank. The composed endpoint has deficit `2*109-66 = 152 = 4*38`, making it the next root-relevant low-even (r=4k) candidate.

**Validation status:** this new module and the extended manual-only workflow are committed on the `agent32/429-low43-root-next-20261113` branch, but have not yet been compiled by CI in this invocation. Do not treat these new declarations as kernel-validated until the workflow compiles them and its fail-closed `sorryAx` audit passes. The transition is a prepared-Junc result; it does not by itself establish that the blank-root run reaches J(119,35), nor prove an all-time nonhalting claim.


## Prepared continuation through the low-even 4k instance

The new `Low43RootNext.lean` now continues the prepared J(119,35) branch beyond J(109,66):

| Segment | Steps | Endpoint | Head displacement | Prefix maximum |
| --- | ---: | --- | ---: | ---: |
| J(109,66) low-even 4k return (N=33,k=38) | 6,027 | J(11,282) | -209 | +76 |
| Full prepared branch from J(119,35) | 9,631 | J(11,282) | -237 | +48 |

The concrete low-even return has direct `runNoFatal` and `runWithMax` certificates in the candidate Lean module. An independent exploratory zipper simulation found C/0 visits at local steps 4,696 and 5,553, both with blank right neighbours; the Lean `runNoFatal` proof, not the simulation, is the intended certificate. The composed 9,631-step branch exposes every guarded source prefix and lifts to the physical tape with endpoint representation and all-prefix head bound.

The next arithmetic candidate is the outer-safe ladder U=11,25,53 from J(11,282) to J(109,95), followed by low43 parameters v=47,k=30. These steps are not included in the current theorem.

**Validation remains pending:** PR #83 is draft and the extended manual-only workflow has not yet been run. None of the new declarations should be described as kernel-validated until CI compiles the module and the fail-closed `sorryAx` audit passes. This is still a prepared-Junc result, not a blank-root composition or all-time nonhalting proof.


## Extended prepared chain through the second low43 entrance

The same candidate module now packages the next outer-safe and low43 stages:

| Segment | Steps | Endpoint | Head displacement | Prefix maximum |
| --- | ---: | --- | ---: | ---: |
| J(11,282) outer-safe ladder U=11,25,53 | 15,191 | J(109,95) | +187 | +187 |
| J(109,95) low43 entry, v=47,k=30 | 9,704 | C/0 frontier | +100 | +100 |
| v=47,k=30 C/0 continuation | 1,480 | J(69,186) | -188 | +1 |
| Outer ladder + low43 | 26,375 | J(69,186) | +99 | +288 |
| Full prepared chain from J(119,35) | 36,006 | J(69,186) | -138 | +51 |

Each concrete source segment has `runNoFatal` and `runWithMax` certificates in the candidate file; the compositions expose all guarded prefixes and lift to physical tapes represented by J(119,35). The new endpoint has deficit `2*69-186=-48`. A next arithmetic candidate is the outer-safe U=69 step to J(141,45), followed by low-odd parameters v=22,n=58; these steps are not included in the current theorem.

**Validation remains pending:** all new declarations in `Low43RootNext.lean` are still draft candidates until the manual-only workflow compiles the module and its fail-closed `sorryAx` audit passes. The 36,006-step result is a prepared-Junc chain only; it is not yet connected to the blank-root run.


## Blank-root composition through J(69,186): 136,182-step candidate

The integrated branch now carries the r=32 root modules from PR #81 and adds `Low43BlankRootExtension.lean`. Its central theorem, `blank_root_lowEvenR32_to_junc69_186`, composes:

1. the existing 43,862-step blank-root prefix to J(0,216);
2. an outer-safe U=0,3,9,21,45 ladder (11,139 steps) to J(93,45);
3. low-odd v=22,n=34 (3,268 steps) to J(74,90);
4. low42 j=45,k=14 (9,421 steps) to J(0,248);
5. a second outer-safe ladder (11,139 steps) to J(93,77);
6. low-odd v=38,n=26 (7,284 steps) to J(58,154);
7. outer-safe U=58 (14,063 steps) to J(119,35);
8. the new prepared low43/low-even/outer/low43 chain (36,006 steps) to J(69,186).

The resulting checkpoints are at steps 43,862; 55,001; 58,269; 67,690; 78,829; 86,113; 100,176; and 136,182. The theorem states the exact physical run from the blank tape, the corresponding Junc tape representations at each checkpoint, and C/01-freedom at every primitive prefix through step 136,182. This is a finite lower-bound result for machine #429 if the Lean audit passes; it is not an all-time nonhalting proof or an exact BB(6) result.

The combined manual workflow `.github/workflows/agent6-429-low42.yml` now compiles the r=32 root modules, all low43 modules, and `Low43BlankRootExtension.lean`, and audits the new theorem for `sorryAx`. **CI has not yet been dispatched in this invocation; the combined theorem remains a candidate until the workflow passes.**
