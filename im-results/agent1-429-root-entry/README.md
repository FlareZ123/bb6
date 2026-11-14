# Exact blank-root entry and initial head-frontier development for #429

## Mathematical statement

For the explicit complete twelve-slot table `source429`, the blank A-root
executes exactly 35 successful primitive transitions and reaches the
configuration `j00Config`:

- state A;
- absolute head coordinate 3;
- marked cells exactly `[-3,4] ∪ {6}`;
- equivalently, relative to the head, marked cells `[-6,1] ∪ {3}`.

The final tape has the defining support pattern of J(0,0). `JRootEntry.lean`
records the complete table (including the genuine D/1 halt), the ordered
35 writes, the exact support theorem, and
`run source429 35 blank = some j00Config`.

## Root-history and gate-safety lemmas

The file defines a raw physical `runWithHeadMax` monitor. It includes the
initial and final configurations and updates the maximum at every successful
primitive step. The generic theorem `runWithHeadMax_projects` proves that a
successful monitored run projects to the repository's ordinary `run`
semantics, so the monitor changes no transition or halt convention.

The monitor also has a proved segment-composition law,
`runWithHeadMax_add`: the maximum over a concatenated run is the maximum
of the two segment maxima. `runWithHeadMax_two_of_rawSteps` gives its exact
two-transition specialization.

Three reusable lemmas now formalize the frontier mechanism:

1. `runWithHeadMax_tape_above`: every tape cell strictly to the right of a
   successful run's maximum head coordinate is unchanged from the input tape.
2. `runWithHeadMax_current_max_right_blank`: if the monitored endpoint is
   itself at the reported maximum and the input tape has a blank right tail
   beginning no farther right than that maximum, then the endpoint's right
   neighbor is blank.
3. `c0GateAfterTwo_frontier`: the C/0-to-D/0 two-step gate writes the new
   rightmost mark one cell beyond its input head whenever the old tape had a
   right blank tail.

The local gate lemma `source429_c0_gate_two_steps` proves that a C/0
configuration with a blank right neighbor executes C/0 then D/0, writing a
new 1 at the next cell and returning left in E/1. The companion
`c0GateAfterTwo_frontier` proves that this new cell is the rightmost mark
when the input already had a blank right tail. This packages the exact
mechanism by which a C/0 event at the current global head frontier is safe
and advances the frontier by one.

## Concrete blank-root prefix

The explicit-table raw monitor proves:

- After 35 steps, the endpoint head is 3, the maximum visited head is 6,
  and the rightmost mark is 6.
- The next 110-step continuation from that endpoint has head maximum 12,
  endpoint head -3, a mark at 12, and no marks to its right.
- After 271 total root steps, the endpoint head is 11, the maximum visited
  head is 12, and the rightmost mark is still 12.
- At the 275-step endpoint, the machine is in C/0 at head 15, which is the
  current global head maximum. The generic monitor lemma proves cell 16
  blank; it is not accepted by direct table lookup alone.
- The C/0-to-D/0 continuation then writes cell 16. After 277 total steps,
  the endpoint is E/1 at head 15, the global maximum is 16, cell 16 is
  marked, and every cell to its right is blank. The 277-step monitor result
  is now derived compositionally from the 275-step prefix and the generic
  two-step gate monitor via `runWithHeadMax_add`; the endpoint is proved
  equal to the gate's exact post-state.

Thus the root-connected finite prefix exhibits the invariant pattern
`historicalHeadMaximum = currentRightmostMarkedCell` at its certified
frontier checkpoints (6, 12, then 16). This is a finite root-history result,
not an all-time invariant.

## Extended source-connected J-chart prefix (new candidate)

`RootToJunc.lean` supplies the 145-step blank-root checkpoint
J(0,12), at absolute head (-3), with head maximum 12 and a complete
physical `Represents` proof. The new `RootJunctionChain.lean` adds an
exact 1463-step source-zipper monitor

```lean
runWithMax 1463 (junc 0 0 12) =
  some (junc 21 0 11, 15, 29)
```

and lifts it to the complete physical tape. The physical segment begins at
head (-3), ends at head 12, and every primitive prefix has head at most
26. Composed with the 145-step root checkpoint, this gives the candidate
blank-root statement at step 1608: J(21,11), head 12, rightmost mark 26,
and exact historical head maximum 26.

The same file composes the corrected low43 physical branch from J(21,11)
to J(11,62). It gives a 1559-step segment, net head displacement (-41),
and local prefix maximum (+24). After translating the segment by the
root head coordinate 12, the resulting candidate blank-root checkpoint is
step 3167, J(11,62), head (-29), rightmost mark 36, and exact historical
head maximum 36. The proof reconstructs a raw `runWithHeadMax` monitor
from raw-run success and all-prefix bounds; the lower bound on the maximum
comes from the newly marked rightmost endpoint cell, while the upper bound
comes from the physical prefix monitor.



The same chain is now extended another 2457 steps. A concrete high-three
branch J(11,62) -> J(25,37) takes 621 steps with displacement +25 and
maximum +25. The exact (v=18,n=2) low-odd return J(25,37) -> J(10,74)
takes 1836 steps with displacement (-34) and full-prefix maximum +43.
Composing these monitors gives J(11,62) -> J(10,74) in 2457 steps,
displacement (-9), maximum +68. The physical lift in
`Low43RootPhysical.lean` retains the all-prefix bound. The new
`root_after_5624_junc10_frontier` theorem in `RootJunctionChain.lean`
therefore claims the blank root reaches J(10,74) at step 5624, head -38,
rightmost mark 39, and exact historical head maximum 39.

The 1836-step low-odd maximum is a concrete `by decide` monitor, not a
general low-odd max theorem. The next simulated state J(49,2) is reached
from J(10,74) by the existing high-three ladder, and its concrete
r=96 return to J(11,98) is separately formalized as a prepared-input
physical theorem. The full root composition through J(49,2) and J(11,98)
is still pending.



The high-three ladder from J(10,74) to J(49,2) is now monitored in two
separate exact source chunks: J(10,74) -> J(23,51) in 527 steps
(displacement/max +23), then J(23,51) -> J(49,2) in 2373 steps
(displacement/max +49). Their composition is 2900 steps, displacement
+72, maximum +72. Composing the concrete low-even r=96 return
J(49,2) -> J(11,98) (719 steps, displacement -89, maximum +12)
gives a 3619-step J(10,74) -> J(11,98) physical segment with
displacement -17 and maximum +84. The new
`root_after_9243_junc11_98_frontier` theorem claims the blank root reaches
J(11,98) at step 9243, head -55, rightmost mark 46, and exact historical
head maximum 46. The 2900-step monitor is composed from two smaller
`by decide` certificates; the monolithic 2900-step decision exceeded
the local recursion/compute budget.

These declarations are kept in `im-results/` pending the full dependency
workflow. The finite zipper equations were reproduced locally with Lean
4.36.0-rc2 and `by decide`, but the composed physical file has not yet
passed repository CI. The manual workflow
`.github/workflows/agent1-429-root-junction-chain.yml` builds the root,
high-zero, high-three, low43, and physical dependencies, then checks the
new root-after-1608 and root-after-3167 axiom reports and rejects
`sorryAx`. It has not yet been dispatched. Until that workflow succeeds,
treat this as a source-level proof candidate rather than CI-certified
evidence.

## Evidence and source boundary

The 35-step and finite-prefix monitor equations are kernel computations.
The generic monitor projection, head-bound, tape-above, and gate-safety
lemmas are Lean-proved. The exact finite-support tape theorem is proved by
case splitting over the write support and integer arithmetic. A local Lean
4.36.0-rc2 preflight against a source-equivalent copy of the relevant
`BB6Coverage` operational definitions (`Config`, `run`, `rawStep`,
and `applyMove`) compiles the declarations; the axiom reports contain only
standard axioms (`propext`, `Classical.choice`, `Quot.sound` as needed),
with no `sorryAx`.

The explicit table bridge is now present in [SourceBridge.lean](SourceBridge.lean).
Its kernel proof establishes pointwise equality
`source429 = BB429PhysicalFrontier.target429` by exhausting all twelve
state-symbol slots. It then transfers both the 35-step blank-root entry and
the 277-step monitored frontier certificate to the repository's canonical
physical #429 table. The generic monitored-record C/0 frontier theorem is
also transferred to `target429`.

The bridge now imports the canonical `JPhysicalPrefix` module and proves
`rootTape_matches_physical_j00`: the 35-step endpoint tape is exactly
`BB429JPhysical.jTape 0 0`, translated by the absolute head coordinate 3.
Thus the root entry is not merely shape-compatible with a locally defined
predicate; it is identified with the physical J(0,0) tape used by the
source-connected J/Junc developments.

The bridge has been locally preflighted against a minimal replica of the
repository's `PartialMachine`, `refine`, and eleven-entry completion
definitions. This confirms the proof script and table equality, but is not a
substitute for compiling against the actual imported physical module. The
manual workflow `.github/workflows/agent1-429-physical-frontier.yml` now
compiles `JRootEntry.lean` and `SourceBridge.lean` after the actual
`BB429PhysicalFrontier.olean` is built, and checks that the source-identity
and 277-step frontier theorems appear in the axiom audit. That updated
workflow has not yet been dispatched. The smaller
`.github/workflows/agent1-429-root-entry.yml` remains a standalone
operational-definition preflight.

## Why the entry matters

The exact root base and the generic gate-safety lemma isolate a concrete
route to the global C/0 argument: maintain
`historicalHeadMaximum ≤ currentRightmostMarkedCell` across every J/Junc
macro; show each exceptional C/0 gate occurs at or beyond the old frontier;
then its right neighbor is blank, and the C/0-to-D/0 pair advances the
rightmost mark to cover the new maximum.

The existing ordinary and exceptional macro certificates provide many of
the local pieces. The missing theorem is their source-connected, all-time
composition along the actual blank-root orbit.

## Remaining open problem

The blank-root orbit now has a **source-level finite proof candidate** through
Junc(45,0,58) at primitive step **16,280**. The appended regular-chart
segment has an exact physical frontier theorem: its 2,562 primitive steps
preserve the absolute rightmost marked cell, and every head position in that
segment remains strictly to its left. The all-prefix source/physical
composition also excludes C/01 through step 16,280. This remains a finite
prefix certificate, not an all-time invariant or a nonhalting proof.

The next root-connected leaf is the concrete low-even r=32 segment
Junc(45,0,58) -> Junc(11,0,146), proposed at 4,407 primitive steps. Agent 32
owns its source no-fatal and physical proof in PR #81; the reported recent
source-proof CI attempts failed, so do not treat the conditional prepared
input theorem as an authentic blank-root result or as CI-certified evidence.
Further low-deficit cases and the all-time physical frontier/history
invariant remain open.

Keep this work in `im-results/`. It is not a complete #429 decision, a BB(6)
bound improvement, or a BB(6) solution.

## Root suffix after J(11,98): outer-safe, low42, and regular-chart bridge

The step-9,243 root frontier is J(11,98), with physical head -55 and
rightmost mark 46. The two all-parameter outer-safe returns are:

- J(11,98) -> J(25,73), 621 steps;
- J(25,73) -> J(53,20), 2,777 steps.

Their 3,398-step source run is C/0-free at every processed instruction and
has net head displacement +78, reaching head +23 at step 12,641.

J(53,20) is the concrete low42 instance j=10, k=21. The 1,077-step
`Low42RootNoFatal` source audit records exactly two C/0 starts, at local
times 510 and 919; both have a blank right neighbor. Its guarded source run
and physical lift exclude C/01 throughout and reach Junc(0,0,136), with net
head displacement -109 from the J(53,20) entry.

Agent 48's `RootNoFatalChain.lean` composes the original 9,243-step
blank-root prefix, the 3,398-step outer-safe suffix, and the 1,077-step
low42 suffix. Its theorem
`BB429RootNoFatalChain.blank_root_no_fatal_to_junc136` states that the
blank root reaches a configuration represented by Junc(0,0,136) at step
**13,718**, with C/01 excluded at every physical prefix through the
endpoint.

The new `RootJunc136To45.lean` then composes the seven ordinary Junc
segments:

| Segment | Transition | Steps | Endpoint |
|---|---|---:|---|
| 1 | zero-u, v=0, w=136 | 27 | Junc(3,0,133) |
| 2 | positive-u, 3 returns | 54 | Junc(0,6,127) |
| 3 | zero-u, v=6, w=127 | 39 | Junc(9,0,124) |
| 4 | positive-u, 9 returns | 378 | Junc(0,18,106) |
| 5 | zero-u, v=18, w=106 | 63 | Junc(21,0,103) |
| 6 | positive-u, 21 returns | 1,890 | Junc(0,42,61) |
| 7 | zero-u, v=42, w=61 | 111 | Junc(45,0,58) |

The exact total is **2,562**. The source composition uses the existing
C/0-free `junc0_regular_safe` and `junc_positive_iter_safe` theorems.
Its physical lift composes the ordinary-return prefix bounds and frontier
conservation theorems. If the Junc(0,0,136) input has head h, the original
rightmost mark is at h+139; every head in the appended 2,562-step segment
is strictly below h+139, and the Junc(45,0,58) endpoint has its rightmost
mark at the same absolute coordinate (endpoint head +61 = h+139).

The resulting candidate theorem
`BB429RootJunc136To45.blank_root_no_fatal_to_junc45` composes that segment
with Agent 48's 13,718-step root certificate. It gives a 16,280-step
blank-root path to Junc(45,0,58), excludes C/01 at every physical prefix,
and retains the regular-segment frontier bound. This is the correct
prepared input for Agent 32's 4,407-step r=32 continuation.

## Verification status and source boundary

The 35-step blank-root entry and the original-table bridge have local
Lean 4.36.0-rc2 proof-script preflights described above. The finite
RootJunctionChain monitors and the newer 13,718-/16,280-step physical
composition candidates still require an unchanged-original-source CI run.
The manual-only workflow
`.github/workflows/agent6-429-low42.yml` builds the low42 and outer-safe
dependencies; it must also compile Agent 48's
`NoFatalGuard`, `RootNoFatalPrefix`, `RootNoFatalPhysical`, and
`RootNoFatalChain`, followed by the ordinary physical-frontier modules and
`RootJunc136To45.lean`. The audit must check the named theorem axiom
reports and reject `sorryAx`. The workflow remains manual-only; no
push-triggered validation is claimed.

Until that end-to-end run succeeds, the 13,718-step and 16,280-step results
are **Lean proof candidates, not CI-certified original-source results**.
They are finite prefixes only and do not decide #429 or BB(6).


## Candidate continuation after Junc(0,744): Junc(0,924) (2026-11-14)

The current PR #94 source candidate reaches Junc(0,744) at primitive step
1,514,038. The new continuation module proposes a further 1,158,049-step
physical run to Junc(0,924), with exact head displacement -139. The route is
compositional:

| Segment | Transition | Steps | Head displacement |
|---|---|---:|---:|
| Outer-safe ladder | Junc(0,744) -> Junc(381,3) | 191,493 | +741 |
| Low43 gap | Junc(381,3) -> Junc(387,2) | 7,382 | +4 |
| Low-even 4k | Junc(387,2) -> Junc(11,774) | 3,761 | -765 |
| Three +32 returns | Junc(11,774) -> Junc(11,870) | 683,267 | -75 |
| Outer-safe ladder | Junc(11,870) -> Junc(445,17) | 261,433 | +853 |
| Low-odd | Junc(445,17) -> Junc(440,34) | 5,306 | -14 |
| Low42 | Junc(440,34) -> Junc(0,924) | 5,407 | -883 |
| **Total** | **Junc(0,744) -> Junc(0,924)** | **1,158,049** | **-139** |

The central new reusable return is in `Junc11Return32.lean`. For
N+2K=221 and K>=1, it composes four outer-safe reductions with the
parameterized low-even 4k return:

`Junc(11,408+2N) -> Junc(11,440+2N)`

in `64093 + 4N^2 + 22N + 18K` steps, with head displacement -25.
The three route instances are (N,K)=(183,19),(199,11),(215,3), giving
Junc(11,774) -> Junc(11,870) in 683,267 steps. The same family also
supplies the 3,761-step Junc(387,2) -> Junc(11,774) return (N=1,K=193).

`Junc744To924.lean` lifts the low43 and low-odd canonical runs to arbitrary
physical Junc representations, composes all seven segments, and applies the
physical C/01 converse at the live Junc(0,924) endpoint. Its candidate
theorem `junc0_744_to_junc0_924_physical` therefore states all-prefix
C/01-freedom for the entire 1,158,049-step interval. The theorem
`blank_root_to_junc0_924` composes this with the 1,514,038-step
blank-root-to-Junc(0,744) candidate, yielding a 2,672,087-step
blank-root prefix ending at Junc(0,924), again with C/01 excluded at every
primitive prefix.

**Verification status:** these are source-proof candidates, not yet
CI-certified original-source results. The separate PR #82 low-even 4k
workflow is currently testing the parameterized dependency. The new manual
workflow `.github/workflows/agent1-429-junc744-to924.yml` compiles the
full dependency graph, the new modules, and their axiom reports; it rejects
any `sorryAx`. It has not yet been dispatched. Do not promote these
statements to `results/` or claim a BB(6) bound improvement until that
original-source CI run succeeds.


## Second continuation: Junc(0,924) -> Junc(0,1008) (2026-11-14)

The uniform low43 Junc-to-Junc theorem in `Low43C0Uniform.lean` permits a
second continuation beyond the special v=1,k=189 gap used above. Starting
from Junc(0,924), seven outer-safe returns reach Junc(381,183). The uniform
low43 instance (v,k)=(91,144) then reaches Junc(297,362), followed by a
low-even 4k return, a five-step outer ladder, low-odd, and low42:

| Segment | Transition | Steps | Head displacement |
|---|---|---:|---:|
| Outer-safe ladder | Junc(0,924) -> Junc(381,183) | 191,493 | +741 |
| Uniform low43, (v,k)=(91,144) | Junc(381,183) -> Junc(297,362) | 40,772 | -176 |
| Low-even 4k, (N,K)=(181,58) | Junc(297,362) -> Junc(11,954) | 136,331 | -585 |
| Outer-safe ladder | Junc(11,954) -> Junc(445,101) | 261,433 | +853 |
| Low-odd, (v,n)=(50,196) | Junc(445,101) -> Junc(398,202) | 15,512 | -98 |
| Low42, (j,k)=(101,148) | Junc(398,202) -> Junc(0,1008) | 45,769 | -799 |
| **Total** | **Junc(0,924) -> Junc(0,1008)** | **691,310** | **-64** |

`Junc924To1008.lean` lifts the uniform low43 canonical run to arbitrary
physical Junc representations, proves each segment, and composes the
physical run. The final live Junc(0,1008) endpoint gives all-prefix C/01
exclusion. Composing with `blank_root_to_junc0_924` yields a candidate
blank-root prefix of **3,363,397** primitive steps ending at Junc(0,1008),
with C/01 excluded at every primitive prefix.

This extension depends on `W4JuncOne.lean`, `W4JuncGeneral.lean`, and
`Low43C0Uniform.lean`; the dedicated workflow now compiles these modules
and audits the new endpoint theorems. This remains an intermediate
source-proof candidate until the complete manual CI workflow passes with
no `sorryAx`.


## Next candidate: a uniform +52 return

`Junc0Plus52Sketch.md` derives an unformalized parameterized composition
`Junc(0,2v+742) -> Junc(0,2v+794)` for odd (131\le v\le177), with
head displacement -39. The two root-connected instances (v=133) and
(v=159) would extend Junc(0,1008) -> Junc(0,1060) -> Junc(0,1112),
adding 1,218,428 steps and giving a 4,581,825-step blank-root prefix.
This is an algebraic proof plan only; it is not yet formalized or included
in the CI workflow.

A proposed +60 continuation beyond Junc(0,1112) was rejected: its
second low-odd step has a parity mismatch (`n=417/2`). The correction is
recorded in `Junc0Plus52Sketch.md`; do not use the rejected route.
