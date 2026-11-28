# Raw11 Extra28: twelve-child proof frontier toward a complete parent Cover

**Exact parent:** `1RB0LB_1RC1LC_0LA0LD_------_------_------`.
The original blank run's first unassigned transition is D1 at step 9.
Its 20 normalized moves split into **eight directly translated-cycle-closed
children and twelve nontrivial children**. No full parent Cover has yet been
source-accepted; this remains one strict subcylinder of unresolved Raw11,
not a global BB(6) reduction.

**Best currently established local proof status:** eight of the twelve
nontrivial first-D1 children have complete, locally Lean-4.36.0-rc2-checked
original-source certificate trees. The other four have complete *candidate*
proof trees, but their exact final joins and parent composition have not
passed an original-source CI audit. Thus the candidate parent bound 158
is **conditional**, never a published universal bound.

## Exact 20-way split and current certificates

The D1-normalized action index is `4·nextState + 2·write + direction`,
with left=0, right=1 and nextState A=0 through E=4. Indices
0–6 and 11 are closed by translated-side-cycle witnesses.
The other twelve indices, with their proposed weighted bounds, are:

| D1 index | Action | Bound | Evidence state |
| ---: | --- | ---: | --- |
| 7 | 1RB | 72 | locally kernel checked |
| 8 | 0LC | 42 | locally kernel checked |
| 9 | 0RC | 84 | locally kernel checked |
| 10 | 1LC | 101 | locally kernel checked |
| 12 | 0LD | 64 | locally kernel checked |
| 13 | 0RD | 79 | locally kernel checked |
| 14 | 1LD | 96 | locally kernel checked |
| 15 | 1RD | 119 | locally kernel checked |
| 16 | 0LE | 81 | complete candidate, join outstanding |
| 17 | 0RE | 150 | complete candidate, join outstanding |
| 18 | 1LE | 141 | complete candidate, join outstanding |
| 19 | 1RE | 158 | complete candidate, join outstanding |

The new portable
[`Raw11Extra28AllChildren.lean`](Raw11Extra28AllChildren.lean)
defines the literal original-source parent, checks all eight side leaves
using the existing `PhaseFrontier` checker and keeps *all twelve* remaining
children explicit. It proves an exact 12-code roster and a conditional
`consume` theorem at any B≥42, accepting a complete per-child proof only
through the sound `consumeAt` interface. This bridge intentionally imports
no previous child theorem, so it can be source-audited independently of
the large child proof objects. It does **not** assert that any of its twelve
remaining premises has been discharged. The original-source Lean 4.36.0-rc2 closure **passed**
[run 46103999142](https://github.com/FlareZ123/bb6/actions/runs/46103999142),
pinning the source from commit `bb294092b564`. The workflow checks the
`consume` theorem and its standard-axiom profile, making the twelve-child
frontier a verified conditional mathematical reduction. No sibling proof
premise was silently assumed or discharged in that run.

The explicit [`Raw11Extra28CompleteJoin.lean`](Raw11Extra28CompleteJoin.lean)
provides a **conditional complete parent theorem** at weighted bound 158:
a typed structure `Certificates` accepts one original-child safety proof
at each of the twelve distinct bounds above, constructs the exact twenty
`Route 158` branches, and checks every table identity and the empty
residual list. Once source-accepted, `completeCover` is the rigorous
composition target for all twelve child proofs. The corresponding
`completeCoverAt` lifts this Cover to any B≥158 for the enclosing Raw11
consumer; it currently still requires the four outstanding child proofs.
Source-closure CI was requested using the existing shared manual checker.
The independent [`Raw11Extra28CodeBank.lean`](Raw11Extra28CodeBank.lean)
offers an order-independent finite-bank variant using any proven injective
table code. These lemmas are conditional glue, **not** a current closed
parent or global BB(6) theorem.

## Proof mechanisms and reproduction

- **D1=0LC (bound 42)**: `source.tar.gz` contains the first proof, a
  3,309-node tree. Run `python generate.py && python split.py`;
  compile `Raw11Counter28`, `Raw11Extra28D1LCBase`, the five parts,
  and `Raw11Extra28D1LCJoin`. Exact checked-file hashes are in
  `checked.sha256`.
- **D1=0LD (bound 64)**: `ld-source.tar.gz` contains the 3,357-node
  tree and an unbounded binary-counter transport into original zipper
  semantics. Use `BB6_Q0_AUTOMATA="$PWD/q0-open-automata.cjs" node generate.cjs`,
  check `LD-checked.sha256`, compile counter modules and five LD parts
  plus join. A separate D1=1RE prepared-leaf counter is source checked,
  but that **does not** close the 1RE parent.
- **Other children**: `siblings-source.tar.gz` provides the general
  `ZFast` translated-halfline checker, `ZTree` full proof tree and
  `ZRoute` sound consumer. Run `python prepare-siblings.py`,
  `node make-periodic.cjs`, and `bash generate-siblings.sh 7 9 10 13 14 15 16 17 18 19`.
  The already-local-checked actions are 7,9,10,13,14,15; the other
  four require source-level completed joins.
- **Shared-prefix optimization**: `trace-core.tar.gz` provides
  `ZJoin` (typed exact child roster) and `ZTrace` (reused zipper history).
  Both general checker modules passed local original-source Lean checks
  with only standard axioms. `node generate-trace.cjs 17 18 19`
  creates additional source shards; `build-fast.sh` builds their
  dependency groups. These are proof-producing compiler optimizations,
  not a substitute for checking each generated certificate.

All archived sources target Lean 4.36.0-rc2 against the pinned original
`PhaseTree`/`PhaseFrontier` closure in artifact **15144626755**.
Locally compiled exported theorems had only
`propext`, `Classical.choice`, `Quot.sound`, with no
`sorryAx`/`native_decide`; local builds do not replace an independent
current-source acceptance of the final parent. Since the local shell
execution boundary currently returns `ClientError`, targeted original
source CI for outstanding actions 16–19 was requested using the existing
manual [Agent44 workflow, run 46103874910](https://github.com/FlareZ123/bb6/actions/runs/46103874910).
Keep the exact actual compiler outcome separate from candidate discovery.

## Complete-parent assembly and exact complement

The missing work is **source-accepting the actual twelve child Cover
premises** and feeding them to the conditional full-parent join. The
[existing manual source-closure workflow](../../.github/workflows/agent44-source-bundle.yml)
now offers independently scoped modes, reusing pinned Lean 4.36.0-rc2
and its original-source cache artifact 15144626755:

- `raw11-extra28`: exact child D1 indices 16/17/18/19 in a four-job
  matrix. Run [46105023399](https://github.com/FlareZ123/bb6/actions/runs/46105023399).
- `raw11-eight`: independent source checks of existing children
  7/8/9/10/12/13/14/15 in eight jobs. Run
  [46105098512](https://github.com/FlareZ123/bb6/actions/runs/46105098512).
- `raw11-final`: after both child matrices *succeed*, downloads their
  exact source-accepted proof objects and invokes
  [`assemble-complete.sh`](assemble-complete.sh) and
  [`generate-complete-join.cjs`](generate-complete-join.cjs).
  The final generated theorem `BB6.Agent44Extra28Completed.literal_complete`
  must source-check every child-table identity using `sameTable_sound`
  and export `Cover (WeightedBound 158) parent` without an extra hypothesis.
  This final mode has **not** run; do not mistake the generated theorem
  plan or the conditional `completeCover` for accepted mathematical
  coverage.

A distinct exact-complement consumer is already written for both real
Raw11 frontiers. [`Raw11Extra28AfterRaw11Route.lean`](Raw11Extra28AfterRaw11Route.lean)
starts from the **source-accepted** original 294-residual Raw11 route;
its `cover_from_293` theorem takes an **explicit** complete Extra28
Cover and preserves a 293-member complement, with source-closure run
[46105484000](https://github.com/FlareZ123/bb6/actions/runs/46105484000)
requested. [`Raw11Extra28AfterRaw11Q0152.lean`](Raw11Extra28AfterRaw11Q0152.lean)
offers the corresponding 152→151 exact-table subtraction from the
**locally checked**, but not independently source-accepted, deeper
Agent47 q0+extra consumer. Neither subtraction is an unconditional
Raw11 theorem until the complete Extra28 Cover is supplied. Neither
changes the still-open global Canonical40 obligations.

Separate discovery found complete *candidate*, not complete checked,
parent trees for **Extra53 (84,445 nodes, bound 356)**,
**Extra68 (89,857 nodes, bound 97)** and
**Extra77 (81,601 nodes, bound 208)**. The exact unbounded Extra68
`Raw11Extra68Sweep.lean` leaf is locally original-source kernel checked:
on its parameter k it realizes a 30+26k transition growth recurrence
from a prepared zipper configuration, without relying on finite replay.
The remaining parent joins are open. Those projects should only be
advanced where they can remove an exact live Raw11 residual without
duplicating already certified sibling work.
