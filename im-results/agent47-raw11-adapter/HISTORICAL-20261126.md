# Raw11 q0 automata-to-checkpoint routing

**Agent 47 — 2026-11-26. Intermediate computational result; not a Raw11 Cover.**

## Exact table containment

I compared the 94 entries in `q0-open-automata.json` against the 156 active and one held table in `q0-export/pilot-0-100-fuel-1000000.json`. Tables were normalized by removing row separators, then compared slotwise: a bank leaf extends a checkpoint parent exactly when every fixed parent transition is identical in the leaf.

Every one of the 94 bank leaves extends **exactly one** active checkpoint row. There are no unmatched leaves, ambiguous parents, or duplicate bank tables. The parent groups are:

| q0 active index | Parent table | Open leaves | Scan nodes | Parent bound |
|---:|---|---:|---:|---:|
| 26 | `1RB1RD_1RC0RE_0LA0RF_1LA1LD_---0LA_------` | 13 | 361 | 200 |
| 33 | `1RB1RD_1RC0RE_0LA---_1LA1LD_---0RB_------` | 1 | 985 | 162 |
| 34 | `1RB1RD_1RC0RE_0LA---_1LA1LD_---1LB_------` | 4 | 1,777 | 81 |
| 39 | `1RB1RD_1RC0RE_0LA---_1LA1LD_---1RC_------` | 16 | 1,873 | 144 |
| 44 | `1RB1RD_1RC0RE_0LA---_1LA1LD_---0LE_------` | 5 | 2,041 | 90 |
| 46 | `1RB1RD_1RC0RE_0LA---_1LA1LD_---1LE_------` | 1 | 2,017 | 64 |
| 48 | `1RB1RD_1RC0RE_0LA---_1LA1LD_---0LF_------` | 2 | 3,745 | 151 |
| 49 | `1RB1RD_1RC0RE_0LA---_1LA1LD_---0RF_------` | 21 | 5,785 | 234 |
| 51 | `1RB1RD_1RC0RE_0LA---_1LA1LD_---1RF_------` | 31 | 4,393 | 208 |
| **Total** | | **94** | | |

The 94 leaves are strict refinements, not exact matches to the 9 checkpoint rows. All 9 parent rows are active (none held). The checkpoint has 156 active and 1 held node, so removing these 9 parents after proving their Covers would leave 147 active and 1 held node.

The 94 bank leaves and all 157 checkpoint residuals share the Raw11 fixed prefix A0=1RB, B0=1RC, C0=0LA. This reproduces the routing observation in Critic's 2026-11-26 Raw11 broadcast. The additional result here is the exact one-to-one grouping of all 94 leaves by their active checkpoint parent.

## Existing proof path

`q0-auto-source.cjs` already accepts a root index and constructs the full first-hole tree from the corresponding checkpoint row. It matches every open leaf in the scan against the automata bank, verifies the multiplicities, and emits a Coq `auto_certificate` plus `auto_parent_safe` via `Agent5AutoTree.auto_check_sound`. The existing `shared-rocq-root-proofs.yml` target `enumerate62-q0-auto-root` accepts the root index through its `offset` input.

The current `Agent5Q0AutoConsume.v` is single-parent: its exact count theorem is `(156,1,1,0)`. A nine-parent roster would need to prove `(156,1,9,0)`, preserve the one held node, and leave the other 147 active nodes as obligations. A common source bound of 234 suffices for the nine local parent bounds, subject to the source-accepted parent proofs.

## Coq source checkpoint and current status

- **Membership source accepted:** `Agent47Q0NineParentMembership.v` compiled in CI run [45844062536](https://github.com/FlareZ123/bb6/actions/runs/45844062536). It establishes the exact packed-queue counts `(156 active, 1 held, 9 active covered, 0 held covered)` and the nine active indices `[26;33;34;39;44;46;48;49;51]`. This is a membership/count theorem, not a parent-safety theorem.
- **Restriction source accepted:** `Agent47Raw11RestrictedQ0.v` compiled in [45844648337](https://github.com/FlareZ123/bb6/actions/runs/45844648337), including `raw11_q0_restriction_exact` and the conditional `raw11_safe_from_restricted_q0` backwards-safety lemma. Thus the filtered actual `q_0` frontier is exactly the two local BFS rounds from `raw11_node`.
- **Corrected queue-reduction wrapper accepted:** `Agent13Raw11Q0Bridge.v` compiled in [45849415822](https://github.com/FlareZ123/bb6/actions/runs/45849415822). It re-exports the exact Raw11 frontier identity, counts `(156,1,9,0)`, remainder length 148, and the conditional `q0_nine_consumption` equivalence. It explicitly does not claim a Raw11 Cover from nine rows alone.
- **Common parent bound:** the nine local bounds in the table have maximum **234**, not 162. The bridge interface now assumes `Forall (source_table_safe 234) q0_nine_parent_roster` before lifting to 1,000,006.
- **Parent source Covers still pending:** the earlier ordinary-root jobs and root 33 were cancelled without completing the source proof. In run [45844978833](https://github.com/FlareZ123/bb6/actions/runs/45844978833), the dependency closure and `Agent5SourceAutoTree.v` finished in about 35 seconds after starting the compilation step; `Agent5Q0AutoData.v` then ran for over 37 minutes until cancellation. Root 33's first two shard modules similarly stalled (run [45843560762](https://github.com/FlareZ123/bb6/actions/runs/45843560762)). Thus the immediate bottleneck is certificate-module acceptance rather than dependency installation. The independent exact-max calculations in `im-results/agent50-q0-index33/exact-sibling-parents.json` are useful corroboration, but are not substitutes for Coq Covers.
- **Focused root 26 proof decomposition:** commit `a455fb180a1c11862539533e198ab6e87d9a9d19` reuses the existing direct-parent generator and manual workflow. It emits 346 independently checked leaf certificates and 15 complete first-hole splits in 27 files, with explicit theorem arguments, direct child proof selection in constructor order, and timing/identity markers for each check. The exact 361-node tree, 13 open-bank leaves, and bound 200 remain unchanged. Generator execution succeeded locally in the JavaScript tool runtime; Coq acceptance is pending in [run 45855979854](https://github.com/FlareZ123/bb6/actions/runs/45855979854). This is one focused pilot rather than another eight-root speculative rerun.

## What is and is not established

- Established computationally: the 94 exact leaf tables group uniquely under the nine active checkpoint parents above.
- Established in Coq source: the exact nine-parent membership/count theorem described above.
- Not yet established: source-accepted safety Covers for all nine parent rows; a completed q0 reduction with those Covers supplied; or a Raw11 parent Cover. The wrapper is conditional on the nine parent Covers, and the remaining 148 obligations still need separate discharge.
- Root 28 is separate: its one open leaf has a separate symbolic proof and is not part of this 94-leaf bank.

The exact restriction identity is already source-accepted. The next useful work is to source-check the nine parent trees, prove their common-bound-234 safety, and apply `q0_nine_consumption` to reduce the global q0 obligations to the 148-entry remainder. Do not infer a Raw11 Cover from these nine rows alone, and do not treat the 94 leaves as 94 queue entries.

## Independently kernel-checked Lean root 26 (2026-11-26)

`Root26Lean.lean` establishes `BB6.Agent47Root26.safe : ∀ m, compatible parent m → WeightedBound 200 m` and `cover : Cover (WeightedBound 200) parent` for the exact q0 active index 26 table `1RB1RD_1RC0RE_0LA0RF_1LA1LD_---0LA_------`. The entire 361-node tree contains 159 side-cycle, 86 finite-stack, 101 last-hole leaves, and 15 complete first-hole splits; all 13 previously open-bank entries are consumed. The source is generated by `generate-root26-lean.cjs` from the exact original q0 export and Agent5's reusable certificate bank. It uses the corrected existing `PhaseTree.sound` with explicit undefined-slot premise (commit a5140b164), not a new trusted checker. All 24 top-level child checks use `decide +kernel`; theorem assumptions are `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. Local Lean 4.36.0-rc2 exited 0 using Canonical77 artifact 14997966221, the repository TwoSidedAutomata source and corrected PhaseTree. Exact locally compiled Git blob `3a0a793f9ea9383d37761421dc9dbf9f485da944` is committed in b929db705. The source-original Coq run 45855979854 remains separate; the Lean theorem is not itself a Coq checkpoint consumption. This is a genuine bounded local Cover, not closure of Raw11 or BB(6).

## Additional accepted Lean results and exact Raw11 route

| q0 parent | Nodes | Weighted bound |
|---:|---:|---:|
|26|361|200|
|34|1777|81|
|39|1873|144|
|44|2041|90|
|46|2017|64|
|48|3745|151|

All six safe/cover theorems compiled locally on Lean 4.36.0-rc2 with only standard axioms (propext, Classical.choice, Quot.sound), using the corrected PhaseTree. `generate-q0-lean.cjs` emits chunked kernel-check proofs. Exact source commits: 1258db6c (34/44/46), c0778bde (48 and route), 4ce78c87 (39).

`PhaseFrontier.lean` supplies an independent sound partial-tree consumer (`consumeAt`) allowing proven leaves at bound 234 to be lifted to arbitrary B >=234. The actual Raw11 root is refined by 38 first-hole splits, 306 side-cycle and 54 finite-stack closures; its retained frontier is exactly the 157 source q0 target tables plus 142 other cylinders (299 total). `Raw11Route.lean` checks exact full and remaining roster codes, bidirectional membership, census, and `cover_from_remaining`.

The six accepted local Covers (26,34,39,44,46,48) are now consumed. `Raw11Root39Consume.lean` removes root39 only by exact `sameTable` equality, proves the corresponding table-code and bidirectional roster identities, and establishes the 299→293 census. Its conditional parent theorem needs bounds only for those 293 retained cylinders; root39's bound 144 is lifted to the existing common bound B >=234. The complete Raw11 route plus this consumer passed Lean 4.36.0-rc2 source-closure CI run [45872082943](https://github.com/FlareZ123/bb6/actions/runs/45872082943), with the workflow rejecting `sorryAx` and `native_decide`. This is an exhaustive **conditional** reduction for the actual Raw11 parent, not a standalone Raw11 Cover.

Agent5 has separately kernel-checked q0 root52 at bound 4663 (`Q0Root52.safe_root`, 27,409 nodes, 24 shards, pinned source artifact 15102359679). `Raw11Root52Consume.lean` regenerates that Lean closure from the pinned artifact, reuses the root39 compiled closure, and removes the exact q0 table after root39. The full generated closure and consumer passed Lean 4.36.0-rc2 CI run [45873233270](https://github.com/FlareZ123/bb6/actions/runs/45873233270), producing artifact 15144626755; the workflow rejects `sorryAx` and `native_decide`. The combined conditional Raw11 interface now has a 299→292 residual census for B >=4663.

The 35 Raw11-extra parents with at most four undefined transitions now all have complete Covers: `Raw11Extra91.lean`, `Raw11ExtraSmall.lean` (indices 93–122 and 141), `Raw11Extra123.lean`, plus the recurrence-backed parent 92 and 124 modules generated by `generate-raw11-extra-external.cjs`. Their local bounds range from 20 to 308, and their exact table codes all occur in `Raw11Route.extraCodes`. Parent 92's seven open leaves are discharged by six `Raw11ExtraFamilyCoverage.variantTable` cases and `Raw11ExtraSweepCoverage.table false`; parent 124's sole open leaf is `Raw11ExtraSweepCoverage.table true`. `Raw11Root52ExtrasConsume.lean`'s 35-cover version passed CI run [45889628989](https://github.com/FlareZ123/bb6/actions/runs/45889628989), targeting 299→257 after root39 and root52. The 46-cover expansion is accepted by CI run [45906697676](https://github.com/FlareZ123/bb6/actions/runs/45906697676), proving the exact 299→246 residual census; its generated source/olean bundle is artifact [15159003899](https://github.com/FlareZ123/bb6/actions/runs/45906697676/artifacts/15159003899). The consumer packages Prop-valued Cover proofs with `PSigma`, not `Sigma`.

Three more q0 checkpoint Covers are available in tracked modules: `Root33Lean.lean` (bound 162), `Root49Lean.lean` (234), and `Root51Lean.lean` (208). Their exact table codes (27873199888846492, 27873199888857308, 27873199888858660) all occur in the Raw11 checkpoint roster. `Raw11Root52Q0ParentsConsume.lean` composes these after the extra-parent consumer. The accepted 35-extra/q0 version targets 299→254 and passed CI run [45889628989](https://github.com/FlareZ123/bb6/actions/runs/45889628989); the accepted 46-extra/q0 composition proves 299→243 in run [45906697676](https://github.com/FlareZ123/bb6/actions/runs/45906697676). Both recurrence-backed 92/124 parent modules compiled with axioms [propext, Classical.choice, Quot.sound], and both 35-cover consumer modules compiled locally after the PSigma repair.

A retained-tree scan of all 18 five-hole extras found 11 complete trees with no unresolved leaves (ids 85–90, 125, 135, 136, 138, 139; bounds 195, 98, 101, 91, 87, 41, 47, 245, 123, 97, 147). A reproducible generator and 46-parent consumer expansion are now in place, targeting 299→246 after root39/root52/extras and 299→243 after q0 parents 33/49/51. Those eleven additional Covers are kernel-accepted in run [45906697676](https://github.com/FlareZ123/bb6/actions/runs/45906697676); the artifact preserves the generated modules because the workflow's source-commit step skipped after main advanced. Two other complete five-hole trees (126,137) retain 15 open leaves; five more (127–130,140) exceeded the initial 12,000-node cap.

Next: finish the separate parent-cover candidates 84, 131–134 and 140 (126/137 and 127–130 have already passed their parent-Cover jobs), then build a second consumer from `Raw11Root52Q0ParentsConsume` if further Covers pass. In parallel, resolve the exact first-D entry115 complement; do not infer closure from the 58 Raw11 cylinders, which only occupy its D0=1LA branch. The source-native Coq pipeline remains separate and is not claimed accepted by these Lean proofs.


### Crosswalk to Agent44's first-D frontier

A table-containment comparison against `im-results/agent44-raw11-fresh-cut/fresh-frontier.json` gives a useful but not yet proof-producing crosswalk:

- The 94 q0 automata-bank leaves all refine first-D frontier entry 115.
- The 33 earlier solved Raw11-extra parent tables (91, 93–122, 123, 141) also refine entry 115. The new recurrence-backed parents 92/124 and the five-hole candidates have not yet been placed in this first-D containment partition.
- The full 142 Raw11-extra cylinders distribute as 58 under entry 115, 84 cylinders in 84 other frontier entries, and 31 frontier entries with no extra cylinder.
- Of the 157 q0 checkpoint tables (156 active + 1 held), 140 refine just 8 first-D frontier entries; 16 are coarser than every individual frontier entry, and the held table lies under entry 115.

Containment is not itself a Cover or a union proof: in particular, the 58 extra cylinders under entry 115 and the 16 coarse q0 nodes require an exact partition argument before any first-D frontier entry can be declared closed. The clean source-queue interface currently has 147 q0 checkpoint residuals plus 107 explicit Raw11-extra residuals after the 35-extra Covers; the proposed 11 five-hole Covers would reduce the extra residual to 96. See `Raw11Q0CheckpointIdentity.lean` for a formal Lean draft of the 157-code identity and the 147-code residual correspondence.


## 2026-11-26 accepted expansion and first-D crosswalk

### Accepted Raw11 consumer

CI run [45906697676](https://github.com/FlareZ123/bb6/actions/runs/45906697676) passed the 46-parent expansion and q0-parent composition. The source module `Raw11Root52ExtrasConsume.lean` proves the 46-parent consumption with exact census `(299,246)`; `Raw11Root52Q0ParentsConsume.lean` then consumes q0 parents 33, 49 and 51, proving `(246,243)`. The conditional root theorem still requires Covers for the 243 remaining cylinders. The accepted compiled/source bundle is artifact [15159003899](https://github.com/FlareZ123/bb6/actions/runs/45906697676/artifacts/15159003899); generated parent modules are preserved there because the workflow's source-commit step skipped after main advanced during the run.

### Exact first-D containment result

A fresh slotwise comparison of `raw11-route.json` with Agent 44's `fresh-frontier.json` confirms:
- Raw11 extra indices 0–83 are exactly equal (table-string equality) to 84 distinct first-D frontier entries, one-to-one.
- Raw11 extra indices 84–141 are the 58 strict refinements of first-D entry 115.
- The other 31 first-D frontier entries have no corresponding Raw11 extra; no Raw11 extra is compatible with more than one frontier entry.
- All 58 fix D0 to `1LA`, while entry 115 leaves D0 undefined. They are pairwise incompatible, hence disjoint, but occupy only the D0=`1LA` branch (one of 24 possible transition values). They do not partition or close entry 115; the other 23 D0 branches are outside this Raw11-extra family.

See `communications/broadcast/20261126T2315Z_agent47-entry115-crosswalk-disjointness.md` for the detailed warning and next question.

### Further parent-cover candidates

Separate source-CI jobs accepted Raw11 parent Covers 127–130 (run `45898270704`) and 126, 137 (run `45908444758`). Parent 140's first two attempts were terminated by runner shutdown while compiling a large child module; the generator now recursively splits oversized modules and the workflow compiles the generated import closure against the pinned cache. Parent 133 has a closed retained tree (78,873 nodes, bound 98). Parents 84, 131, 132, 133, 134 and 140 are being checked in separate runs; do not count a candidate until its parent theorem and axiom guard pass.

The 134 candidate exposed one unresolved leaf, `1RB1RD_1RC1LE_0LA1LF_1LA0RD_---0LC_1LA0LB`. A direct simulator reaches its first undefined E0 slot after 1,694 steps. The Raw11 classifier's fallback horizon was raised from 1,500 to 2,500 so the one-hole/last-transition proof can be attempted; this is not yet accepted until the generated Lean proof compiles.


### 2026-11-26 six-parent composition accepted

CI run [45911662010](https://github.com/FlareZ123/bb6/actions/runs/45911662010) compiled Raw11Root52CappedParentsConsume.lean against the accepted 46-parent/q0 artifact and six separate parent-proof artifacts. It composes Covers for Raw11 extra indices 126, 127, 128, 129, 130 and 137, with local bounds 167, 168, 125, 214, 131 and 180.

The new exact census is `(299,237)`: 299 initial residual cylinders, 246 after the 46 extra Covers, 243 after q0 parents 33/49/51, and 237 after these six additional parent Covers. The exact-membership, nodup, subset, census and conditional `cover_from_remaining` theorems all compiled; the CI guard found neither `sorryAx` nor `native_decide`. Artifact [15161045625](https://github.com/FlareZ123/bb6/actions/runs/45911662010/artifacts/15161045625) preserves the consumer source, compiled module and provenance.

This remains a conditional reduction: 237 residual cylinders still require Covers or a further exact partition.


### q0-target crosswalk to the first-D frontier

The 157 q0 targets also admit an exact slotwise crosswalk:
- 20 targets (indices 116–135) refine first-D entry 24.
- 20 (96–115) refine entry 25.
- One each (148, 149, 150, 151) is exactly equal to entries 94, 99, 108, 113 respectively.
- 20 (76–95) refine entry 114.
- 77 (0–75 and 156) refine entry 115.
- The remaining 16 targets (136–147 and 152–155) are disjoint from every first-D frontier entry.

Together with the extra crosswalk, 135 open cylinders (58 extra children plus 77 q0 targets) refine entry 115. They are pairwise disjoint, but their D0 values cover only 18 of 24 transitions; the absent values are 0LA, 0RA, 0LF, 0RF, 1LF and 1RF. The 16 out-of-frontier q0 targets and 24 first-D entries with no Raw11 open target still need an explicit tree-level explanation. They may be discharged by internal Raw11 route nodes, but this must be checked against the route proof tree, not inferred from the crosswalk.

See `communications/broadcast/20261126T2337Z_agent47-q0-firstd-crosswalk.md`.
