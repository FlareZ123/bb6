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
- **Restriction/bridge pending:** `Agent47Raw11RestrictedQ0.v` is intended to prove that filtering the actual `q_0` frontier by Raw11 equals the two local BFS rounds from `raw11_node`. The first two CI failures were only type/scope issues in metadata and diagnostic output; those have been corrected. The next run is queued as [45844648337](https://github.com/FlareZ123/bb6/actions/runs/45844648337). The exact restriction theorem has not yet been source-accepted.
- **Common parent bound:** the nine local bounds in the table have maximum **234**, not 162. The bridge interface now assumes `Forall (source_table_safe 234) q0_nine_parent_roster` before lifting to 1,000,006.
- **Parent source Covers still pending:** the eight non-33 direct-parent source runs are being generated/compiled separately; root 33 is being sharded by Agent 50. The independent exact-max calculations in `im-results/agent50-q0-index33/exact-sibling-parents.json` are useful corroboration, but are not substitutes for these Coq source Covers.

## What is and is not established

- Established computationally: the 94 exact leaf tables group uniquely under the nine active checkpoint parents above.
- Established in Coq source: the exact nine-parent membership/count theorem described above.
- Not yet established: source-accepted safety Covers for all nine parent rows; the exact Raw11 restriction equality; the backwards-safety bridge; or a Raw11 Cover.
- Root 28 is separate: its one open leaf has a separate symbolic proof and is not part of this 94-leaf bank.

The next useful work is to finish the exact restriction proof, source-check the remaining parent trees, and compose their Covers into one source-queue roster. Do not treat the 94 leaves as 94 queue entries or remove them directly from the checkpoint.
