# Raw36: source-checked parent Cover reduction to nine direct cylinders

**Raw36 remains open.** The eight-hole parent is `1RB---_1RC---_0RD---_0LD---_------_------`. Source-accepted B1=0LE, B1=1RE and B1=1LE Covers now compose with the earlier reductions to leave exactly nine premises at any common weighted threshold B ≥ 1152: the direct D1 moves 0LA, 1LA, 0LB, 0LC, 1LC, 0LE, 0RE, 1LE and 1RE. The exact composition is `BB6.Agent29Raw36.parent_cover_from_nine` in [Raw36ParentLive9.lean](Raw36ParentLive9.lean); the existing parameterized compose runner checks the complete pinned original-source object closure. No nested B1 premise remains. No Canonical40 removal is claimed until all ten remaining cylinders are discharged.

The predecessor `parent_cover_from_twelve` remains a dependency and records the earlier B1=0LB consumption. B1=0LE is source-accepted at weighted bound 1152 in [run 46097780398](https://github.com/FlareZ123/bb6/actions/runs/46097780398), artifact 15249355743; B1=1RE is source-accepted at weighted bound 332 in [run 46112385989](https://github.com/FlareZ123/bb6/actions/runs/46112385989), artifact 15252363171; B1=1LE is source-accepted at weighted bound 387 in [run 46121176787](https://github.com/FlareZ123/bb6/actions/runs/46121176787), artifact 15253439483. Their exact artifact digests and source revisions are pinned in [accepted_pins.json](accepted_pins.json).

## Closed B1 cylinders

All eleven non-0LA rows below have source-accepted original-machine weighted covers at the indicated threshold. The B1=0LA row now also has an unconditional local source-compiled `branch_cover`; its twenty independently accepted child objects are composed using the source-level symmetry theorem.

| B1 action | Weighted bound | Source evidence |
| --- | ---: | --- |
| 0LB | 315 | [46095057554](https://github.com/FlareZ123/bb6/actions/runs/46095057554), artifact 15243776901 |
| 0LE | 1152 | [46097780398](https://github.com/FlareZ123/bb6/actions/runs/46097780398), artifact 15249355743 |
| 0LA | 1022 | [four shards](https://github.com/FlareZ123/bb6/actions/runs/46085477064), local `Raw36Branch.lean` |
| 0RA | 225 | [46089144018](https://github.com/FlareZ123/bb6/actions/runs/46089144018), artifact 15241456595 |
| 0RB | 326 | [46087166988](https://github.com/FlareZ123/bb6/actions/runs/46087166988), artifact 15240236503 |
| 0RC | 105 | same run, artifact 15240191527 |
| 0RD | 85 | same run, artifact 15239309480 |
| 0RE | 245 | [46089144018](https://github.com/FlareZ123/bb6/actions/runs/46089144018), artifact 15242360828 |
| 1LA | 551 | same run, artifact 15242397102 |
| 1LB | 415 | [46087166988](https://github.com/FlareZ123/bb6/actions/runs/46087166988), artifact 15240986373 |
| 1LC | 288 | [46087583776](https://github.com/FlareZ123/bb6/actions/runs/46087583776), artifact 15240727480 |
| 1LE | 387 | [46121176787](https://github.com/FlareZ123/bb6/actions/runs/46121176787), artifact 15253439483 |
| 1RA | 263 | [46089144018](https://github.com/FlareZ123/bb6/actions/runs/46089144018), artifact 15241768281 |
| 1RC | 95 | [46087166988](https://github.com/FlareZ123/bb6/actions/runs/46087166988), artifact 15239643588 |
| 1RE | 332 | [46112385989](https://github.com/FlareZ123/bb6/actions/runs/46112385989), artifact 15252363171 |

The five immediate B1 cycles (0LC, 0LD, 1LD, 1RB, 1RD) and E/F transport are source-accepted in [46076282287](https://github.com/FlareZ123/bb6/actions/runs/46076282287), artifact 15234902017. All nested B1 actions under D1=1LB are now consumed; the parent interface retains only direct D1 children.

**Composition evidence.** On 28 November 2026, the four corrected shard ZIPs, the relevant pilot closure and ten B1 branch ZIPs were retrieved and matched against the GitHub artifact SHA-256 digests. Common imported source/object identities agree; the pilot's obsolete Raw36Kid08 is excluded in favor of the corrected shard object. Using the exact Lean 4.36.0-rc2 executable (SHA-256 db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00), `Raw36Branch.lean` and `Raw36D1Complement.lean` compiled locally. The final `branch_cover` and `d1_cover_from_four` both report only `[propext, Classical.choice, Quot.sound]`. The local root source SHA-256 digests are 4d255a57c9d994364beba263dccb93dca1fd530190e41d63227a38323b0e3811 and f30b8a06e54d695db57e17a93b42e0344a152f7c32e129e3940bc68099c33db6, respectively. The compiled root object SHA-256 values are da675f9c71914204ec6f0f6cd83a79449d0940b22cdc40c1d428334ca8d83931 and 6534567c04e5989a842dc69438ffdb0d7a7ceca4519b49fa89733f69c705497f. [accepted_pins.json](accepted_pins.json) records all input artifacts; [compose_accepted.py](compose_accepted.py) reconstructs the exact selected dependency union and the two new roots without rebuilding the expensive child trees.

## B1=0LA source boundary and earlier FAR correction

The six-hole parent `1RB---_1RC0LA_0RD---_0LD1LB_------_------` admits the source-level C1 E/F equivalence, reducing 24 ordinary moves to 20 representatives plus the true halt action. The earlier candidate-only FAR classifier prematurely stopped its fixed-point iteration (it wrote `change` instead of `changed`). The independent Lean generator rejected that bad evidence. The corrected census identified 393 OPEN leaves across seven C1 representatives (0LE: 5; 0RE: 38; 1LE: 8; 1RA: 134; 1RB: 94; 1RC: 82; 1RE: 32). The exact-table evidence is 350 transferred FAR, 27 reconstructed FAR (codes 101230333/101023202), and 16 sweep invariants. The old duplicate sweep literal ID360 was replaced with its authentic C1=1RE table.

All twenty corrected child roots passed [46085477064](https://github.com/FlareZ123/bb6/actions/runs/46085477064), pinned to `7a78c06e431a4110e5af8df227b51812dcaf7e74`. The corrected conservative threshold 1022 is now a theorem via `Raw36Branch.lean`. The former bound 162 for the entire B1=0LA cylinder is formally false: [46075570333](https://github.com/FlareZ123/bb6/actions/runs/46075570333) accepted the explicit 1016 ordinary-step halter and a weighted lower bound of 1017. Thus the current proven maximum interval is [1017,1022]; exact sharpness at 1022 is not asserted.

## Direct D1=0LC candidate and exceptional theorem

The direct seven-hole cylinder `1RB---_1RC---_0RD---_0LD0LC_------_------` has a new exact canonical discovery tree (773737 nodes, 32241 split nodes, 593100 cycles, 12497 FAR, 135774 last-hole nodes, 125 OPEN literals; weighted halt candidate threshold 172). The 125 sorted OPEN literals have SHA-256 `570f28e662feade63e755b77541f09dfeff21657eeb3028e887f0392009e06ee`. The compact exact-table candidate bank `direct-02-compact.json.xz.b64` supplies 103 FAR certificates, 21 regular-ray certificates and one manual theorem. The manual theorem `BB6.Agent29Raw36D1LCExceptional.never` is locally kernel checked against original `SweepPumping` objects, axiom profile `[propext, Quot.sound]`. It applies to every A1 completion of `1RB---_1RC1RF_0RD1RE_0LD0LC_1LF0RA_0LA0LE`; blank entry 11 reaches state A with empty left zipper and right `0 (1010)^n 10100` at n=0, exact recurrence cost `14*n+25` increments n. The other 124 certificates and whole direct parent still require source composition; no parent Cover is claimed here yet.

## New exact leaf closures and descendant certificates (28 November)

The B1=0LB branch now has a source-accepted weighted Cover at 315 ([run 46095057554](https://github.com/FlareZ123/bb6/actions/runs/46095057554), artifact 15243776901). It is consumed by the locally compiled twelve-cylinder parent theorem.

For direct D1=1LC, all 250 formerly OPEN literal tables are locally kernel-checked against the original TwoSidedAutomata semantics (184 ngram, 46 run-length, 20 modular active inverse-stack certificates). All 250 match the complete canonical discovery tree exactly; the proposed full weighted bound is 366. The full parent closure is dispatched, not yet accepted.

For D1=1LB/B1=1RE, the 187 OPEN leaves now have a complete exact-key certificate bank (126 FAR, 46 sweep, 8 active inverse-stack, 3 late-cycle, 2 regular-ray, 2 manual). The last two were solved symbolically, with local original-source Lean proofs:

* `1RB1LE_1RC1RE_0RD1RF_0LD1LB_1LD0RE_0RA---`: at time 1207, state A has left zipper 0011 and right zipper 0010(00010)^(2+n)000001000010101 T at n=0 and T empty. The same configuration family returns with n+1 and T replaced by 1::T in 144n+758 primitive steps. The recurrence is universal in T. See emit_b122_153.py; growth and never use only propext and Quot.sound.
* `1RB1LE_1RC1RE_0RD0RF_0LD1LB_1LD0RE_1RA---`: let X and Y be state A, left zipper 0101, right zipper respectively 0100010(0010)^n0100 T and 0100010(0010)^n11 T. X(n,T) -> Y(n+1,T) costs 34n+114; Y(n,1^k0U) -> X(n,0^k1U) costs 34n+2k+90, including the implicit blank case Y(n,1^k) -> X(n,0^k1). Blank entry at 221 is Y(1,[]). See emit_b122_150.py; all three transitions and never use only propext and Quot.sound.

Both manual proofs hold for every completion of their F1 hole. The full B1=1RE weighted bound 332 is source accepted in run 46112385989 and consumed by `parent_cover_from_ten`. The exact compact banks are direct-14-compact.json.xz.b64 and d1-22-compact.json.xz.b64; active_cert.py independently replays the active-edge witnesses and emits kernel certificates. The global Canonical40 frontier is unchanged.


## Direct D1=0LB: 313/320 exact active closures

A fresh exhaustive canonical search of `1RB---_1RC---_0RD---_0LD0LB_------_------` at support cut 4 visits 793,761 nodes, has weighted halt candidate threshold 450, and leaves exactly 320 literal OPEN tables after the current FAR bank. Their sorted literal digest is `ad90b7aa9a5268eb5b045e84ffab208cd3bcbbbdfb86a6724f32b5730a34d41c`.

The compact bank `direct-01-partial.json.xz.b64` now supplies replayable two-sided finite-automata certificates for **313 of 320** literals. `generate_d101_partial.py` regenerates the canonical tree, checks the digest, independently replays every active quotient through `active_cert.py`, and emits Lean `NeverHalts` modules. Seven literal machines remain:

- `1RB1LB_1RC1LE_0RD0RF_0LD0LB_1LF---_0LA0RF`
- `1RB1LE_1RC1RE_0RD0RB_0LD0LB_1LB1LF_---0LA`
- `1RB1LF_1RC0RE_0RD1RA_0LD0LB_1LF---_0LA1LC`
- `1RB1LF_1RC1LE_0RD0RE_0LD0LB_0LA0RE_1LB---`
- `1RB1LF_1RC1LE_0RD1RB_0LD0LB_0LA0RC_1LB---`
- `1RB1LF_1RC1LE_0RD1RB_0LD0LB_0LA0RE_1LB---`
- `1RB1RE_1RC1LE_0RD0RB_0LD0LB_1RA0LF_---1LD`

The 313 emitted `NeverHalts` theorems are source-accepted by [run 46123293966](https://github.com/FlareZ123/bb6/actions/runs/46123293966), artifact 15254827367, SHA-256 `bceede8d409935cd00b17e176ef47672a1bd53397cbe38f20532e97838aca92f`. This is an intermediate descendant closure, not yet a Cover of the direct D1=0LB parent; exactly the seven literals above remain.

## Remaining research

Finish the nine direct D1 descendants. B1=1LE is source accepted at bound 387 by resumed run 46121176787; do not repeat any nested B1 closure. Use `parent_cover_from_nine` as the current parent interface, then consume completed direct D1 Covers into that exact live list. The global Canonical40 frontier is unchanged until the full Raw36 parent is proved.

Historical corrected-census data and proof generators remain in this directory. `candidate.json` and old `d1-*.json` are experimental inputs, not proofs; no obsolete pre-correction claimed census should be read as a theorem.
