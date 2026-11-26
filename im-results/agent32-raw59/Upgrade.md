# Raw59 candidate reduction and parent proof

**Parent status: one remaining child, Upgrade0LA.** The proposed parent weighted bound is 4,200,000. All other required child/group artifacts have passed their individual source-checked jobs: Upgrade0LE and Upgrade1LF in [45675872170](https://github.com/FlareZ123/bb6/actions/runs/45675872170), Upgrade1LE and ClosedA–F in [45727352966](https://github.com/FlareZ123/bb6/actions/runs/45727352966), and Upgrade0LB, Upgrade0LF, Upgrade1LB in [45742419127](https://github.com/FlareZ123/bb6/actions/runs/45742419127). These mixed-revision jobs are not a parent acceptance: the final merger checks the source, object and import-closure identities and runs Raw59ParentCover against the composed closure. The last substantial 0LB computational leaf, index 190, has a source-accepted finite trace of 4,136,170 executed transitions followed by its unassigned C/1 query, using 5,473 packed actions in [45675277810](https://github.com/FlareZ123/bb6/actions/runs/45675277810) at source 9ad2992f66eaf06e943d4c1b8f5dffec7060390e.

### Focused 0LA repair: proof-carrying packed exact traces

[45756260211](https://github.com/FlareZ123/bb6/actions/runs/45756260211) failed at Raw59Upgrade0LAKid11.lean:4078:84 with maxRecDepth. The actual preserved source artifact 15088512701 identifies the entire partialCheck theorem c_kid11_18_13, not an individual q theorem or the preceding 927-entry cycle. The split includes several long final-hole traces (26334, 66552, 26298, 26346). The 66552-step table is 1RB0LA_1RC0LC_0RD0RF_1LD1RE_---1LA_1RA1LB, with final unassigned E/0; the exact Python trajectory has 66552 live steps. This is an untrusted trace witness until its concrete Lean theorem is accepted.

[Raw59PackedQuery.lean](Raw59PackedQuery.lean) proves exact packed-step and run correspondence to the original SweepPumping and zipper semantics, then reduces a last-hole PartialAudit proof to a certified exact final read, the final unassigned slot, restOK, and n+6≤B. [Raw59PackedMacro.lean](Raw59PackedMacro.lean) proves that a block-transfer rule valid over arbitrary untouched tails can be iterated exactly n times, with primitive cost k*n. It checks packed trace segments by induction and composes their exact costs. Both source modules compiled locally with Lean 4.36.0-rc2 against the original accepted 0LE artifact 15054146521; printed theorem axiom dependencies are standard propext, Classical.choice, Quot.sound. The new generator mines repeated query words and verifies the candidate framed rule and each checkpoint in Lean. It selects 0LA late final-hole leaves with n≥5000, emits independent modules, forces the tree proof to split down to their leaves, and transports the checked literal table to the exact original refined table via tableOK_sound. Other child source generation is unchanged. Commit 6481ee1b1e6f900ba6da4296c164f8da723469b8 implements the route; [focused run 45780862896](https://github.com/FlareZ123/bb6/actions/runs/45780862896) is the current acceptance attempt.

For the long test leaf the miner obtains seven sweep rules and 780 actions, with 62273 steps covered by repeated sweeps and 4279 raw steps. The local initial group proof passed; complete trace attempts hit 120s/240s local limits, without a false equality diagnostic. A follow-up closed-form repetition and sealed-prefix bridge checker is being tested to reduce primitive computation further. No parent Cover or reduction of the canonical roster follows before source acceptance.

### Integration

Canonical64 is the accepted roster; coordinate any eventual Raw59 cut with the existing single direct-from-Canonical64 parent-list programme (Agent31/Agent4). The older Raw59Canonical77Graft and Raw59Raw112Canonical62Integrated files are historical/provisional consumers, not accepted frontier reductions. The parent itself must first pass its source and axiom gates.

## Earlier reduction and certificate details

Baseline: prior checked partial audits in run 45547813131, source c8aa2607ad4711501e18e0943eec70e9475fd834. Retrieved all seven exact residual artifacts and matched them against the SHA-pinned enumeration.

| child | baseline residuals | new sparse-window candidates | new sweep candidates | prospective remainder |
|---|---:|---:|---:|---:|
| 0LA | 242 | 52 | 27 | 163 |
| 0LB | 35 | 18 | 6 | 11 |
| 0LE | 160 | 10 | 132 | 18 |
| 0LF | 149 | 40 | 0 | 109 |
| 1LB | 46 | 13 | 27 | 6 |
| 1LE | 34 | 5 | 22 | 7 |
| 1LF | 65 | 3 | 0 | 62 |
| Total | 731 | 141 | 214 | 376 |

### Final six known 1LB candidates

[Raw59LB1Sweep1734.lean](Raw59LB1Sweep1734.lean) gives the exact partial table `1RB1LB_1RC1RF_0RD0LE_1LD1RE_---1LA_0RA0RB` (E/0 unassigned), open index 1734 in the SHA-pinned 1LB enumeration. In the existing zipper convention (head at the first bit of the left list), define D(n) with left word `0 (011)^(n+2) (01)^(4(n+1))` and empty right list. The blank run reaches D(0) after 104 steps. For every n, D(n) returns to D(n+1) after exactly `120(n+1)+101` steps. The proof composes two exact left/right sweep pairs: 4-step `10` transfer, 17-step framed `110 -> 010`, 12-step `1010 -> 0101`, and 3-step `100 -> 011` transfers, with arbitrary untouched tails. Entry and growth compile locally with Lean 4.36.0-rc2 against the copied computational SweepPumping core (axioms: propext and Quot.sound only). The original-source `never` bridge passed [run 45632801815](https://github.com/FlareZ123/bb6/actions/runs/45632801815). The earlier sweep for 583 passed [run 45595774004](https://github.com/FlareZ123/bb6/actions/runs/45595774004). The upgrade generator binds the certificate to the SHA-pinned exact leaf; only source acceptance of the full audit permits removing it from the retained complement. This additional candidate is not included in the earlier table. No new parent or global coverage count is claimed.

The four other exact retained indices are 189, 190, 191 and 194 (F/0 remains unassigned; E/0 is respectively 1LA, 1LC, 1LD, 1RD in the common table `1RB1LB_1RC0LB_0RD0RF_1LD1RE_???1LA_---1RA`). The existing two-sided DFA witnesses for 189 and 191 close under saturation (873 and 888 abstract configurations, 117 edges each). The two previously unresolved leaves now have one-sided block-FAR witnesses from the forward saturation algorithm:

| Index | Block width | Run cap | Run modulus | Retained runs | Left states before quotient | NFA nodes before quotient |
|---|---:|---:|---:|---:|---:|---:|
| 190 | 4 | 1 | 7 | 6 | 434 | 1321 |
| 194 | 2 | 3 | 2 | 3 | 51 | 448 |

Unreflected in both cases. The larger width-six witness for 190 also closed (cap 2, modulus 2, five runs), but width four has a smaller source proof. `generate_lb1_four.py` deterministically generates the finite checker witnesses, original coverage adapters and previous rungram certificates. The updated SHA-pinned audit generator binds all four exact tables to their leaf indices. [Source verification run 45657895022](https://github.com/FlareZ123/bb6/actions/runs/45657895022) targets the four leaves; full 1LB audit still required. These candidate results are not yet a closed source-checked parent.

All candidate sets disjoint relative to the baseline. Counts are candidate reductions, not source-accepted coverage. The historical largest sparse candidate (0LF 1530, 92189 states) required additional treatment; the current upgrade generator proposes a full cover. The exact source-checked residual files and final theorem, rather than historical counts, determine acceptance.

The compact manifests are gzip/base64; python upgrade_data.py decodes the actual entries. IDs are bound by the original source enumerator's SHA checks. Sweep generator uses the existing exact arbitrary-tail sweep induction, including the blank-entry equality, and sparse certificates use the independent-width checker. The existing partial audit's typed .proven constructor consumes only original-source nonhalting theorems. The new --upgrade flag writes separate Upgrade source modules and preserves the previously accepted baseline. Target UpgradeAll, or Upgrade1LB etc in the existing manual workflow.

Initial asymmetric pilot [run 45559896528](https://github.com/FlareZ123/bb6/actions/runs/45559896528) completed successfully. Prior accepted return-family proofs are not counted here unless the upgrade actually consumes them.

The parent workflow now also accepts `raw59_child=UpgradeRemaining`: it checks only `Upgrade0LA`, `Upgrade0LB`, `Upgrade0LF`, `Upgrade1LB`, `Upgrade1LE`, and `ClosedBase`, reusing the already checked `Upgrade0LE` and `Upgrade1LF` artifacts from run 45675872170. The parent composition still validates all eight shard manifests before accepting the 4,200,000 bound. Its accepted artifact now retains the merged child `.olean` closure so the canonical77 consumer can be compiled without rebuilding either side.

The mixed-revision shard merge is deliberate: the two reused artifacts predate the current workflow commit. `merge_shards.py` still verifies every source and provenance-input hash against the checkout/artifact, the full project-import closure, Lean version and compiler binary hash, module identity, and `.olean` hash; only the commit-SHA equality requirement is relaxed.
