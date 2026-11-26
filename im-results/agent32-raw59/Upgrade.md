# Raw59 candidate reduction and parent proof

All previously identified open leaves have proposed certificates. The last outstanding computational leaf, 0LB/190, has a source-accepted finite trace: 4,136,170 executed transitions followed by its unassigned C/1 query. The 5,473-action packed certificate and original-source last-hole adapter passed [Late190 run 45675277810](https://github.com/FlareZ123/bb6/actions/runs/45675277810) at source 9ad2992f66eaf06e943d4c1b8f5dffec7060390e. The weighted leaf bound is 4,200,000.

**Parent status:** the complete parent certificate is proposed, not yet source-accepted. [UpgradeAll run 45675872170](https://github.com/FlareZ123/bb6/actions/runs/45675872170) accepted upgraded children 0LE and 1LF, but six groups were unsuccessful. The ClosedBase partition failed because two opened namespaces exported `child`; the qualified `Raw59ParentPartition.lean` now compiles locally against the original 0LE artifact, with standard axioms only (Lean 4.36.0-rc2). The later [1LB run 45695347773](https://github.com/FlareZ123/bb6/actions/runs/45695347773) timed out near child 05 without a Lean diagnostic; its closure log spent roughly 47 minutes between ZeroMaskOracle and the next compilation event. The current existing workflow restores the accepted 0LE dependency manifest before compiling the six remaining groups, reusing only matching source/import/object identities and the identical compiler. It still checks empty residuals and named theorem axiom profiles, then strictly merges all eight shards. The cached UpgradeRemaining run 45707834408 produced no new accepted shards (three worker terminations and three cancellations). The new [bit-synchronous trie checker](TrieRoute.md) has a compiled generic soundness theorem and an initial large-certificate row speed improvement; full leaf and parent acceptance remain pending. Only successful final composition establishes the parent bound. No decrease in the accepted canonical frontier is claimed yet.

A downstream consumer draft now exists at [Raw59Canonical77Graft.lean](Raw59Canonical77Graft.lean). It composes the proposed 4,200,000 parent bound with the already accepted Raw114-cut canonical roster, proves that the Raw59 table survives the Raw114 cut, and filters it to a 76-entry remaining roster. Its `exact_at_target` theorem is conditional on Covers for those 76 entries and the champion witness. This is not yet a source-accepted reduction: it depends on the pending Raw59 parent composition and a separate shared-object Lean check against the accepted canonical77 artifact.

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
