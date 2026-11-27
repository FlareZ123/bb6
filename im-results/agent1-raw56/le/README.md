# Raw56 E1=0LE conditional frontier

Parent `1RB---_1RC---_0RD---_1LD1LE_---0LE_------` queries E0 at step 7. The exact canonical search (cut.cpp blob `88d5dfc4994f8bd203fe3f3def5ea90efda86037`, cap 1000, lookback 32, depth 7) reports 514070 cycles, 219588 last-hole cases, 33050 splits, zero aliases, and 26493 open leaves. Full tree SHA256 `07d7c27d6d5d09587b9e693229cb9558b6199a2d8f732f2097ccb3fbf27d905e`, open-list SHA256 `aba63f28439c707c3343fd4ff53f66717d5924b88b1aa8012947f6039e0da7ef`. Full deterministic FAR5 scan (farbank.cpp blob `30cac1862b3b88d7ba596b359a9dc8503163593d`) gives 23205 hits, output SHA256 `d0ffded0f50f307101e1c354ccc1643d844cb509c9e48578e1c7021d159666ed`.

## Source-accepted two-child reduction

`Raw56E1LECut.lean` closes ten immediate translated-cycle choices and proves `sound14`: every compatible completion has weighted bound 7014 or lies in one of fourteen literal residual children. The E0=0RB and E0=0RC children are now complete source-accepted Covers at the same bound. Workflow run [46048213225](https://github.com/FlareZ123/bb6/actions/runs/46048213225) replayed both exact searches under Lean 4.36.0-rc2 and then accepted `BB6.Agent1Raw56E1LE.sound12_closed`, reducing the conditional child frontier from fourteen to twelve. The final artifact is `raw56-le-two-source-accepted`, ID **15224286798**, SHA-256 `aedec75e4a70d9865e23d128b3eded72382e445ad60d14a5a690f5fb14471a62`.

This is **not** a complete E1=0LE Cover and does not remove Raw56 from any global roster. The remaining twelve E0 children are still proof obligations.

## Remaining candidate inventory

`inventory-79.json.gz.b64` stores 959 further FAR witnesses, 2161 finite abstraction parameters (129 distinct parameter groups), 89 late query/cycle certificates, and the 79 remaining global zero-based DFS indices. Uncompressed SHA256 `869a651cebab0b5eda351eb783438e7040237b3412747f3ac6265629b840da6f`. In `fmore` and `abs`, each row contains the exact witness/parameter followed by delta-coded sorted global leaf IDs. Every original open index is covered once by FAR5, fmore, abs, late, sat, or remaining.

One two-hole machine, global leaf 23011, first queries F0 at 1202. Expanding it gives three last-hole branches, one cycle, nineteen FAR candidates and one difficult child (E0=1RC, F0=1RA); that expanded child is not covered by the inventory. The remaining subfamilies also contain late queries, with a maximum observed query of 246741, so a complete E1=0LE theorem must use a larger weighted bound than 7014 unless those late branches are proved nonhalting independently. Simulation and candidate coverage alone are not proofs.

## Reproduction

`prepare_le.py` deterministically regenerates the accepted E0=0RB and E0=0RC cuts and candidate certificates without rerunning the other children: from repository root, run `python im-results/agent1-raw56/le/prepare_le.py /tmp/le-gen 0RB 0RC`. `le_delta.py` links the exact accepted Raw56 root/common dependency closures, compiles each child independently, and composes `Raw56E1LETwoClosed.lean`. The search layer is untrusted; the universal claims come from the kernel-checked original canonical checker and the final standard-axiom Lean theorems.
