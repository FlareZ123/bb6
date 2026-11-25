# Raw120 E0=1LF — complete candidate partition, source acceptance pending

Parent `1RB---_1RC---_0RD---_1LD1RE_1LF1LE_------` is one child of raw120's E0 hole, anchored by Raw120CanonicalPartition and Raw120FourHoleFrontierIngestion (the remaining siblings must be preserved). The deterministic first-hole tree accounts for all 25^5 = 9,765,625 raw completions.

- 1763 splits, 26120 cycle leaves, 9966 last-hole leaves, 4464 open leaves.
- Open-list SHA256 b5ca9ab66092d18182df4d2c3bc13763c2a31dac5216705b23a6852373abf077.
- Local candidate discovery: 4421 FAR, 27 one-block, 8 multi-block and 1 longer-period multi-block pump, six custom invariants, one late final query. All 4464 accounted for in the discovery run. The original generator still needs regeneration/compile against the full repository.
- Leaf 2558 `1RB0LA_1RC1RA_0RD---_1LD1RE_1LF1LE_1RA0RB` first queries its sole hole C1 at t=1849 in physical simulation. Candidate weighted bound 1855 includes the final query and at most five blank-prefix steps.

## The six hard leaves

Raw120OneLFCounter.lean: indices 2617/2806/2823/2945, varying A1=0LD/0RD/0RE/1LF, all other rows fixed and C1 unassigned. In state F at a fresh left boundary, right word is 1^(6(a+1)) 0^(3b+2) 1^(c+2). If b>0 return to (a+1,b-1,c) at cost d+18(a+1)+11; otherwise return to (0,2a+1,c+1) at cost d+18(a+1)+22. d=6/8/6/4 respectively. Blank entries t=56/58/56/54, seed (0,0,4). Every phase is an arbitrary-tail exact zipper equality, proved for all natural counters.

Raw120OneLFTwo.lean: index 2549, `1RB0LA_1RC---_0RD0RA_1LD1RE_1LF1LE_1RA0LF`. At F left boundary the word is 1^(6(a+1)) 0^(2b+1) 1^(c+2). Return (a+1,b-1,c) at cost 18(a+1)+24 for b>0, otherwise (0,3a+2,c+1) at cost 18(a+1)+35. Blank entry t=63, seed (0,1,3). B1 is never queried.

Raw120OneLFStack.lean: index 2753, `1RB0RC_1RC---_0RD0RE_1LD1RE_1LF1LE_1RA0LF`. Stronger invariant: every finite word with initial one-run length at least five, followed by arbitrary positive zero gaps and one-runs of length at least five, has a positive return in that language at F left boundary. Short gaps push a frame; long gaps or implicit blank terminate descent. Recursive unwinding removes two frames at a time, reconstructing legal runs with minimum length five. Blank entry at t=10. This handles arbitrary stack lengths and arbitrary unary counters, without extrapolating a finite trace.

All three modules compiled locally under Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a), using copied original Z0, move0, step0, run0 and join0 definitions and a proved local zipper-only never_of_growth bridge. No sorryAx; advance axioms propext/Quot.sound; never additionally Classical.choice for the stack theorem. This is local mathematical model checking, not original-source raw-machine acceptance. Original source SweepPumping supplies the raw-machine transfer in repository compilation.

## Reproduction and consuming theorem

```
python im-results/agent13-coverage/unpack.py
python im-results/agent3-tnf-raw120/generate_sibling.py 1LF
python tools/lean_compile_closure.py --workdir /tmp/a3-raw120 --jobs 4 im-results/agent3-tnf-raw120/1lf/Raw120OneLFData.lean
```

Existing manual workflow target `weighted-tnf-raw120-1lf`. Generated theorem `BB6.Agent3Raw120OneLF.allOneLF` is intended to certify every compatible completion at weighted bound 1855. The generator pins table identities, tree statistics and open-list digest and refuses emission on any unmatched leaf. No source-accepted sibling count, parent cover, or global canonical count may change until that source theorem is checked and consumed.

## Other newly enumerated siblings (discovery only)

| E0 | split | cycle | last | open | FAR union |
|---|---:|---:|---:|---:|---:|
| 0LB | 934 | 14635 | 4457 | 2391 | 2326 |
| 0LF | 1932 | 28231 | 11454 | 4752 | 4654 |
| 1LA | 1661 | 24485 | 9483 | 4236 | 4180 |
| 1LB | 1599 | 24218 | 8209 | 4351 | 4295 |
| 1RA | 1329 | 19345 | 6849 | 4374 | 4286 |
| 1RF | 2002 | 31424 | 8212 | 6411 | 6335 |

Every row accounts for 25^5 completions. Candidate discovery used the union of existing ten bank files. No claim of complete symbolic assignment or source acceptance for these six branches.

### Original-source leaf acceptance (2026-11-25 13:48 UTC)

All three new modules were compiled locally with Lean 4.36.0-rc2 against exact repository imports Frontier, Symmetry, RootShift, SparseZipper, SweepPumping. Their Git blob identities were checked against the fetched originals. All six genuine raw-machine `never` theorems passed, with only propext/Quot.sound (plus Classical.choice for the arbitrary-stack theorem). This supersedes the earlier reconstructed-model-only status for the six hard leaf proofs; full sibling source checker still pending.
