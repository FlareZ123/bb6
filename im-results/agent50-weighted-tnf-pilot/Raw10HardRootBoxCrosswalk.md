# Raw10 hard-root to residual-box crosswalk

**Status:** intermediate computational crosswalk, not a new Lean theorem or a parent closure.

## Why this exists

The hard-root crosswalk in `agent19-hard-root-crosswalk/HardRootLeaves.lean` maps several difficult literal machines into the B0=1LC parent. The raw10 consumer has since accumulated 68 certified cylinders and an exact 41-box complement. Parent membership alone does not identify which open residual obligations contain those root leaves. This audit computes that missing link.

Run from the repository root:

```sh
node im-results/agent50-weighted-tnf-pilot/raw10-hardroot-crosswalk.js
```

The script reads the actual Lean literal tables, the 66 encoded side/held rows, and the two raw10 cycle/halt tables. It reproduces the first-mismatch `subtractMany` algorithm from `agent49-box-complement/BoxComplement.lean`, with the same order as `Raw10BoxCombinedConsumer.lean`. It checks that the computed complement has the existing Lean count and mass before reporting root containment.

## Exact output

The source inputs give 68 certified cylinders (65 side witnesses, the q_i(2800,100) held leaf, the 24+14 cycle leaf, and the forced-halt leaf). The replay reproduces:

- residual boxes: **41**
- residual mass: **90,737,503,713,725**
- parent: A0=1RB, B0=1LC

The one-hole leaves of four roots are wholly contained in these residual boxes:

| Root | Sole halt slot | Residual box | Leaf size |
|---|---|---:|---:|
| C | F0 | 0 | 25 |
| D0 | F1 | 0 | 25 |
| D2 | F1 | 0 | 25 |
| r1 | D1 | 24 | 25 |

“Wholly contained” is stronger than saying the particular halt completion belongs to the box: every fixed instruction of the one-hole leaf is admitted by the box, and the hole coordinate has all 25 transitions available. Thus the complete 25-machine leaf is inside that residual box and is disjoint from all 68 earlier cylinders.

For reproducibility, the two containing box domain-size vectors (slot order A0,A1,B0,B1,C0,C1,D0,D1,E0,E1,F0,F1) are:

- box 0: `[1,23,1,25,25,23,25,25,25,25,25,25]`
- box 24: `[1,18,1,1,1,1,1,25,1,1,13,25]`

The source file `HardRootLeaves.lean` gives the exact literal rows. The script's full output includes the actual domains and encoded leaf cubes.

## The immediately consumable root

The r1 table is the first of the six source-accepted nonhalting roots in `agent42-cryptids-current-main/Cryptids608NonHalt.lean`:

`1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF`.

Its upstream source is pinned to `google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a`. The local source-graft audit passed in [run 45178351479](https://github.com/FlareZ123/bb6/actions/runs/45178351479), including the transitive axiom audit; the transferred theorem is `Cryptids608.literal_r1_never`.

Erasing r1's sole halt row D1 yields the 25-completion leaf in residual box 24. The source theorem proves the halt completion never halts. The other 24 completions have an ordinary transition at D1 and ordinary transitions everywhere else, so `all_ordinary_never` proves they never halt as well. Consequently this leaf has `Cover (WeightedBound B)` for every B; the delay surcharge is irrelevant once nonhalting is established.

Adding this leaf to the 68-certificate list and rerunning the exact partition gives:

- residual boxes: **43** (the containing box splits into three first-mismatch pieces)
- residual mass: **90,737,503,713,700**
- mass removed: **25**

The count increases by two because box 24 is larger than the leaf. This is not a defect: the exact uncovered complement is retained. A conditional consumer can instead keep the 41-box list and handle the r1-compatible part of box 24 with the source theorem, leaving only the complement of that leaf as the open obligation.

## Remaining roots concentrated in box 0

C, D0 and D2 all lie in box 0, and their complete one-hole leaves are contained there. Their exact downstream conditions are already expressed in `HardRootLeaves.lean`:

- C: every `HaltsAfter C k` must satisfy `k+1 ≤ B`.
- D0: every `HaltsAfter D0 k` must satisfy `k+1 ≤ B`.
- D2: every `HaltsAfter D2 k` must satisfy `k+2 ≤ B` (one unit of delay surcharge).

These are not resolved by this crosswalk. C still needs its joint reachability gate or a score-B halting bound; D0 and D2 have distinct root seeds. The crosswalk identifies box 0 as the exact place where those root-level decisions can be consumed, rather than treating them as unrelated searches.

## Scope and next integration

This is a finite source-data audit plus an executable reproduction of the existing box subtraction. It is **not** a Lean proof that r1's leaf is covered, and it does not close the B0=1LC parent. The next small Lean integration is to import the accepted r1 nonhalting theorem, prove `Cover (WeightedBound B) (forgetHaltRows r1)`, and feed that leaf into the existing raw10 remainder consumer while preserving the complement of box 24. The C/D0/D2 leaf obligations should be exposed against box 0 with their exact delay corrections.

Do not move this artifact into `results/`: it is useful intermediate infrastructure, not yet a publishable mathematical result.
