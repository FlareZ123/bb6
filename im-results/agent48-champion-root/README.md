# Six-step rooted-runtime equivalence for the published BB(6) champion family

**Agent 48; 2026-11-03. Status: kernel-checked intermediate bridge.** This does not compute BB(6), import the Rocq halting result into Lean, or improve a published lower bound. It resolves a concrete root-identity and step-convention issue that would otherwise permit unsound use of an external proof.

## Exact source and statement

The historical six-state champion candidate in the [Busy Beaver Wiki](https://wiki.bbchallenge.org/wiki/1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE) has transition table

```text
1RB1RA_1RC---_1LD0RF_1RA0LE_0LD1RC_1RA0RE
```

for the 12 **ordinary transition/halting-query** table slots. Its wiki `1RZ` terminal action is mapped to `---` in the local raw semantics. Both end on the same final query and have identical Busy Beaver step counts; the final written-one count of the terminal action differs.

The cited [published Rocq machine source, revision `3f302b87...`](https://github.com/ccz181078/busycoq/blob/3f302b87f5fb933c46e97672ffbb6907f373fb6e/verify/SOBCv5.v#L10750-L11283) defines **TM63** in `verify/SOBCv5.v:10750` with literal table:

```text
1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD
```

and proves `TM63.halt : halts tm c0` near line 11249. The separate published TM62 source at line 10212 has another root of the same unrooted family. A state permutation that maps champion letters `ABCDEF` to TM63 letters `EABCDF` sends champion blank root A to **TM63 root E**, *rather than* TM63's source-proved blank root A. The root distinction matters: an arbitrary state relabeling of the same table does not preserve the distinguished starting state unless the root is explicitly transported.

The original-source Lean file [ChampionRootBridge.lean](ChampionRootBridge.lean) proves:

- `champion_renamed`: literal equality `renameTable championPerm championTable = tm2`, using all twelve transition slots.
- `join_source`: equality of **complete, bi-infinite raw-tape configurations** `run tm2 15 (blankAt 4) = run tm2 9 blank`. The two finite exact configurations are `state E, head +3, ones {-2,-1,0,+2}`.
- `all_join`: this coincidence remains exact for every continuation index `n`.
- `champion_halts_offset`: `HaltsAfter championTable (15+n) ↔ HaltsAfter tm2 (9+n)` for **every** `n : Nat`.
- `champion_halts_iff_tm2`: `(∃ n, HaltsAfter championTable n) ↔ (∃ n, HaltsAfter tm2 n)`. Explicit proven 15-step champion and 9-step TM63 live prefixes exclude missed earlier stops.
  
The Lean proof implements a finite marked-cell interpreter and proves its **exact functional embedding** into the unchanged original `BB6Coverage.Config` with `Int → Bool` tape. The decisive 9/15 transition witness is kernel-evaluated by `decide`; all-time transport uses the original `run_append`, `run_none_add` and `rename_haltsAt_iff` proofs. No proof about an arbitrary finite simulation is treated as if it were an all-time result.

## Validation

**[Manual GitHub Actions run 41562388566, job 125675776442](https://github.com/FlareZ123/bb6/actions/runs/41562388566/job/125675776442): SUCCESS**, at source revision `490e4f53174f91810e405c434b18d67769cf9ca5`; Lean 4.36.0-rc2. The isolated job compiles the unmodified original `Frontier.lean`, `Symmetry.lean`, `RootShift.lean`, then our source-dependent `ChampionRootBridge.lean`. Original action: [agent48-champion-root.yml](../../.github/workflows/agent48-champion-root.yml), manual dispatch only.

Actual job logs print the five final theorem axiom sets as subsets of `[propext, Classical.choice, Quot.sound]`, with **no `sorryAx`**. Two unused-`simp` warnings are harmless proof-style warnings.

## Significance and remaining proof contract

The source-connected Lean theorem **conditionally transports** any exact TM63 A-root stop time `9+n` to the champion A-root time `15+n`. It also proves both roots halt or both do not, without imposing a result in advance. It verifies a concrete same-table/different-root case in a historically significant four-root family.

The original Rocq proof already asserts termination of TM63; this independent local Lean source **does not import the Rocq `TM63.halt` theorem or prove its cross-assistant semantic equivalence**. Therefore this repository cannot infer an unconditional champion witness from `champion_halts_iff_tm2` alone. To connect the original Rocq theorem to `BB6Coverage.Attainable`, either source-verify a Coq→Lean semantic bridge or check a witness in Lean with an appropriately justified acceleration. For a **numerical** attained Busy Beaver score, prove an exact `HaltsAfter ... n` statement, not only the existential termination theorem.

Even such a lower-bound witness would not supply the missing **global upper-bound certificate** for the two first-instruction cylinders defined by Agent 42. There is no new solved holdout and no evidence this familiar root-shift observation is independent publishable novelty, so this work belongs under `im-results/`.

### Next genuinely discriminating work

- Recover a machine-specific exact primitive-step witness (not merely existence) from a pinned formally verified source, and establish the source semantics/step convention.
- Independently close a **currently unsolved rooted case** or a nontrivial subset of one of the two universal machine cylinders.
- Audit the current external champion-family history before calling this bridge a new research finding; the wiki had already noted post-prefix equivalence of TM1 and TM2.
