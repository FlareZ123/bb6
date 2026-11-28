# F421: one-hole Raw139 holdout

The standard blank-start table is `1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---`, initial state A, sole unassigned F1. The canonical representative in `im-results/agent8-coverage-contract/LedgerTextRows.lean` has order FDAEBC, root C, no reflection. This is the open E0=1LD,A1=0LC branch of Raw139.

## Blank-start result

`blankFirstSecondaryZero` in [F421FirstSeed.lean](F421FirstSeed.lean) proves that every completion of F1 reaches the all-clear secondary frontier from the authentic blank tape. The proof follows the first secondary seed at odd macro 190, then completes 32,750 guarded secondary cycles to odd macro 65,690. Its exact endpoint is specified symbolically by `sIter` and `sTailFinal`. The theorem certifies at least 13,628,275,276 primitive transitions. The return edges use exact primitive costs and the multi-return drains contribute a conservative macro-count lower bound.

The proof starts with a literal 24-step trace. A compressed certificate checks 622 individual frontier returns and 304 source-proved drains on the next segment. Partial drains across a near prefix bypass the isolated nonterminal-deletion obstruction without expanding the long carry skip. Lean checks the full word before and after each edge in a run-length encoding, including the terminal symbols and untouched suffix. The 1,024 explicit blank pairs used by the finite certificate preserve the original tape by `embedPad`. The certified seed matches all ten primary cells, all fifteen secondary cells, and the suffix before applying the existing exact secondary theorem.

## Kernel-checked secondary lifetime quotient (2026-11-28)

The exact primary successor `sNext` admits a smaller P-coordinate recurrence, independent of Q-run values. For a far-to-near normalized list of positive lifetimes `ls`, one step deletes `l=1` entries, replaces each surviving `l` by `(l-1)*2^d`, where `d` counts earlier deletions, and appends `2^(d+1)` for the total number of deletions. Define the weighted mass recursively by `mass []=0`, `mass (l::ls)=l+2*mass ls`. The exact arithmetic theorem is `mass (advance ls)=mass ls+2^ls.length+1` for positive lists.

[**F421SecondaryLifetimes.lean**](F421SecondaryLifetimes.lean) proves the arithmetic and the exact physical P-run projection of all-marked drains; [**F421SourceLifetimeBridge.lean**](F421SourceLifetimeBridge.lean) connects this projection to the original `F421TertiaryGuard.drain` without assumptions on Q values. Original-source Lean CI [46086128496](https://github.com/FlareZ123/bb6/actions/runs/46086128496) **passed**, with no sorry or native_decide. [**F421SecondaryPSource.lean**](F421SecondaryPSource.lean) proves the exact `sNext` P-coordinate successor under two protected far runs. [**F421SecondaryLifeIter.lean**](F421SecondaryLifeIter.lean) composes the quotient through any finite countdown and instantiates the real seed, proving `firstSecondaryP`: the 32,750-cycle `sIter` endpoint has far P runs 2,818,045 and 6,946,811 followed by `physicalP 4 (lifeIter 32750 [327661,14,30,6,22,14,1,2])`. Original-source CI [46086481156](https://github.com/FlareZ123/bb6/actions/runs/46086481156) **passed**.

This is an exact source-linked P-profile, **not** a certified numeric 8,217-cell endpoint, source proof of the secondary-zero-to-tertiary boundary, nonhalting proof, or BB(6) maximality result. The finite Python lifetime iterator yields 8,215 head cells, consistent with the previously independent arithmetic checkpoint, but a compact kernel certificate for that length is still needed.

## Remaining machine decision

The first zero frontier is now connected to the blank tape. Its crossing into the odd-65,700 tertiary seed remains established by arithmetic computation in [BoundaryEpoch.md](BoundaryEpoch.md). The tertiary countdown and zero-crossing theorems are source-proved for any seed satisfying their guards, but their application to the current blank-start theorem still needs that crossing. The next secondary primary guard after the tertiary zero also remains open. [PrimaryEvents.md](PrimaryEvents.md) computes 198 far Q entries at the end of the tertiary countdown and verifies the budget for the 197 corresponding known P runs.

## Reproduction and dependencies

- `frontier_map.py`: exact bit-word formula, compared against 1000 primitive returns (711352 steps).
- `compressed.cpp`, `carry.cpp`, `test_compressed.py`: strict carry skip, 10^18 macros and exact primitive count 2741467853641781568730607840197912170.
- `boundary.py`: arbitrary-precision whole-drain and secondary arithmetic; 10^50-macro exact safe prefix and odd-5000 primitive cost recorded in BoundaryEpoch.md.
- `prefix.cpp`, `fast_prefix.cpp`, `cross_zero.py`, `verify_tertiary.py`: autonomous prefix recurrence, byte-identical secondary-zero checkpoint, new tertiary seed and exact-cycle checks.
- `F421Frontier.lean`, `F421Regular.lean`, `F421Drain.lean`, `F421Odd.lean`, `PrimaryGuard.lean`, `TertiaryGuard.lean`: frontier, regular-budget and arithmetic proofs; distinguish local copied-model checks from original-source closure. [GeneralDrain.md](GeneralDrain.md) gives the arbitrary terminal-deletion drain theorem, now used by the source-level tertiary epoch.
- `F421DrainPlan.lean`, `F421GeneralDrain.lean`: generic mixed-marker drain with zero-P ghosts and arbitrary terminal deletions; local plan proof accepted; `F421MergedDrain.lean` proves normalized merging and connects the arithmetic drain to its word endpoint. [CI 45961519738](https://github.com/FlareZ123/bb6/actions/runs/45961519738) checked the earlier original-source closure.
- `tertiary_zero.py`, `TertiaryHead.lean`: exact conditional zero-crossing experiments and normalized head arithmetic; the authentic tail is computed but the authentic primary endpoint is not.
- `primary_events.cpp`, `primary_events.py`, `F421PrimaryEvents.lean`: exact far-prefix event skip and checks, with prefix independence and affine skip proofs.
- `state-1b.json`, `state-2b.json`: independent finite primitive checkpoints.
- [FARIncremental.md](FARIncremental.md), `far_incremental.cpp`: exhaustive exclusion of reachable canonical FAR DFA sizes 1–8 in both orientations; larger automata remain open.

### Lean reproduction

The existing `f421-frontier-proof` workflow generates `F421SeedTrace.lean` with `compressed_trace.py` before compiling the closure of `F421FirstSeed.lean`. The original-source closure was built locally with Lean 4.36.0-rc2, and both blank-start theorems report only `propext`, `Classical.choice` and `Quot.sound`. The Python generator supplies witnesses for kernel equality checks.

- [FrontierTransduction.md](FrontierTransduction.md) gives the original D-to-D word return and the bad 111 parse.
- [PrimaryGuard.md](PrimaryGuard.md) gives the mixed P-budget and divisibility invariant used for the secondary epoch. `F421SecondaryExact.lean` establishes the deterministic primary and closed-form tail endpoints.
- [TertiaryEpoch.md](TertiaryEpoch.md) gives the source-proved positive tertiary countdown. [TertiaryZero.md](TertiaryZero.md) gives the source-proved guarded zero crossing into a new secondary epoch.
