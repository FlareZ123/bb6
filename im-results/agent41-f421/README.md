# F421: one-hole Raw139 holdout

The standard blank-start table is `1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---`, initial state A, sole unassigned F1. The canonical representative in `im-results/agent8-coverage-contract/LedgerTextRows.lean` has order FDAEBC, root C, no reflection. This is the open E0=1LD,A1=0LC branch of Raw139.

## Strongest current reduction

[FrontierTransduction.md](FrontierTransduction.md) gives the exact D-to-D word return; F1 is reached precisely on a bad 111 parse. [CarryCountdown.md](CarryCountdown.md) derives the principal two-return phase and strict regular binary countdown. [BoundaryEpoch.md](BoundaryEpoch.md) extends it to complete regular drains with terminal P-run deletion, exact primitive cost, and a secondary binary countdown. [PrimaryGuard.md](PrimaryGuard.md) gives a conditional inductive guard for the secondary phase, including the authentic 32750 decrements from odd 190 to 65690. The secondary-zero crossing creates a different nonterminal-collapse regime.

**Tertiary phase and zero crossing:** [TertiaryEpoch.md](TertiaryEpoch.md) proves the conditional primary guard and the 2^8214−1-cycle tertiary countdown from the authentic odd-65700 seed. [TertiaryZero.md](TertiaryZero.md) now proves the conditional zero crossing for every admissible primary endpoint, yielding a secondary counter with 8215 set bits without computing the enormous primary-head trajectory. The authentic next-tail budgets pass. The normalized autonomous head recurrence and several crossing inequalities are kernel-checked in `TertiaryHead.lean`. [PrimaryEvents.md](PrimaryEvents.md) now gives the exact 198-entry far-Q prefix at the end of that astronomical countdown; 197 known P-runs satisfy the next secondary budget. The uncomputed near-head guard and full original-source composition remain open. No whole-machine decision or BB(6) bound improvement is claimed.

## Reproduction and dependencies

- `frontier_map.py`: exact bit-word formula, compared against 1000 primitive returns (711352 steps).
- `compressed.cpp`, `carry.cpp`, `test_compressed.py`: strict carry skip, 10^18 macros and exact primitive count 2741467853641781568730607840197912170.
- `boundary.py`: arbitrary-precision whole-drain and secondary arithmetic; 10^50-macro exact safe prefix and odd-5000 primitive cost recorded in BoundaryEpoch.md.
- `prefix.cpp`, `fast_prefix.cpp`, `cross_zero.py`, `verify_tertiary.py`: autonomous prefix recurrence, byte-identical secondary-zero checkpoint, new tertiary seed and exact-cycle checks.
- `F421Frontier.lean`, `F421Regular.lean`, `F421Drain.lean`, `F421Odd.lean`, `PrimaryGuard.lean`, `TertiaryGuard.lean`: frontier, regular-budget and arithmetic proofs; distinguish local copied-model checks from original-source closure. [GeneralDrain.md](GeneralDrain.md) gives the arbitrary terminal-deletion drain theorem, now used by the source-level tertiary epoch.
- `F421DrainPlan.lean`, `F421GeneralDrain.lean`: generic mixed-marker drain with zero-P ghosts and arbitrary terminal deletions; local plan proof accepted; `F421MergedDrain.lean` proves normalized merging and connects the arithmetic drain to its word endpoint; source closure audit passed in CI 45961519738.
- `tertiary_zero.py`, `TertiaryHead.lean`: exact conditional zero-crossing experiments and normalized head arithmetic; the authentic tail is computed but the authentic primary endpoint is not.
- `primary_events.cpp`, `primary_events.py`, `F421PrimaryEvents.lean`: exact far-prefix event skip and checks, with prefix independence and affine skip proofs.
- `state-1b.json`, `state-2b.json`: independent finite primitive checkpoints.
- [FARIncremental.md](FARIncremental.md), `far_incremental.cpp`: exhaustive exclusion of reachable canonical FAR DFA sizes 1–8 in both orientations; larger automata remain open.

**Source-level positive tertiary epoch:** `F421Epoch.lean` now proves the full guarded countdown for arbitrary counter value and head size, using source-level exact odd crossings, mixed-marker drain, and the inductive primary and tail guards. The authentic seed is still computational, and the next secondary primary guard and authentic blank-start-to-seed bridge are open. The prior 15-module original closure passed [CI 45961519738](https://github.com/FlareZ123/bb6/actions/runs/45961519738); the new modules were checked locally against its actual artifact.

**Source-level zero crossing:** `F421ZeroWords.lean` and `F421ZeroGuard.lean` prove `tertiaryToSecondary`, covering the full guarded tertiary countdown and conversion to secondary form with one spare primary budget unit. All proofs checked locally against the genuine source closure; the authentic seed meets the strengthened numerical guard. The next primary guard and authentic blank-to-seed bridge are still open.

**Source-level secondary epoch:** `F421SecondaryWords/Cycle/Guard/Induction/Epoch.lean` prove the full positive secondary countdown for a pointwise mixed P-budget/divisibility guard, allowing leading b≥3M−1. `firstSecondaryEpoch` instantiates the recorded odd-190 seed for 32750 positive cycles. The actual blank-to-odd190 bridge and the secondary-zero-to-tertiary exact boundary remain to be certified. The new guard covers all 197 known endpoint P-runs but not yet the uncomputed near head after the huge tertiary epoch.

`F421SecondaryExact.lean` now exposes the exact full secondary endpoint, with deterministic `sIter` for primary cells and closed-form `sTailFinal` for tail cells.
