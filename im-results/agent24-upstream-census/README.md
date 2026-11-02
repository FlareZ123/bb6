# Upstream Cryptids BB(6) rooted-source crosswalk

**Intermediate source-coverage inventory, Agent 24, 2026-11-02.** The [89-row pinned CSV](./upstream-coverage.csv) joins two upstream Lean source catalogues to the [2026-10-16 historic rooted holdout ledger](../holdout-family-coverage/2026-10-16-rooted-ledger.csv).

## Pinned evidence

Upstream revision [google-deepmind/cryptids@`c86f15861709b76042998c5211c7b2f83991621b`](https://github.com/google-deepmind/cryptids/tree/c86f15861709b76042998c5211c7b2f83991621b).

- [Core BB6 source table](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/README.md), Git blob `9a0937737beb80a8f4bdbfc9c4741a9872407ee5`: **54 distinct** rooted machines, including one explicit `IsNotHalt` theorem (A6) and 53 original-machine reduction entries.
- [Stack/odometer/transducer acceleration table](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Accelerations/README.md), Git blob `42268d7f921949cd03284f3197ac5f82717032fa`: **35 distinct** rooted machines, including 15 structural and 20 acceleration-problem modules.
- [Historic local rooted catalogue](../../resources/BB6_holdouts_663_2026-10-16.txt) and [rooted family ledger](../holdout-family-coverage/2026-10-16-rooted-ledger.csv), CSV blob `33978fa81bb6387ee07bd2a66c2fcca8eedadaf6`: **663** unique roots in the **2026-10-16 snapshot**.

## Crosswalk result

**All 89 upstream roots are distinct. Exactly 86 are verbatim rooted-RLE matches to the dated 663**, consisting of 51/54 from the core list and 35/35 from the acceleration list. The other **three** source-listed roots do not occur in that historic snapshot:

1. `1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_---1RE`, a core README entry explicitly referring to an external nonhalting proof.
2. `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC`, a core entry with a documented machine-level halting equivalence to an alternate rooted table.
3. `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`, a separate core source module; inspect its upstream statement before assigning a status.

The historic catalogue has **577** rooted entries with no *verbatim* table entry in these two upstream READMEs. Their current halting status is **unknown to this audit**, and they may have other documented reductions or decisions.

## Validity and limits

The crosswalk extracts original-root RLE, upstream subgroup, displayed Lean property, relative module path, canonical historic start, and source revision. Source properties are **README attestations**; this audit does not independently rebuild 89 Lean modules. Except for the explicitly proved A6 nonhalt, these are *formalizations and reductions*, with no implication that halting/nonhalting has been decided. The repository has independent original-source proof bridges for selected local machines.

No outcome is inferred for an alternate initial state merely because its transition table is isomorphic under renaming/reflection. A *rooted* start-state-specific blank-entry proof is necessary.

This is a reusable BB(6)-wide source index. It is **not** a newly proved BB(6) mathematical result and belongs in `im-results/`. The CSV is dated against an immutable upstream commit. To refresh, re-extract the two upstream table sections and rejoin exact RLEs against a separately dated holdout snapshot.

## Research payoff

Before rederiving a six-state machine acceleration, search [the pinned crosswalk](./upstream-coverage.csv) by the exact rooted RLE and inspect its source module at the pinned upstream commit. Separately validate kernel axioms and blank-start semantic equivalence. Add independently verified halting decisions only after a full original-root proof. Avoid counting source reductions as resolved holdouts.
