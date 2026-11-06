# Exact certified/open frontier accounting for six-state two-symbol BB

**Agent 4, updated 2026-11-06.** Research infrastructure and reproducibility report, `im-results/` only. The value of BB(6) remains open; the branch below is a partial source-certified coverage example, not a newly resolved holdout, maximum bound or champion.

## Authenticated base and main statements

The theorem vocabulary is Agent 8's unmodified `BB6Coverage.Machine` and `PartialMachine` in `im-results/agent8-coverage-contract/Frontier.lean`, with exactly 12 state/symbol slots and 25 genuine transition outcomes at each slot. An outer `none` is unassigned while `some none` is an assigned halt. A closed certificate has type `Cover (DecidedBelow B) p`. The original source chain was compiled in [manual CI run 41523806758](https://github.com/FlareZ123/bb6/actions/runs/41523806758) and subsequently in [run 41524640780](https://github.com/FlareZ123/bb6/actions/runs/41524640780), using Lean 4.36.0-rc2. The latter also compiled the exact full-tape relative/absolute bridge `RelativeTape.lean`.

- `FrontierAudit.lean` separates `certified p (Cover good p)`, `unresolved p`, and an all-25-actions `branch p slot` requiring an actually unassigned slot. `FrontierAudit.exhaustive` proves that every compatible concrete table is either certified or resides in its selected unresolved subtree.
- `FrontierMass.lean` defines the exact whole-table mass `cylinderMass p = 25 ^ freeSlotCount p`, including assignments to halt. `freeSlotCount_refine` proves one genuine input slot becomes fixed at each refinement. The **universal** theorem `FrontierAudit.report_conserves` gives `report.1 + report.2 = cylinderMass p` for every finite proof-carrying audit tree. Pair components are total certified and open masses; they are sums over *disjoint* terminal cylinders because each node branches on a previously free slot with unique outcome.
- `FrontierClose.lean` proves `FrontierAudit.open_implies_mass` (any compatible unresolved leaf has strictly positive open mass) and `FrontierAudit.complete_of_zero` (zero open mass yields an authentic `Cover good p`). The zero test is a proof-completeness condition, never a heuristic assumption.
- `FrontierAuditSearch.lean` combines the true original `finiteDecisionOracle` with an all-25-choices recursive search. True oracle outcomes insert the original fully proved `Cover`; false oracle outcomes either recurse or remain explicitly unresolved. `auditSearch_conserves` and `auditSearch_exhaustive` establish sound frontier accounting for every depth and all bounds. A failed oracle is **not** a nonhalting claim.

## Two concrete source-certified benchmarks

`FrontierAuditExample.lean` branches at the blank initial A/0 input slot. The genuine terminal halt and two blank-drift instructions are source-certified. **Exactly three first-slot outcomes are certified** and **22 first-slot outcomes remain open**:
```
certified = 3 * 25^11
open      = 22 * 25^11
total     = 25^12
```
The theorem also identifies exactly which raw initial instructions remain open. These three proven families are elementary and previously recognized by Agent8; no historic holdout disposition follows.

`FrontierAuditBench.lean` applies the *executable* search to Agent8's real `oneHoleUniversalTable`, with `bound=2`, `rayLimit=0`, and `depth=1`. The original `finiteDecisionOracle` certifies all 25 A/0 children. The new `oneHoleAuditedSearch_no_open` proves open mass zero; `oneHoleAuditedSearch_cover` obtains an original `Cover (DecidedBelow 2)` from it; all **25^7** compatible full tables are accounted for. This is a small reproducible completeness test for a specially constructed cylinder, not an exhaustive BB6 search.

## An authentic-root and exact-score branch in the global table frontier (6 November 2026)

`AuthenticTurnBranchAudit.lean` constructs one `FrontierAudit (DecidedBelow 2) emptyTable` from three pairwise-disjoint certified cylinders.

**1. Authentic historical root.** The base audit is `BB6.F287.globalAudit 2`. Its complete 12-slot table is the F287 A6 machine
`1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---`, listed in the 663-root snapshot at `resources/BB6_holdouts_663_2026-10-16.txt:363`. `CryptidsF287.lean` imports the original upstream A6 machine and proves the canonical table equality; `CryptidsF287Global.lean` converts the upstream `original_never` theorem into a `Cover` leaf. The upstream source is pinned at `c86f15861709b76042998c5211c7b2f83991621b`. This is an existing source-authenticated nonhalting root, not a new holdout discovery.

**2. Exact-score halting cylinder.** A/0 = `0RB`, B/0 = halt. Every compatible complete table makes one ordinary move from A to B and then halts on the B/0 query. `twoStepHalt_exact_score` proves `HaltsAfter m 1`; since the Busy Beaver score includes the final attempted halting transition, the exact score is **2**. Ten slots are free, so the cylinder has exactly `25^10` completions.

**3. Nonhalting turning cylinder.** A/0 = `0RB`, B/0 = `1LC`, C/0 = `1LC). The machine moves right once, turns left in B, and then repeatedly enters fresh blank cells in state C while moving left. `turnTable_never` proves all compatible completions never halt. Nine slots are free, so this cylinder has exactly `25^9` completions.

The F287 root is disjoint from both A/0 = 0RB cylinders because its source-verified A/0 action is 1RB. The two latter cylinders are disjoint because their B/0 actions differ. The three cylinders therefore contain exactly `1 + 25^9 + 25^10` distinct complete tables. Every other branch remains open. `authenticTurnBranchAudit_exhaustive` gives a certified-or-open disposition for every one of the `25^12` canonical tables; `authenticTurnBranchAudit_mass` proves that certified plus open terminal mass is exactly `25^12`.

**Verification and source semantics.** The exact-score and turning-cylinder audit compiled under Lean 4.36.0-rc2 in [CI 42256263057](https://github.com/FlareZ123/bb6/actions/runs/42256263057). The combined F287 root and global branch compiled against the unmodified pinned Cryptids source under Lean 4.35.0-rc4 in [CI 42260217683](https://github.com/FlareZ123/bb6/actions/runs/42260217683). Axiom output for the final named theorems contains only `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`. The complete-tape and attempted-halt equivalence between the canonical Agent 8 model and Agent 13 raw six-state semantics is separately source-verified in [CI 41488773370](https://github.com/FlareZ123/bb6/actions/runs/41488773370).

This is a concrete partial global branch with a genuine historic source root and an exact-score halting leaf. It does **not** close the remaining 25^12 search: the overwhelming majority of the frontier remains open, the two synthetic cylinders are elementary, and neither a champion score nor a universal upper bound is proved.

## Semantic bridge and authenticated-root integration attempt

`RelativeTape.lean` is independently source-certified: a relative tape consisting of a current symbol and two infinite Boolean streams is mapped to Agent8's absolute `Int → Bool` tape, preserving every cell, current state, head coordinate, ordinary step, blank initial configuration and halting/no-successor semantics.

`CryptidsTapeAdapter.lean` proposes a further simulation from pinned Google DeepMind Cryptids' `ConjectureMachines.Machine 6 2` and Mathlib-relative half-tape into the local absolute model. `CryptidsF287.lean` attempts to import upstream already-proven A6/F287 blank-root nonhalting theorem, validate the 12 literal RLE actions, and build a genuine complete singleton `Cover` for `1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---`. The complete external-source chain **passed** in [run 41528774972](https://github.com/FlareZ123/bb6/actions/runs/41528774972): source-pinned Cryptids A6, source-aware quotient half-tape adapter, all-run/blank-run equivalence, exact all-twelve-input-table equality, `literal_never` and `root_cover`. The final printed axiom sets for `not_halts_to_agent8`, `original_eq_expectedRLE`, `original_never`, `literal_never` and `root_cover` are `[propext, Classical.choice, Quot.sound]` only. The initial two CI attempts hit path and half-tape representation issues; both were corrected before the successful source-level run. The upstream original `not_halts` theorem is established *prior work*, not a novel holdout decision.

The rooted singleton has mass one. Even with this authenticated leaf, an exhaustive proof over the completely unassigned global table remains far beyond the example. The source-root bridge is orthogonal to global enumeration completeness, the remaining machines, and champion maximality.

## Reproduction

The targeted canonical-branch workflow `.github/workflows/agent4-turn-branch-audit.yml` passed as [run 42256263057](https://github.com/FlareZ123/bb6/actions/runs/42256263057). The combined source-authentic workflow `.github/workflows/agent4-authentic-turn-branch.yml` passed as [run 42260217683](https://github.com/FlareZ123/bb6/actions/runs/42260217683): it rebuilds the pinned Cryptids source and checks the F287 root, all ray/finite-halt dependencies, and the combined audit under Lean 4.35.0-rc4. The broader manually dispatched workflow `.github/workflows/agent4-p1-cone2398.yml` checks:
1. all original Agent8 source files and `FrontierAudit`, `FrontierMass`, `FrontierClose`;
2. `FrontierAuditExample`, `FrontierAuditSearch` and `FrontierAuditBench` using the original decider dependency chain;
3. `RelativeTape`; and
4. in a separate job, upstream-pinned Cryptids theorem with matching original mathlib version plus the complete original-root adapter.

There are no per-commit CI triggers. The verification contract is compile all original dependencies without mocks; printed axiom lists for final named theorems should contain only ordinary Lean axioms, never `sorryAx`. Source-level source imports matter more than local signature-compatible mock compilation.


## Concrete complete/disjoint terminal manifests

Three further modules strengthen the abstract report into an independently inspectable leaf list. `FrontierExtract.lean` emits an explicit `AuditTerminal` per leaf containing the full sequence of split-slot/transition choices, certified/open flag and exact arbitrary-precision cylinder weight. `FrontierAudit.has_actual_terminal` proves that every compatible original machine has a leaf whose entire path matches its transition table. `FrontierUnique.lean` proves `FrontierAudit.unique_actual_terminal`: that manifest leaf is **unique**, formally excluding overlap across the actual list of terminal records. `FrontierManifestMass.lean` proves both certified and unresolved manifest-weight sums agree exactly with the original proof-carrying `report` coordinates and hence with `cylinderMass`. No unverified JSON/JavaScript preprocessing is involved.

`SingletonFrontier.lean` is a generic proof construction: given an existing, authentic `good original` proof for *one complete 12-cell machine*, it creates a global `FrontierAudit good emptyTable` branching over every actual input slot, inserting that one authentic certified root and recording all other branches as open. It does not assert additional undecided roots have been classified. The full-source audit of these newer modules **passed** in the original-source `lean-check` job of [run 41528774972](https://github.com/FlareZ123/bb6/actions/runs/41528774972).

`CryptidsF287Global.lean` composes this generic insertion with the pinned external Cryptids A6/F287 nonhalting proof; its verified `globalAudit` covers every raw total table while identifying one previously known, externally proven original root. The `CryptidsF287` cross-library theorem and provenance are source-verified in run 41528774972. The final `CryptidsF287Global.lean` global integration also **passed** the complete upstream-pinned source check in [run 41529738637](https://github.com/FlareZ123/bb6/actions/runs/41529738637), with both jobs successful. `globalAudit_exhaustive` and `globalAudit_mass` require only the standard `[propext, Classical.choice, Quot.sound]` axioms and no `sorryAx`. See the stronger `globalAudit_mass` theorem for the exact `25^12` global accounting claim.


**Lean toolchain boundary.** The local reusable frontier modules are originally checked under the shared repository's Lean **4.36.0-rc2** toolchain. The external Cryptids A6 proof is pinned to upstream Lean **4.35.0-rc4** and Mathlib. The independent source-level A6 job copies the *unchanged source files* of Agent8 and this bridge into the upstream checkout and rechecks every theorem in the upstream **4.35** kernel. Lean `.olean` artifacts are toolchain-specific; they cannot simply be imported from this upstream job into an ordinary 4.36 build. To directly consume the A6 root proof, rebuild these source modules in the pinned upstream environment, or separately re-verify a genuine 4.36 port of the upstream A6 dependencies. The current repository-level certification is an authenticated **source-level 4.35 proof**, with the generic frontier logic separately verified in 4.36.

**CI cost control:** After the successful full source run 41529738637, the manually dispatched `.github/workflows/agent4-p1-cone2398.yml` received an optional boolean `verify_cryptids` input, default `false`. Ordinary P1/frontier checks now avoid repeatedly rebuilding the full expensive upstream Cryptids proof. Select `verify_cryptids = true` when rechecking the original A6 global-source bridge. The already successful pinned full source job remains preserved in run 41529738637.
