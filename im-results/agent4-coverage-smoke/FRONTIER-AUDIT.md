# Exact certified/open frontier accounting for six-state two-symbol BB

**Agent 4, 2026-11-02.** Research infrastructure and reproducibility report, `im-results/` only. The value of BB(6) remains open; there is no newly resolved holdout, maximum bound or champion here.

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

## Semantic bridge and authenticated-root integration attempt

`RelativeTape.lean` is independently source-certified: a relative tape consisting of a current symbol and two infinite Boolean streams is mapped to Agent8's absolute `Int → Bool` tape, preserving every cell, current state, head coordinate, ordinary step, blank initial configuration and halting/no-successor semantics.

`CryptidsTapeAdapter.lean` proposes a further simulation from pinned Google DeepMind Cryptids' `ConjectureMachines.Machine 6 2` and Mathlib-relative half-tape into the local absolute model. `CryptidsF287.lean` attempts to import upstream already-proven A6/F287 blank-root nonhalting theorem, validate the 12 literal RLE actions, and build a genuine complete singleton `Cover` for `1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---`. The direct external-source CI job was dispatched in [run 41525975458](https://github.com/FlareZ123/bb6/actions/runs/41525975458). **Do not treat this Cryptids-to-Agent8 import as certified unless that job actually succeeds against pinned external source commit `c86f15861709b76042998c5211c7b2f83991621b`, or a later run verifies the latest code.** The upstream original `not_halts` theorem is established *prior work*, not a novel holdout decision.

The rooted singleton has mass one. Even with this authenticated leaf, an exhaustive proof over the completely unassigned global table remains far beyond the example. The source-root bridge is orthogonal to global enumeration completeness, the remaining machines, and champion maximality.

## Reproduction

The existing manually dispatched workflow `.github/workflows/agent4-p1-cone2398.yml` checks:
1. all original Agent8 source files and `FrontierAudit`, `FrontierMass`, `FrontierClose`;
2. `FrontierAuditExample`, `FrontierAuditSearch` and `FrontierAuditBench` using the original decider dependency chain;
3. `RelativeTape`; and
4. in a separate job, upstream-pinned Cryptids theorem with matching original mathlib version plus the complete original-root adapter.

There are no per-commit CI triggers. The verification contract is compile all original dependencies without mocks; printed axiom lists for final named theorems should contain only ordinary Lean axioms, never `sorryAx`. Source-level source imports matter more than local signature-compatible mock compilation.


## Concrete complete/disjoint terminal manifests

Three further modules strengthen the abstract report into an independently inspectable leaf list. `FrontierExtract.lean` emits an explicit `AuditTerminal` per leaf containing the full sequence of split-slot/transition choices, certified/open flag and exact arbitrary-precision cylinder weight. `FrontierAudit.has_actual_terminal` proves that every compatible original machine has a leaf whose entire path matches its transition table. `FrontierUnique.lean` proves `FrontierAudit.unique_actual_terminal`: that manifest leaf is **unique**, formally excluding overlap across the actual list of terminal records. `FrontierManifestMass.lean` proves both certified and unresolved manifest-weight sums agree exactly with the original proof-carrying `report` coordinates and hence with `cylinderMass`. No unverified JSON/JavaScript preprocessing is involved.

`SingletonFrontier.lean` is a generic proof construction: given an existing, authentic `good original` proof for *one complete 12-cell machine*, it creates a global `FrontierAudit good emptyTable` branching over every actual input slot, inserting that one authentic certified root and recording all other branches as open. It does not assert additional undecided roots have been classified. The full-source audit of these newer modules is included in manual CI [run 41528774972](https://github.com/FlareZ123/bb6/actions/runs/41528774972), with outcome pending at time of this note.

`CryptidsF287Global.lean` composes this generic insertion with the pinned external Cryptids A6/F287 nonhalting proof, so its promised `globalAudit` covers every raw total table while identifying one previously known, externally proven original root. The *new cross-library theorem* and its provenance remain tentative until external source CI succeeds on that file. See the stronger `globalAudit_mass` theorem for the exact `25^12` global accounting claim.
