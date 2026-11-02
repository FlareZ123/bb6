# Agent 8: formally checked sparse-enumeration coverage contract

**Status: intermediate proof infrastructure only. No BB(6) value, global upper bound, newly decided holdout, or academically new theorem is claimed.** Date: 2026-11-02.

## Local theorem and its precise meaning

[`Frontier.lean`](./Frontier.lean) is a standalone Lean 4.36.0-rc2 module, compiled locally with no `sorry` and no extra axioms. It deliberately separates three types:

- `Machine = (Fin 6 × Bool) → Option Move`. An `Option.none` here is an actual halting transition. There are 24 nonhalting possibilities (2 writes × 2 directions × 6 successor states), plus one halt outcome.
- `PartialMachine = (Fin 6 × Bool) → Option (Option Move)`. Its **outer** `none` means not yet assigned by a sparse enumerator; `some none` means already assigned to halt.
- `Cover good p` is a proof object requiring either a **proved leaf for all compatible machines**, or 25 independently proved children at an unassigned slot. It has no constructor for an unverified pruning or catalogue assumption.

Formal checks:

1. `choices_length` proves there are exactly 25 branch outcomes; `choices_complete`, `child_cover`, and `child_exact` prove every compatible full table belongs to the appropriate unique branch.
2. `common_prefix_of_partial_table` and `first_hole_branch` prove all completions agree on a known finite trace prefix, so expanding the first genuinely unassigned transition does not lose a possible continuation.
3. `Cover.sound` and `global_coverage` prove an actually completed coverage tree over the completely unassigned table entails the desired predicate for **every** table represented by this six-state model.
4. `halting_time_unique`, `maximal_runtime_if_cover`, and `exact_maximum_if_certificate` combine an explicit finite-time outcome-or-nonhalting certificate with an explicitly supplied champion halt witness into a universal upper bound and an attained maximum.
5. `immediate_halt_leaf` is an actual proved search leaf for the class whose initial A/0 transition is halt.

The final `#print axioms` outputs for `Frontier.lean` are at most `[propext, Quot.sound]`. The additional modules use at most the ordinary Lean axioms `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. These are **generic soundness inferences**, not a completed tree. No numerical bound has been proved.

## Newly verified completeness edges: final-action semantics, symmetry, and one-halt normal form

[`TerminalBridge.lean`](./TerminalBridge.lean) defines a six-state explicitly-halting machine whose final instruction writes and moves before entering the halting state. `explicit_halts_iff_implicit` proves a step-by-step semantics bridge preserving exact halting times when the terminal writing and direction are erased. `all_explicit_iff_all_implicit` establishes the converse for all tables via a canonical 1RZ embedding. This closes the **last-step runtime convention** interface *within the self-contained formal model*, though an external source library parser still requires a verified bridge.

[`Symmetry.lean`](./Symmetry.lean) proves `normalized_haltsAt_iff` for arbitrary bijective renaming of all six state labels and optional left/right reflection of the full bi-infinite tape. Exact run length and blank tape are preserved, with the designated initial state **moved along with the permutation**. This provides a generic source-level safety rule behind the repository's 435 unrooted table-family census, but does not independently certify that the JS ledger's computed witness permutations were applied correctly.

[`OneHalt.lean`](./OneHalt.lean) proves `one_halt_normal_form`: for any six-state halting machine (even one with many missing/halting entries), there exists a same-time halting completion with **exactly one** undefined entry, chosen as the actual halting entry, all other missing entries filled by a fixed ordinary move. `one_halt_upper_bound` proves that a runtime upper bound checked over every one-halt machine automatically extends to all raw six-state halters. This is a constructive normalization for the step-count problem, not for the number of 1s left by an explicit final action.

[`Prune.lean`](./Prune.lean) constructs two completely proved all-time nonhalting search leaves, for first transition 0RA and 0LA: write 0, move right or left, remain in state A. The remaining 11 entries are universally arbitrary. In combination with `Frontier.lean`'s immediate-halt leaf, the coverage language now has **three concrete decidable leaf classes**. These are well-known easy machines, not a claim of new Busy Beaver classification.

All modules are compiled and audited by the existing [manual coverage workflow](https://github.com/FlareZ123/bb6/actions/workflows/agent8-coverage-contract.yml); no per-commit CI is enabled. The gap is now especially explicit: enumeration completeness can use these proven transformations and leaves, yet it lacks an exhaustive, verified decision certificate for all remaining rooted tables.

## Important semantic boundary

The local semantics has six states, two symbols, an initially blank tape, and a designated start state A. A transition to `none` has no successor. `HaltsAfter m n` denotes `n` successfully executed ordinary moves followed by an attempted absent transition. Its candidate step score is `n+1`. Standard Busy Beaver implementations also express writes and directions on transitions to a halting state (e.g. `1RZ`). A sound **external source-semantics bridge**, including the exact final-step convention for S(6), is required before a maximality theorem in this local model can be promoted to a theorem about the published BB(6) convention.

The independent [rooted portfolio ledger](../holdout-family-coverage/README.md) has 663 machine strings from a pinned **2026-10-16** external list, grouped into 435 unrooted tables. Its historical list is neither a complete enumeration certificate nor a proof that all omitted machines are below any given time bound. Root A must be tracked through any relabelling; a common unrooted table with two distinct initial states can have different blank-origin outcomes.

## Missing end-to-end certificate: first unproved edge

The `Cover` theorem exposes a precise contract: a single term

`Cover (DecidedBelow B) emptyTable`

would certify that **every** raw table represented by the local semantics either never halts on blank or halts with score at most `B`. Separately, `HaltsAfter champion n` and `n+1=B` would establish attainability.

**No such universal `Cover` term or verified mapping from the historical 663-root snapshot to it exists in this repository.** In particular:

- A source-complete, independently checked six-state transition-normal-form enumerator and all of its pruning transformations must be related to the exact raw table semantics, with a proof that every omitted table is safely represented or decided.
- Every leaf, including machines removed by external deciders, must carry a checked nonhalting theorem or an exact raw-time bound. A CSV entry marked “undecided”, “not curated”, or “formerly a holdout” does not provide a leaf proof.
- The model must be bridged to the precise published halting-action and step-score convention; the lower-bound witness must be connected to the same convention.
- State-permutation and tape-reflection reuse must track the **designated blank initial state**. Agent 3's existing raw conjugacy formalization is a useful starting point rather than an excuse to discard root distinctions.

The immediate gap is the **raw-enumeration-to-certified-leaf evidence chain**; it appears before the extraordinarily hard remaining machine-specific infinite orbit problems in any end-to-end proof of BB(6).

## Reproduction and prior research

- Local check: Lean 4.36.0-rc2, `lean im-results/agent8-coverage-contract/Frontier.lean`. Pinned manual CI workflow: `.github/workflows/agent8-coverage-contract.yml`; it has no per-commit trigger.
- The [bbchallenge construction method](https://bbchallenge.org/method) describes *five-state* sparse enumeration, first-undefined branching, pruning and a residual-machine database. The [bbchallenge seed source](https://github.com/bbchallenge/bbchallenge-seed) similarly documents its five-state run. Neither document by itself certifies the October 2026 **six-state** inventory.
- The bbchallenge collaboration's [BB(5) formal result](https://arxiv.org/abs/2509.12337) shows a full formal-completeness strategy for five states.
- The [2026-10-16 six-state holdout list](https://wiki.bbchallenge.org/wiki/Holdouts) is expressly an informally contributed snapshot, with no independent guarantee on its downloadable-list page.
- See the repository's [critic completeness intervention](../../communications/broadcast/2026-11-02T1608Z_critic-global-completeness-contract.md) for the motivation.

The definitions and lemmas are deliberately modest and likely standard; their contribution here is a **locally kernel-checkable formal interface for complete coverage**, rather than a claim of new mathematical discovery. Keep this material in `im-results/`.

## All-time fresh-ray and finite-entry nonhalting checker

Agent 8's [source-certified ray decider dossier](./RAY-DECIDER.md) documents an executable 64-subset certificate checker, uniformly quantified outward-sweep nonhalting leaves, and a two-step turning-prefix example leaving nine transition slots free. Its original unmodified-source [CI 41505998296](https://github.com/FlareZ123/bb6/actions/runs/41505998296) passed with standard axioms only. The independent BigInt census counts 37.341044736% of canonical six-state full tables as immediate monotone-ray cases; this percentage concerns the raw full-table space, not historic holdouts or true unresolved coverage. BB(6) remains open.


## Authenticated A6/F287 nonhalting cylinders and incremental global certificate, 2026-11-02

The previously published Google DeepMind Cryptids A6/F287 blank-A nonhalting theorem was imported and independently source-compiled against the pinned upstream commit `c86f15861709b76042998c5211c7b2f83991621b` (Lean 4.35.0-rc4). The original RLE is `1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---`. These are **logical consequences of prior machine-specific nonhalting proof**, not newly decided historical holdouts.

The original F/1 halt entry is unreachable on any blank execution. `HaltSlotFreedom.lean` proves that replacing such a transition by any of the 25 complete actions preserves all-time nonhalting. `F287HaltFreedom.lean` specializes this to the A6 source, certifying a full **25-table** cylinder; pinned whole-source [CI 41532345357](https://github.com/FlareZ123/bb6/actions/runs/41532345357) passed, with only the standard `[propext, Classical.choice, Quot.sound]` Lean axioms.

The stronger `AllHaltsFreedom.lean` leaves **every** originally halting input unspecified simultaneously, certifying exactly `25^h` full tables when the source has h missing entries. `CylinderFrontier.lean` embeds any source-authenticated partial cylinder in a complete `FrontierAudit` certified-or-open search; `AllHaltsGlobal.lean` combines these generic operations. Original-source Lean 4.36.0-rc2 [CI 41533231130](https://github.com/FlareZ123/bb6/actions/runs/41533231130) passed, and `F287CylinderGlobal.lean` source-checked in pinned Cryptids [CI 41533318944](https://github.com/FlareZ123/bb6/actions/runs/41533318944).

`RootShift.lean` proves an exact all-time `Int`-tape translation and run-concatenation theorem, enabling sound root changes after finite raw-machine prefixes. `F287Roots.lean` proves literal source root E enters shifted blank A after one primitive transition, while source root D enters shifted blank A after two. `F287RenamedRoots.lean` moves the initial D/E roots to conventional A via explicitly proved state-permutations and checks the resulting literal 12-entry RLE tables. Exact source proofs passed pinned Cryptids [CI 41534663734](https://github.com/FlareZ123/bb6/actions/runs/41534663734) and [CI 41535830930](https://github.com/FlareZ123/bb6/actions/runs/41535830930). Neither resulting rooted string occurs in the repository's historic October 2026 663-root holdout snapshot.

`F287RootCylinders.lean` produces three **pairwise disjoint** 25-table nonhalting cylinders from the A, D and E starting states and proves their disjointness over actual complete machines. `IncrementalAudit.lean` constructs a generic operator `addCertificate` that inserts authenticated partial source cylinders into a pre-existing arbitrary certified-or-open proof tree, preserving all previous certified terminals and keeping all incompatible outcomes explicitly open. `F287TripleAudit.lean` composes these into one source-verified global `FrontierAudit (DecidedBelow bound) emptyTable`, with all original `25^12` tables represented as certified or explicitly unresolved. **Exactly 75 source-covered complete tables are known from the three disjoint cylinders**, although the generated frontier still leaves nearly the entire universal space open. Pinned original-source whole-module [CI 41537949231](https://github.com/FlareZ123/bb6/actions/runs/41537949231) and generic Lean4.36 [CI 41537722049](https://github.com/FlareZ123/bb6/actions/runs/41537722049) both succeeded.

`OrbitPerms.lean` and `OrbitProof.lean` additionally generalize original-root, A-fixing state renamings and tape reflection to a computable 3 × 120 × 2 parameter space of authentic nonhalting cylinders, including 120 kernel-checked inverse permutations. Their direct pinned-source CI verification was dispatched as a separate follow-up and should be checked before presenting that generalized source chain as independently verified. A plain Python computation suggests the resulting 720 cylinders are disjoint, which is **experimental evidence only**; no formal all-pairs disjointness theorem or rigorously proved 18,000-table union has been established. Source-level proof of the individual nonhalting cylinders does not itself prove that finite cardinality.

All these modules are research infrastructure. Neither an upper bound on BB(6) nor a previously undecided 2026 root nor a halting champion witness is supplied. No full `Cover (DecidedBelow bound) emptyTable` exists. Keep this section and source in `im-results/`, outside the academically publishable `results/` directory.
