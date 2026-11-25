# Exact convergence of the 124-table first-one residual frontier

This intermediate result joins two independently constructed certificate manifests:

- Agent31's seven-edge four-hole frontier, which proves that every completion of the first-one cylinder is either weighted-bounded by 395 or extends one of 124 residual partial tables.
- Agent50's nine-edge weighted-TNF data frontier, reconstructed from its recursive sibling trees, six growth tables, 98 block-pump tables, and three exceptional table exclusions.

The exact residual sets agree slot-for-slot after packing Agent31's partial machines into Agent50's twelve-slot representation. A machine-readable export with stable root-to-leaf residual addresses, all twelve slots, and hole counts is provided in canonical-124.json. The Lean theorem agent31PackedRoster_perm_canonicalResidualRoster proves list permutation by kernel computation; it does not rely on a hash, count, or textual manifest.

The theorem canonicalResidualRoster_sound_395 transports Agent31's sharper bound 395 to the canonical Agent50 data roster. Thus both research lines can work against one common 124-table frontier, with the stronger bound retained.

## Important proof-status distinction

The Lean bridge deliberately imports only the pure data modules (RecursiveResidual, DepthEightSiblingData1-4, C1Growth, and BlockPumpData1-4). It reconstructs the sibling, growth, and pump roster definitions locally. It does **not** import DepthEightSiblingCoverage or BlockPumpCoverage: run 45465820694 found a Lean type error at List.find?_some, and the associated replaceResidual_sound / refinedRootRoster_sound / finalRootRoster_sound output exposed sorryAx. It also does not import ExceptionalPumps.lean: run 45465034561 found an unsolved branch in never_of_arbitrary and reported sorryAx for Nested.never / DoubleGrow.never. ExceptionalPumps.lean has since been edited, but no successful recompile of that proof module has been observed.

The three exceptional tables are reproduced as data exclusions only. No exceptional nonhalting claim or Agent50 coverage-wrapper soundness theorem is used. The 395-bound soundness theorem here comes solely from Agent31's checked remainingRootRoster_sound theorem plus the exact table permutation.

This is an intermediate upper-bound component, not a complete BB(6) proof: three source-checked five-hole cylinders (raw66, raw70, raw80) have since been removed from the frontier, leaving 121 residual cylinders to resolve; the first-one cylinder is only one part of the global machine space.

## Verification

The CI target weighted-tnf-roster-convergence regenerates the source-derived four-hole data, uses the committed Agent50 tree/pump data, compiles the import closure without the defective coverage wrappers or ExceptionalPumps, and rejects sorryAx or native_decide in the output.

## Root-to-leaf composition contract (Lean-checked)

`RosterCoverComposition.lean` supplies the missing logical composition interface without requiring a second explicit root tree or the noncomputable Agent31/Agent50 roster permutation.

- `cover_of_roster_dichotomy` turns any sound root dichotomy into a finite residual roster, plus one `Cover (WeightedBound C)` for each residual, into a single root `Cover`.
- `exact_from_roster_dichotomy` lifts that cover to B≥C, converts it to the normalized `WeightedTNFCertificate`, and combines it with the raw champion witness.
- Specializations consume Agent31's accepted 124-cylinder dichotomies at both 395 and 7014. The 7014 interface allows sibling certificates at that bound to be used without pretending they prove the stronger 395 bound. The separate FiveHoleRoster theorem below removes raw66/raw70/raw80 at the sharper 395 bound.

The generalized module and its full import closure passed the manual CI target `weighted-tnf-roster-composition` in run [45489676758](https://github.com/FlareZ123/bb6/actions/runs/45489676758). The workflow rejects `sorryAx` and `native_decide` in the compiled closure.

This is a conditional theorem, not a completed upper bound: the per-residual safety Covers and the attained champion witness still have to be supplied. The generic interface alone closes no residual; the separate FiveHoleRoster source certificate closes exactly three and leaves 121.


## Three source-checked five-hole closures: raw66, raw70, raw80

The existing Agent10 candidate generator and pinned specs now have a source-checked Lean bridge through `FiveHoleRoster.lean`. The three canonical partial tables match residual indices 66, 70, and 80 slot-for-slot:

| Residual | Fixed B1 transition | Weighted bound | Open FAR leaves |
|---|---:|---:|---:|
| raw66 | 0RB | 120 | 125 |
| raw70 | 0RC | 104 | 22 |
| raw80 | 1RE | 164 | 395 |

Each is a complete five-hole cylinder (25^5 completions). The generated exhaustive trees contain 2,009 split nodes, 39,013 cycle leaves, 6,724 last-hole leaves, and 542 open leaves in total. The generator checks the committed open-list hashes and tree statistics; Lean checks every open FAR certificate and the exact-table transfer. All three bounds are below 395.

The Lean closure in run [45510820286](https://github.com/FlareZ123/bb6/actions/runs/45510820286) successfully compiled `Raw66Data`, `Raw70Data`, `Raw80Data`, and `BB6.Agent10FiveHoleRoster.reduced_sound`; their printed assumptions were only `propext`, `Classical.choice`, and `Quot.sound`. The overall run failed only when the newly added `FiveHoleRosterComposition.lean` wrapper referenced `WeightedBound` and `WeightedTNFCertificate` without opening `BB6.Agent13BlankDelay`. That namespace import is now fixed. The full wrapper rerun [45513767248](https://github.com/FlareZ123/bb6/actions/runs/45513767248) passed.

The machine-readable [canonical-121.json](canonical-121.json) export preserves original canonical indices, stable addresses, the removed entries, the reduced roster's hole histogram (18/14/22/19/12/17/19 for 4–10 holes), and exact completion mass 1,878,783,591,015,625. The roster bridge proves `reduced_count = 121` and the sound dichotomy: every completion of the authentic 1RB root is either already bounded by 395 or compatible with one of the 121 retained residual tables. `FiveHoleRosterComposition.lean` exposes the corresponding root Cover, normalized TNF certificate, and conditional exact-BB(6) theorem once the remaining 121 Covers and champion witness are supplied. The specialized wrapper is now fully Lean-checked by run 45513767248.

This is a genuine reduction of the intermediate frontier, not a global upper bound: the remaining 121 safety obligations are still open.

## Mixed-bound maximality contract and 109-roster ingestion

The earlier same-threshold composition theorems remain logically sound, but their premise
`∀ e ∈ roster, Cover (WeightedBound C) e.2` is not the right target for a maximality
proof when the attained champion has score `B > C`. Requiring every retained cylinder
to be safe at the early classification cutoff would force the champion below that cutoff.

`RosterCoverComposition.lean` now also supplies the mixed-bound interface:

- the root dichotomy is retained at the early cutoff `C`;
- each retained cylinder is required to have `Cover (WeightedBound B)`;
- the already-bounded root branch is lifted from `C` to `B`, while residual leaves
  are consumed directly at `B`.

The new `MixedBound109Composition.lean` instantiates this contract against the
source-accepted `Combined109Roster.reduced_sound` dichotomy at `C = 7014` and the
exact champion score `B = proposedTM63Moves + 7`. It proves, using the exact champion
run and its exact blank-delay list, that:

1. `B > 7014`;
2. the champion is compatible with the authentic first-one root;
3. the champion is not `WeightedBound 7014`, so the accepted 109-way dichotomy places
   it in one of the 109 retained residual cylinders;
4. the complete champion table is a concrete singleton `Cover (WeightedBound B)`
   but cannot be a `Cover (WeightedBound 7014)`;
5. if all 109 residual cylinders receive `B`-bound Covers, the mixed adapter yields
   the normalized first-one TNF certificate and conditional `ExactBB6 B`.

This is a corrected, satisfiable proof contract and a concrete larger-bound leaf test,
**not** a completed upper bound. The 109 full-cylinder safety obligations at `B`
remain unproved; the singleton example does not discharge its containing residual
cylinder. The combined manual CI target is being extended to compile the original
champion source closure and the mixed-bound adapter together.
