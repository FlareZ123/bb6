# Raw34 D1=1RD: explicit finite proof frontier and assigned-halt descendants

**Status (28 November 2026).** This is an exact *finite computational* physical-table partition, with an additional twelve-leaf source-Lean proof **draft pending full compilation**. It is not a complete Raw34 Cover or a universal BB(6) upper bound. The original certified Raw34 nonhalting families remain unchanged.

For the Raw34 parent `1RB---_1RC---_0RD---_1LC---_------_------` with D1=`1RD`, exactly **25^7 = 6,103,515,625** physical tables are possible:

| Classification at the current evidence level | Physical completions |
| --- | ---: |
| In previously accepted nonhalting cylinders | **3,320,312,500** |
| Outside those accepted nonhalting cylinders | **2,783,203,125** |

The finite recursion partitions this branch into **124 proof-labeled covered leaves and 165 disjoint leaves not covered by those nonhalting certificates**. It uses 12 actual 25-outcome splits, 13 wildcard skips, and 314 visited nodes.

## Concrete new finite-halt candidates

Independently executing the original blank-start transitions of each of the 165 uncovered leaves to its first unassigned instruction or assigned HALT identifies **12 leaves that encounter an explicitly assigned HALT without ever querying an unassigned transition**. Their disjoint physical-machine mass is **351,562,500** (one six-hole case of 244,140,625 completions, plus eleven five-hole cases of 9,765,625 each). Their assigned HALT is encountered within **9 to 12 ordinary step attempts** (the C1=HALT case at attempted step 8); the other **153 leaves and 2,431,640,625 completions** still first encounter an unspecified instruction.

The complete individual table decisions, query traces, halt times, and physical masses are in [halting12.json](halting12.json). The [Raw34D1RDHalting12.lean](Raw34D1RDHalting12.lean) draft uses *existing original-source* `finiteHaltCheck_sound` and `weighted_of_margin`, with 12 explicit checked Boolean instances, to attempt a `Cover (WeightedBound 18)` for each fixed halt leaf. **Source-level acceptance has not yet been obtained** because the local shell/Lean failed at the tool boundary; do not count these candidates as kernel-proved halting cylinders until a successful original-source CI source and axiom audit.

## Reproducible complement

The pure [export.mjs](export.mjs) consumes Agent50's unmodified [depth-two and depth-three certificate data](../agent50-raw34-firsthole/) and reconstructs [D1-1RD-proof-frontier.json](D1-1RD-proof-frontier.json). Run from repository root `node im-results/agent23-raw34-frontier/export.mjs` to audit the manifest, or `--write` to regenerate it. The script checks 3,087 original accepted proof patterns, containment of every covered leaf, zero intersection of any uncovered leaf with any input proof, 289-way leaf disjointness, and the exact 25-ary total mass. Source families include eleven oriented rays, 74 depth-two and 1206 depth-three side cycles, unary growth, closed C–D and B–C–D controls, and three accepted polynomial sweep pumps.

A physical **HALT** instruction is different from the wildcard `---`. The manifest's `decisions` and `explicitHalts` are authoritative. Its `projection` replaces a fixed HALT with `---` **solely for human-readable display** and is not a faithful completion definition. The accepted triple-sweep `pA` additionally fixes A1=1LD, not a wildcard: its correct five-hole cylinder is used.

## Mathematical proof boundary and next action

The accepted source Lean proofs establish `NeverHalts` for each old nonhalting source cylinder. The finite JS partition/trace computation is not a Lean partition theorem, and the twelve new `WeightedBound 18` declarations are an **uncompiled proof candidate**. To promote them, compile `Raw34D1RDHalting12.lean` against unmodified `FiniteHalting`, `WeightedFirstOneCover` and the full dependencies in Lean 4.36.0-rc2 with axiom profiles excluding `sorryAx`. Then compose the checked 25-way physical split with these 12 and the accepted nonhalting leaves, explicitly retaining the 153 still open leaves; solve all remaining descendants at the target score before consuming the whole parent in the accepted global roster.

The 2,431,640,625 completion remainder is **not known to halt or diverge**, and no new Canonical40 reduction is claimed. Full Raw34 accepted nonhalting union remains 97,539,062,500 physical completions in [Agent50's published synthesis](../../results/2026-11-28-raw34-covering-97b-tables-agent50.md).
