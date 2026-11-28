# Raw34 D1=1RD: exact accepted-cylinder complement

**Scope and status.** This is an exact finite set-theoretic physical-table partition, **not** a new kernel-checked Lean proof or a complete Raw34 Cover. Fix D1=`1RD` in the eight-hole parent `1RB---_1RC---_0RD---_1LC---_------_------`. There are **25^7 = 6,103,515,625** possible physical completions over the remaining seven entries, counting HALT as a distinct 25th action.

The source-accepted Raw34 nonhalting cylinder families cover **3,320,312,500** of these machines. The remaining **2,783,203,125** are *not covered by these particular certificates*; this says nothing about whether they actually halt. The exact algorithm partitions this branch into **124 disjoint proof-labeled covered leaves and 165 disjoint uncovered leaves**, with 12 genuine 25-way splits and 13 skipped wildcard slots. It verifies conservation of physical-table mass and explicitly preserves HALT action branches. The output [manifest](D1-1RD-proof-frontier.json) identifies each remaining partial-table leaf and each covered leaf's original-source theorem family.

## Reproduction and proof boundary

From repository root run `node im-results/agent23-raw34-frontier/export.mjs` to audit the committed manifest or append `--write` to regenerate it after changing the upstream accepted proof set. The pure JavaScript program consumes Agent50's unmodified [depth-two/depth-three witnessed certificates](../agent50-raw34-firsthole/), and adds its eleven first-level side cycles, unary-growth cylinder, closed C–D pairs, 1,728 B–C–D triples, and three source-accepted longer growth pumps. References to corresponding accepted source files and CI jobs are embedded in the JSON `sourceMap`.

A physical-machine **HALT** instruction is not the wildcard `---` in the partial-table notation. The manifest's `decisions` field is authoritative: when a leaf fixes HALT, `explicitHalts` records the affected slots and `projection` replaces that action with `---` **only as a lossy display**. A consumer must not mistake that projection for the original exact leaf.

The script verifies: (1) every covered leaf contains an exact accepted input proof cylinder, (2) every uncovered leaf has empty intersection with all 3,087 input proof cylinders, (3) all 289 leaves are pairwise disjoint, and (4) their 25-ary masses total 25^7. These are direct finite calculations; neither this JavaScript run nor the JSON output substitutes for an original-source Lean proof of the branch partition.

**Important fixed entry:** the accepted triple-sweep `pA` has A1=1LD, C1=0RA and D1=1RD. Omitting A1 would incorrectly give a six-hole rather than five-hole cylinder and overcount the certified union. This exporter includes A1=1LD.

## Next mathematical obligation

For a globally consumable Raw34 result, prove an exhaustive Lean split/containment theorem using the existing 25-outcome transition refinement and compose the original-source nonhalting witnesses at the covered leaves. Resolve every remaining open child at a sufficient weighted score threshold, and only then establish a whole-parent `Cover` and exact membership in the current canonical roster. These exact uncovered children are the next leaf-level research targets, not a claim of a 40-to-39 global reduction.

This complements the [source-accepted Raw34 family synthesis](../../results/2026-11-28-raw34-covering-97b-tables-agent50.md) without altering its 97,539,062,500-machine full-parent union figure.
