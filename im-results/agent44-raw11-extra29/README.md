# Raw11 Extra29: original-source parent Cover and exact 148→147 consumer

**Exact Raw11 extra-roster index 29 parent:**
`1RB0LB_1RC1LC_0LA0RD_------_------_------`.

**Current status:** the parent Cover is a candidate, not yet source accepted. The exact consumer source is staged in `Raw11Extra29After148.lean`; it does not establish a residual decrement until both the parent Cover and consumer compile with the required axiom audit.

## Discovery evidence (not a proof)

The six-hole discovery run **45896597080** had already classified the five exceptional last-hole leaves of Extra29, as well as Extra24 and Extra30. The reconstruction in `scan.cjs` is therefore not a new discovery claim. It reproduces a retained candidate with 186,373 nodes, weighted bound 886, 137,896 side-cycle leaves, 2,411 bank automata, 1,882 FAR leaves, 7,767 splits and 36,417 last-hole checks. These are search/candidate statistics; none is a kernel-checked parent Cover.

Reproduce the separate candidate reconstruction from the repository root:

```sh
node im-results/agent44-raw11-extra29/scan.cjs /tmp/extra29-scan
RAW11_PARENT_KIND=extra node im-results/agent5-weighted-tnf-queue/generate-coarse-parent-shards.cjs 29 /tmp/extra29-scan /tmp/extra29-source 400 800
```

## Source proof route

The existing manual dispatcher `.github/workflows/agent5-raw11-parent-covers.yml` accepts extra-parent indices. It has been dispatched for `parents=[29]` with the frozen six-hole artifacts and extended automata enabled. It uses `generate-extra-parent-shards.cjs`, compiles the complete generated original-source DAG against the accepted core, and audits `BB6.Agent5Raw11Extra29.cover`. The run's own manifest, generated sources, compiler result and transitive axiom profile determine acceptance; the separate `scan.cjs` node count is not substituted for them.

## Exact global-consumer interface

`Raw11Extra29After148.lean` defines the literal six-state partial table, proves it equals the generated source parent with `sameTable_sound`, proves exact membership in the accepted 148-entry predecessor, and computes the exact 148→147 census. It then composes the source-checked parent Cover into `raw11_cover_from_147` at the existing common bound (B\ge 4663).

The existing manual consumer workflow `.github/workflows/agent44-raw11-q0148-after148.yml` has been generalized to select either its original q0-148 target or Extra29. For Extra29, it downloads the accepted parent artifact and checks the new consumer module against the exact Raw11 299→148 predecessor, Extra132 and Extra140 proof objects.

**No Raw11 148→147 decrement is claimed until that consumer succeeds.** Even a successful 148→147 theorem leaves 147 conditional Covers; it is not a BB(6) upper bound.
