# Machine C and #623 mapped to the depth-four residual audit

**Status:** source-authenticated open-leaf mapping; not a halting/nonhalting classification.

## Audit being mapped

`im-results/agent32-zero-prefix-global/ResidualFrontierManifest.lean` defines

```lean
depth4ResidualAudit :=
  lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4
```

The audit uses score bound 6, finite-ray limit 6, physical scan limit 12, exact-lasso limit 12, entry-prefix limit 2, macro limit 4, and branch depth 4. `depth4ResidualTerminals` is exactly `depth4ResidualAudit.terminals`; `depth4ResidualManifest_unique` gives one unique terminal for each full machine. `encodePath` preserves the terminal's fresh-slot assignment order. The Python canonicalizer separately sorts assignments when constructing a symmetry key.

Both machine-specific frontier files prove the same depth-four audit is open at their respective full machines:
- Machine C: `machineC_first_four_global_slots`, `machineC_oracle_false_first_five`, `machineC_depth_four_open`, `machineC_first_four_mass` in `im-results/agent4-machine-c-global-path/MachineCFrontier.lean`.
- #623: `machine623_first_four_global_slots`, `machine623_oracle_false_first_five`, `machine623_depth_four_open`, `machine623_first_four_mass` in `im-results/agent8-623-frontier/Machine623Frontier.lean`.

Thus both source-authenticated blank-root paths follow the same depth-four audit to unique unresolved leaves. "Open" means the bounded source oracles did not certify the cylinder; it does not mean all compatible completions are nonhalting.

**Export caveat:** the latest known `agent32-zero-path-global.yml` run (43740950404) failed at the explicit export step, so no successful uploaded depth-four artifact was available for byte-level inspection. The mapping below is to the exact terminal records defined by the source manifest and machine-specific branch proofs; it is not a claim that a fresh JSONL artifact was successfully generated. The Machine C and #623 source-proof workflows themselves have successful runs (42338247534 and 42325888583, respectively).

## Machine C terminal

**Ordered terminal path** (also the `encodePath` field, preserving physical order):

```text
00:M111,10:M102,21:M001,20:M100
```

**Partial table:**

| Slot | Transition |
|---|---|
| A/0 | 1RB |
| B/0 | 1LC |
| C/1 | 0LB |
| C/0 | 1LA |

**Free slots:** A/1, B/1, D/0, D/1, E/0, E/1, F/0, F/1.

The compatible completion set is exactly
`{m : Machine // compatible p m}` for this four-entry partial table: each of the eight free slots has 25 possible instructions (24 moves plus halt). Its cylinder mass is
`25^8 = 152,587,890,625`, as certified by `machineC_first_four_mass`.

**Physical scan probe (deterministic replay of the manifest's scanner):**

- Result: `U` (first unassigned input), after 6 successful moves; this occurs before the 12-move scan limit.
- Configuration: state B (index 1), head position -2, one-cells `[-3,-2,-1,1]`.
- Next unassigned physical slot: B/1 (encoded slot `11`).
- Export stop reason: `tree-depth-exhausted`, because the terminal path already has depth 4. The physical probe nevertheless identifies B/1.

**Root-preserving symmetry class:** the group is the 240-element action of permutations of B–F fixing A, together with optional L/R reflection. Exhaustive enumeration of these 240 transforms using the algorithm in `canonicalize_residual_frontier.py` gives:

- Canonical key: `00:M101;10:M112;20:M110;21:M011`.
- Orbit size: 40; stabilizer size: 6 (the permutations of unused D, E, F).
- Canonicalizing witness: identity state relabeling and L/R reflection.

## #623 terminal

**Ordered terminal path**:

```text
00:M111,10:M012,20:M013,30:M103
```

**Partial table:**

| Slot | Transition |
|---|---|
| A/0 | 1RB |
| B/0 | 0RC |
| C/0 | 0RD |
| D/0 | 1LD |

**Free slots:** A/1, B/1, C/1, D/1, E/0, E/1, F/0, F/1.

The compatible completion set is again the full cylinder over the eight free slots, with
`25^8 = 152,587,890,625` completions, certified by `machine623_first_four_mass`.

**Physical scan probe (deterministic replay of the manifest's scanner):**

- Result: `U`, after 6 successful moves.
- Configuration: state D (index 3), head position 0, one-cells `[1,2,3,0]` (the exact `FinRayCfg.ones` list order).
- Next unassigned physical slot: D/1 (encoded slot `31`).
- Export stop reason: `tree-depth-exhausted`.

**Root-preserving symmetry class:**

- Canonical key: `00:M101;10:M002;20:M003;30:M113`.
- Orbit size: 120; stabilizer size: 2 (the swap of unused E and F).
- Canonicalizing witness: identity state relabeling and L/R reflection.

## Deeper #623 refinement (not a depth-four export terminal)

The separate `Machine623Path.lean` and `Machine623HaltCylinder.lean` (both included in the successful Agent 8 workflow) establish the eleven-entry/54-move cylinder of mass 25, with only F/0 unassigned. The separate `Machine623DeepFrontier.lean` file contains a further depth-eleven open-audit statement with physical scan limit 96, but that file is not included in the successful Agent 8 workflow and must be treated as an uncompiled experiment, not as an established Lean result.

`Machine623HaltCylinder.lean` proves `machine623_only_one_nontrivial_completion`: every completion of this eleven-entry cylinder is either the original #623 machine or `NeverHalts`. The 24 choices making F/0 an ordinary transition have no halting instruction anywhere; the sole nontrivial completion is the original machine with F/0=halt. Therefore the remaining mathematical obligation for this refined cylinder is precisely `NeverHalts machine623`.

A direct 96-step replay of the experimental deep-frontier path (not a Lean-verified theorem) ends at state C, head -4, with `ones = [-6,-8,-3,-3,-2,-1,0,1,2,3,4,5]`. This endpoint has not been added as a separate Lean `by decide` lemma.

## Machine C's deeper source path

`MachineCPath.lean` separately proves that eleven fresh inputs fix 23 moves and leave F/0 unassigned, with cylinder mass 25. This is a deeper refinement of the depth-four Machine C cylinder, not an additional terminal in the current depth-four export.

## Reproducibility and limitations

- Raw transition tables and blank-root paths: `MachineCPath.lean`, `Machine623Path.lean`.
- Depth-four open status and first four fresh slots: the two `*Frontier.lean` files cited above.
- Export terminal semantics and probe encoding: `ResidualFrontierManifest.lean`.
- Root-preserving symmetry action: `im-results/agent8-coverage-contract/Symmetry.lean`.
- Canonical-key/orbit enumeration: `im-results/agent32-zero-prefix-global/canonicalize_residual_frontier.py`.

The physical probe endpoint fields and 240-element canonicalization values above are deterministic replays of those source algorithms, not new Lean theorems in this report. The successful machine-specific workflows certify the actual first-four paths, cylinder masses, and open status. The physical-probe endpoints were independently checked with a local Lean 4.36.0-rc2 finite replay model mirroring the exact `RayFinite.writeOnes`/`finiteMove` semantics; both `.unknown 6` equations close by `decide` and introduce no `sorryAx`. This replay is not yet wired into a theorem importing the repository's `machineCPrefix`/`machine623Prefix` definitions. The symmetry keys and orbit sizes were independently recomputed by exhaustive Python enumeration of all 240 root-preserving transformations using the repository canonicalizer's algorithm; these are not Lean theorems. No claim is made that either depth-four cylinder has been fully classified, or that BB(6) has been solved.
