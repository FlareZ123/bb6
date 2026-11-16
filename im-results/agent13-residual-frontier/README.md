# Authentic roots inside the depth-four residual frontier

**Status: intermediate integration, not yet Lean-preflighted or exported.** The source module `RootedFrontierMap.lean` is a proof draft pending a targeted Lean 4.36.0-rc2 dependency-closure compile. The 240-element symmetry keys below are an exact finite enumeration computed independently; they still need to be cross-checked against the existing manual exporter artifact. Nothing here is promoted to `results/`.

This work connects two already source-authenticated blank-root machines to exact leaves of Agent 32's diagnostic audit. It does **not** close either machine's all-time behavior and does **not** give a BB(6) upper bound.

## Exact audit being mapped

The exported object is

`depth4ResidualAudit = lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4`.

The final argument is **tree depth four**, not twelve. The separately named `globalLassoPhysicalTraceAudit` has tree depth twelve. The audit's target is `DecidedBelow 6`: a completion is certified only if it is nonhalting or halts with score at most six. A known halt above six is not certified by this predicate.

For an open terminal, the manifest records the three actual composite oracle outcomes as false:

- `finiteDecisionOracle p 6 6`
- `finiteLassoOracle p 12`
- `finiteEntryMacroBiOracle p 2 4`

The stop reason for the two roots below is `tree-depth-exhausted`. The physical probe is separate from the tree-depth stop: it finds a still-unassigned physical input after six successful moves, within its 12-move scan limit. The exact global discharge interface for a leaf partial table `p` is a proof of `Cover (DecidedBelow B) p` for all compatible total tables, or a stronger pointwise all-time theorem.

## Machine C (historical holdout #39)

**Ordered branch path**

| Branch | Input | Fixed action |
|---:|---|---|
| 1 | A/0 | `1RB` |
| 2 | B/0 | `1LC` |
| 3 | C/1 | `0LB` |
| 4 | C/0 | `1LA` |

This is the first four entries of `machineCVisited`; the branch order matters. The terminal is the unique manifest terminal matching this root (not the unique machine in the cylinder). The partial table has eight free inputs:

`A/1, B/1, D/0, D/1, E/0, E/1, F/0, F/1`.

Thus the exact raw compatible completion set has mass `25^8 = 152,587,890,625`. This is the full four-row leaf, **not** the size of the authentic source-root cylinder.

**Root-preserving symmetry class**

- Group: all (5!) permutations of B–F fixing A, optionally composed with L/R reflection; order 240.
- Canonical key: `00:M101;10:M112;20:M110;21:M011`.
- Orbit size: 40; stabilizer size: 6.
- Canonicalizing transform: identity state permutation and L/R reflection.

**Next physical input**

The exact 12-limit probe returns unknown at **B/1** after six successful moves. Endpoint: state B, head (-2), one-cells ([-3,-2,-1,1]). Every completion of this partial table shares that six-move prefix; B/1 is the next free transition query. The tree stopped because it had used its four branch levels, not because the physical scan limit was exhausted.

**Sharper authentic-root subcylinder**

The authentic 11-row prefix fixes, in order,

`A/0, B/0, C/1, C/0, B/1, D/1, E/0, F/1, D/0, A/1, E/1`.

Only F/0 remains free, so this source-authentic subcylinder has 25 completions and lies inside the (25^8) four-row leaf. The source-connected `CryptidsPhysicalC.lean` proves the stronger exact equivalence `machineC_cylinder_raw_halts_iff_thin_gateway`: for every one of the 25 completions, physical halting is equivalent to F/0 remaining HALT and the pinned three-counter source reaching `BB6CLine.Reach (0,2*j,4*j+10)` for some (j). Its conditional corollary `machineC_counter_nonhalt_closes_physical_cylinder` closes the entire authentic 25-machine cylinder if that three-counter process is proved nonhalting. This is a sharp source-level reduction, **not** a proof of the required nonhalting statement; the thin-gateway reachability remains open.

**Stronger source-checked root reductions already exist elsewhere in the repository.** Agent 4's `CResidualMassIntegration.lean` composes the original-source halt equivalence with a finite raw-mass-10,000 exclusion. The relevant integration theorems compiled in [CI 42420171662](https://github.com/FlareZ123/bb6/actions/runs/42420171662): a genuine Machine C halt must have a low/high stopping target of raw mass greater than 10,000, with the corresponding low/high parameter-tail restrictions recorded in `im-results/agent4-machine-c-global-path/README.md`. That all-phase workflow failed later in an unrelated M0Mod8Three proof; the Machine C integration theorems were printed before that unrelated failure.

Agent 4's `CResidualMass100000.lean` strengthens the *target exclusion* to raw mass 100,000. Its `rootTrace100000_no_stop_target` theorem depends on no axioms and compiled in dedicated original-source [CI 42420156191](https://github.com/FlareZ123/bb6/actions/runs/42420156191), using a 50,000-step half-mass bound and a complete finite parameter box through (m\le6). However, the corresponding 100,000-mass integration into the genuine Machine C halt theorem had not yet been added or compiled in the Agent 4 README. This is a stronger checked stop-target exclusion, **not** a complete Machine C nonhalting proof.

The root-only section analysis is sharpened further in the Lean source `im-results/agent15-c-halting/NoMachineCHalt.lean`, theorem `blank_halt_requires_residual_families`: a blank-root halt forces one of two exact residual source families. **Current CI status is unverified:** the latest `agent15-c-halting` run (42367962614) failed at a preceding `cp` of missing `im-results/agent38-m192-high-zero/HighZeroEven.lean`, before the log showed this module compiling; do not treat that run as a successful check. A local compile or repaired workflow run is still needed.

- first family: `CReach 1 k`, with `m >= 1`, `k >= 8`, and `k+3*m+4 = 2^(2*m+3)`;
- second family: `CReach (2*j+3) k`, with `(j,m) != (0,0)`, `k >= 10`, and `k+j+3*m+5 = 2^(2*m+2)*(j+3)`.

The source file invokes `BB6CLine.special_unreachable` and `source_no_3_7` to exclude the two small feeders `(1,4,0)` and `(3,7,0)`. Because the current workflow fails before compiling `NoMachineCHalt.lean`, the residual-family statement above is a **source-level proposed reduction, not yet a CI-verified conclusion**. If checked, it would leave the infinite first- and second-family reachability questions open; it would still not prove nonhalting. The current M192 low-core condition does not cover either family wholesale; the dossier records explicit first- and second-family examples outside that predicate. An unformalized inverse-tree derivation in [ThinGatewayInverse.md](ThinGatewayInverse.md) suggests that the CLine thin gateway itself maps into the same second-stop equation family (the `m=0` slice is the first predecessor; `m >= 1` comes from repeated even-`k` inverse branches). This is an intermediate derivation pending Lean formalization and a source-coordinate bridge, not an additional proof.

## Machine #623

**Ordered branch path**

| Branch | Input | Fixed action |
|---:|---|---|
| 1 | A/0 | `1RB` |
| 2 | B/0 | `0RC` |
| 3 | C/0 | `0RD` |
| 4 | D/0 | `1LD` |

The partial table has eight free inputs:

`A/1, B/1, C/1, D/1, E/0, E/1, F/0, F/1`. The terminal is the unique manifest terminal matching this root (not the unique machine in the cylinder).

Its exact raw compatible completion mass is again `25^8 = 152,587,890,625`.

**Root-preserving symmetry class**

- Group: all (5!) permutations of B–F fixing A, optionally composed with L/R reflection; order 240.
- Canonical key: `00:M101;10:M002;20:M003;30:M113`.
- Orbit size: 120; stabilizer size: 2.
- Canonicalizing transform: identity state permutation and L/R reflection.

**Next physical input**

The exact 12-limit probe returns unknown at **D/1** after six successful moves. Endpoint: state D, head (0), one-cells ([1,2,3,0]). Every completion shares this six-move prefix; D/1 is the next free transition query. The tree stop is again depth-four exhaustion, not scan-limit exhaustion.

**Sharper authentic-root subcylinder**

The authentic 11-row prefix fixes, in order,

`A/0, B/0, C/0, D/0, D/1, C/1, B/1, A/1, E/1, E/0, F/1`.

Only F/0 remains free, so the source-authentic subcylinder has 25 completions and lies inside the (25^8) leaf. `Machine623Source.lean` proves cellwise equality `original_eq_machine623` with the pinned Cryptids source table; this source identity was compiled in original-source CI [42323091458](https://github.com/FlareZ123/bb6/actions/runs/42323091458). The source-connected `Machine623HaltCylinder.lean` theorem `machine623_only_one_nontrivial_completion` proves that 24 of these 25 completions are `NeverHalts`; the sole remaining completion is that original #623 machine. `machine623_full_cylinder_if_never` closes the entire 25-machine cylinder if the original machine is proved nonhalting. The halt-cylinder and frontier modules were compiled in successful canonical-frontier CI [42323087878](https://github.com/FlareZ123/bb6/actions/runs/42323087878). The remaining question is precisely whether the original #623 run ever reads F/0; it is not resolved here.

## What is formally connected, and what remains

`RootedFrontierMap.lean` is intended to kernel-check the following integration:

1. an open audit branch has a manifest terminal whose path is the exact ordered path selected by the total machine;
2. the terminal's partial table is reconstructed from that path and its mass is exactly (25^8);
3. each authentic 11-row, 25-completion cylinder is contained in its corresponding four-row manifest leaf;
4. the three composite oracle outcomes are false at each root leaf;
5. the 12-step physical probe identifies the exact next unknown input and a six-move finite-tape endpoint, uniformly for every compatible completion.

The symmetry keys and orbit sizes are finite computations over the 240 root-preserving transforms, not Lean theorems. The symmetry action itself is specified in `im-results/agent8-coverage-contract/Symmetry.lean`; the existing exact exporter is `im-results/agent32-zero-prefix-global/canonicalize_residual_frontier.py`.

### Required next work

1. Obtain the requested local Lean preflight for `ResidualFrontierManifest.lean`, the Machine C/#623 path and frontier modules, and `RootedFrontierMap.lean`. The prior manifest export run failed during elaboration; its diagnostics were repaired in the current source, but no fresh compile claim is made.
2. Only after that local preflight succeeds, extend the existing manual-only `.github/workflows/agent32-zero-path-global.yml` export branch to compile the two root-frontier modules and `RootedFrontierMap.lean`, then run its `export_frontier=true` path once.
3. Run [verify_export.py](verify_export.py) on `/tmp/bb6-depth4-residual-frontier.jsonl`; it asserts both exact ordered paths, partial tables, free slots, (25^8) masses, oracle outcomes, probe endpoints, discharge contract, canonical keys, and orbit sizes.
4. For actual mathematical closure, either prove `Cover (DecidedBelow B) p` for the entire four-row leaf, or finish the authentic-root F/0 all-time question for each 25-completion subcylinder. The latter does not by itself close the entire (25^8) leaf.

No exact BB(6) value, global six-state upper bound, Machine C all-time decision, or #623 all-time decision is claimed.
