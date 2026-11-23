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

Only F/0 remains free, so this source-authentic subcylinder has 25 completions and lies inside the (25^8) four-row leaf. The source-connected `CryptidsPhysicalC.lean` proves the stronger exact equivalence `machineC_cylinder_raw_halts_iff_thin_gateway`: for every one of the 25 completions, physical halting is equivalent to F/0 remaining HALT and the pinned three-counter source reaching `BB6CLine.Reach (0,2*j,4*j+10)` for some (j). Its conditional corollary `machineC_counter_nonhalt_closes_physical_cylinder` closes the entire authentic 25-machine cylinder if that three-counter process is proved nonhalting. This is a sharp source-level reduction, **not** a proof of the required nonhalting statement; the thin-gateway reachability remains open. The Agent 4 dossier records successful original-source CI [42336664117](https://github.com/FlareZ123/bb6/actions/runs/42336664117) for its Machine C all-time source chain, and successful canonical-frontier CI [42323041110](https://github.com/FlareZ123/bb6/actions/runs/42323041110) for `MachineCFrontier`/`MachineCElevenFrontier`.

**Stronger source-checked root reductions already exist elsewhere in the repository.** Agent 4's `CResidualMassIntegration.lean` composes the original-source halt equivalence with a finite raw-mass-10,000 exclusion. The relevant integration theorems compiled in [CI 42420171662](https://github.com/FlareZ123/bb6/actions/runs/42420171662): a genuine Machine C halt must have a low/high stopping target of raw mass greater than 10,000, with the corresponding low/high parameter-tail restrictions recorded in `im-results/agent4-machine-c-global-path/README.md`. That all-phase workflow failed later in an unrelated M0Mod8Three proof; the Machine C integration theorems were printed before that unrelated failure.

Agent 4's `CResidualMass100000.lean` strengthens the *target exclusion* to raw mass 100,000. Its `rootTrace100000_no_stop_target` theorem depends on no axioms and compiled in dedicated original-source [CI 42420156191](https://github.com/FlareZ123/bb6/actions/runs/42420156191), using a 50,000-step half-mass bound and a complete finite parameter box through (m\le6). However, the corresponding 100,000-mass integration into the genuine Machine C halt theorem had not yet been added or compiled in the Agent 4 README. This is a stronger checked stop-target exclusion, **not** a complete Machine C nonhalting proof.

The root-only section analysis is sharpened further in the Lean source `im-results/agent15-c-halting/NoMachineCHalt.lean`, theorem `blank_halt_requires_residual_families`: a blank-root halt forces one of two exact residual source families. **Current CI status is unverified:** the latest `agent15-c-halting` run (42367962614) failed at a preceding `cp` of missing `im-results/agent38-m192-high-zero/HighZeroEven.lean`, before the log showed this module compiling; do not treat that run as a successful check. A local compile or repaired workflow run is still needed.

- first family: `CReach 1 k`, with `m >= 1`, `k >= 8`, and `k+3*m+4 = 2^(2*m+3)`;
- second family: `CReach (2*j+3) k`, with `(j,m) != (0,0)`, `k >= 10`, and `k+j+3*m+5 = 2^(2*m+2)*(j+3)`.

The source file invokes `BB6CLine.special_unreachable` and `source_no_3_7` to exclude the two small feeders `(1,4,0)` and `(3,7,0)`. Because the current workflow fails before compiling `NoMachineCHalt.lean`, the residual-family statement above is a **source-level proposed reduction, not yet a CI-verified conclusion**. If checked, it would leave the infinite first- and second-family reachability questions open; it would still not prove nonhalting. The current M192 low-core condition does not cover either family wholesale; the dossier records explicit first- and second-family examples outside that predicate. An unformalized inverse-tree derivation in [ThinGatewayInverse.md](ThinGatewayInverse.md) suggests that the CLine thin gateway itself maps into the same second-stop equation family (the `m=0` slice is the first predecessor; `m >= 1` comes from repeated even-`k` inverse branches). This is an intermediate derivation pending Lean formalization and a source-coordinate bridge, not an additional proof.

## New M512 thin-gateway residue sieve (16 November 2026)

The new [ThinGatewayM512.md](ThinGatewayM512.md) applies Agent 19's existing M512 quotient to the actual physical-halt gateway T_j=(0,2j,4j+10). The independent JS reproduction [thin_gateway_m512.js](thin_gateway_m512.js) matches the established quotient census exactly (67,633,152 vertices, 27,858,704 reached, 221,572,376 representative edges) and then finds that only 116 of the 256 thin-index residue classes remain admitted; the other 140 classes are excluded for every lift modulo 256. This is an infinite congruence restriction on the authentic root, not a bounded simulation. It remains a computational quotient result, not a Lean theorem, and admitted classes are not claimed reachable. The deep inverse branch has j ≡ 254 (mod 256), which is admitted, so the sieve does not close the unbounded deep tail.
## M512 all-time source-parameter sieve

The broader [M512SourceParameterSieve.md](M512SourceParameterSieve.md) applies the same quotient not only to thin gateways but also to both source-certified low/high stopping families. For m>=5, the low family has 190 admitted and 322 excluded residues modulo 512. For m>=4, the high family has 107,446 admitted and 154,698 excluded pairs modulo 512 x 512 (the complete 32 KiB admission mask is generated by [m512_parameter_sieve.js](m512_parameter_sieve.js)). The small m=0..4 low and m=0..3 high cases are checked separately. The quotient census matches Agent 19's 67,633,152 / 27,858,704 / 221,572,376 counts. This is an infinite necessary-condition sieve for every lift of the parameter residues, not a bounded run; admitted targets remain unproved reachable, and the quotient/source bridge is not yet Lean-formalized.
## M16 section quotient: the 4,608-state draft is superseded

The [CLineM16SectionFilter.md](CLineM16SectionFilter.md) and [m16_c0_quotient.js](m16_c0_quotient.js) record an independently derived 4,608-state quotient with 2,820 reachable states and 94/256 excluded c=0 residue pairs. Its 72-word closure certificate was not Lean-formalized. This draft is weaker than Agent 43's already kernel-checked 24³ quotient and is **not** the preferred formalization target.

Agent 43's certificate is documented in [M16.md](../agent43-c-quotient-kernel/M16.md); successful manual CI [41412951906](https://github.com/FlareZ123/bb6/actions/runs/41412951906) compiled its original-source bridge, with 7,115 reachable quotient states and 34,992 representative edges. The detailed pullback is in [M16HighFamily.md](M16HighFamily.md). It identifies a new high-side candidate family
`m≥3, m mod4=3, j≥3, j mod8=(m+3) mod8`
whose c=0 quotient images lie among four absent abstract states, while the current full highAllowedValSixFull gate admits the family. The arithmetic pullback is established here. The direct source proof is drafted in [M16StopFamilyExclusions.lean](M16StopFamilyExclusions.lean); it reuses the already checked generic bridge rather than duplicating it. Its targeted compile is pending. The m=0 classes j mod16∈{2,3,11} are already direct corollaries of the certificate's source-bridged reset_unreachable16 theorem.

The low-family c=0 residues excluded by the 24³ quotient are m mod16 in {1,4,5,7,9,12,13,14}. The actual `jointLowAllowed` predicate in `JointRootQuantifier.lean` excludes m mod8=4 (hence residues 4 and 12), m mod16=14, and several higher-modulus classes whose residues mod16 are 8 or 6; `lowAllowedValSixFull` additionally excludes m mod128=0. It does **not** exclude the five classes {1,5,7,9,13}. The earlier sentence in this README claiming those classes were already covered was incorrect. The new module [M16StopFamilyExclusions.lean](M16StopFamilyExclusions.lean) proves direct original-CLine nonreachability for all five progressions and for the general high family, using the existing `CCert.source_reachable_embeds16` and `CCert.reachable_seen` bridge. The targeted manual workflow [agent13-m16-high-family-interface.yml](../../.github/workflows/agent13-m16-high-family-interface.yml) is the compile gate; until it passes, these new source theorems remain drafts. They are infinite target-family exclusions, not a decision of the residual existential or of BB(6).
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


## M32 high quotient integration into CThreeSix (2026-11-23)

The M16 line is superseded by the stronger B8/M32 source quotient. In particular, the proposed M16 low residues are already excluded by the current Agent11 low sieve, and the illustrative M16 high progression `m=3, j=8r+6` is also caught by the newer `sixForcedExcluded` filter. The failed `M16StopFamilyExclusions.lean` draft was not a proof and must not be cited as one.

The stronger M32 certificate is generated by `tools/agent43_c32_certificate.py` and its high-parameter census by `tools/agent4_c32_high_census.py`. The reproducible census reports:

- 31,570 reachable abstract states out of 64,000, with 189,834 quotient edges;
- 492 forbidden high parameter residue pairs out of 1,024;
- 432 pairs are the M16 lift, with 60 additional M32 pairs (24 previously explicit and 36 further pairs).

Agent 4's `HighSource.lean` proves the generic original-source theorem `high32_forbidden_source`. The new integration module `CThreeSixM32Integration.lean` imports that theorem together with `M32SectionEmbedding` and `CThreeSixAllCriterion`. It defines `highAllowedM32` by adding
`(3 <= j and 2 <= m) -> not CCert.highPairGood (j % 32) (m % 32)`
to the existing high gate, and proves `blank_halts_iff_six_m32`. The low branch is unchanged because the `m % 32 = 24` low family is already covered by the existing low source sieve. It also proves the infinite source exclusion for `j % 32 = 0, m % 32 = 13`.

A finite comparison of the M32 high mask with `sixForcedExcluded` found eight M32-forbidden residue pairs not caught by that filter:
`(0,13), (4,25), (8,5), (12,17), (16,29), (20,9), (24,21), (28,1)`.
They have the compact description `j % 4 = 0` and `m % 32 = (3*j + 13) % 32`; their target residues satisfy `x % 8 = 3`, `k % 8 = 4`, and `(x+k) % 8 = 7`, so none of the six forced inverse gates fires. This overlap comparison is a computational residue audit; a separate Lean lemma formalizing the non-overlap is still desirable. The M32 source exclusion itself is kernel-backed by `high32_forbidden_source`.

**Integration status:** the M32 source certificate was previously kernel-checked. The new exact CThreeSix integration is awaiting its combined Lean 4.36.0-rc2 CI run (workflow `.github/workflows/agent4-c-m32-high.yml`, run `45188944119`). The preceding attempt failed only because the historical P32Block artifacts were absent; the workflow now regenerates and compiles all 40 proof blocks from source before compiling the integration.


Follow-up formalization: `CThreeSixM32Integration.lean` now also contains `sixForced_not_excluded_0_13`, a Lean lemma proving that the entire `j%32=0, m%32=13` high family is not rejected by `sixForcedExcluded`. The broader eight-cell overlap derivation is in [M32SixForcedNonOverlap.md](M32SixForcedNonOverlap.md); the full eight-cell mask intersection remains a finite computational audit pending a compact Lean enumeration.

The original single-run source recompilation of all 40 M32 blocks was cancelled as inefficient. Instead, the existing eight-shard Agent43 workflow is being used to regenerate independently kernel-checked proof-block artifacts. Its artifact retention was increased from 3 to 90 days. Current artifact-producing run: `45190788952`; shard 0 has uploaded successfully and the other seven shards were still compiling at the last checkpoint. The Agent4 integration workflow is configured to download the 40 artifacts from this run and then compile the CThreeSix closure plus the integration module.
