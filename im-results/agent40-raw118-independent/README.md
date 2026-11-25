# Raw118: independent counters and periodic phase graphs

## Accepted source-level result

For each of the ten exact partial tables in `independent.py`, every compatible physical completion is nonhalting from blank. The original-source Lean verification and axiom guard passed in [run 45600114599](https://github.com/FlareZ123/bb6/actions/runs/45600114599).

The section invariant is state F, empty left zipper, right zipper (0^{4+a}1^{1+b}) for arbitrary independent naturals a,b. Each table reaches the family in ten steps. Universal positive-cost returns cover all parameters by separating the small b cases and using symbolic sweeps for the remaining range. The counters can reset or decrease independently. `IndependentSweepCore.lean` proves `never_of_closed` using the original zipper-to-raw bridge, and `generate_independent.py` emits the ten certificates.

Zero-based raw118 roster indices: 299, 320, 323, 325, 340, 345, 347, 348, 353, 363. These are exact tables, not representative renamings. Two have two holes and eight have one; the total compatible completion mass is 1,450 assuming the original disjoint residual partition is connected. This dossier does not establish the partition itself.

## Larger phase-graph certificates (source verification pending)

The separate `phasegraph.py` and `generate_phasegraph.py` extend the invariant to finitely many section families, each with its own state, direction, prefix, repeated block, suffix, and minimal repetition count. Every family has an exact universal positive-return arc, together with exact computations for all excluded small values. Arc endpoints are normalized by the proved repeated-word rotation and concatenation identities. The generated Lean statements use `never_of_closed`; the Python discovery and all finite simulations are untrusted.

The 48 targets are listed explicitly in `phase_candidates.tsv`. Local compilation uses copied zipper semantics; original-source verification has been dispatched via the existing manual coverage workflow target `weighted-tnf-raw118-phasegraph`. Do not count these 48 as source-accepted until that run succeeds.

Reproduction: `python generate_independent.py > Raw118Independent.lean`; for the larger proof set, `python generate_phasegraph.py --modules`. The workflow unpacks the original sources and compiles the import closure with `tools/lean_compile_closure.py`.

## Scope

The source parent is `1RB---_1RC---_0RD---_1LD1RE_---0LE_------` (Agent16's raw118 dossier). The independently reproduced 6,085-row open roster has SHA256 `00b82e8ded916fb719ebfd627d29da4bbf86659039b3b7889ff60a3f9ae396f9`. The long weighted halter at index 439 has an existing certified score 756,496. These nonhalting results do not establish a uniform bound for all remaining raw118 completions, a canonical frontier reduction, or the global BB(6) value.
