# ABEGraph versus the RouteBlock family: interface comparison

Status: this is a contract-level comparison from the committed reproduction notes. The Lean source files are packed in the respective `.tar.xz.b64` bundles, and their binder-level declarations were not extracted in this invocation. Do not treat inferred type details below as a substitute for `#check` output.

## Shared mathematical core

Both frameworks formalize the same return arithmetic: a successful section return has unary parameter

\[n=3k+a_r \quad\longmapsto\quad n'=8k+c,\]

with the branch residue `a_r` and suffix-dependent output constant `c`. Iterating L certified returns gives the characteristic lift from an input shift by `3^L d` to an output shift by `8^L d`. This is the common mathematical engine, not a reason to maintain two independent production evaluators.

## ABEGraph / ABEReturn

- `ABEReturn.lean`: `a_valid_return` proves a full counted source return for every unary parameter k, assuming a finite `ACert` validity check. Its documented affine output is `n'=8k+2p+3+lead`.
- `ABEGraph.lean`: `edge_sound`, `advance_sound`, and `path_sound` compose exact source returns for any validated finite indexed graph.
- `path_shift` lifts a successful L-edge path `(n,i) → (m,j)` to the path from `n+3^L*d` to `m+8^L*d`, preserving the suffix indices. The README explicitly describes this as not restricted to regular-language suffixes or B/E words.
- Local Lean 4.36.0-rc2 compilation and axiom audit are reported as `[propext, Quot.sound]`, without `sorryAx` or `native_decide`.
- The actual finite graph and blank-origin block computations are not kernel-certified in this package. The 20,000,000-return I9 computation is experimental evidence, not an all-time result.

**Distinct strength:** a graph-parametric source-soundness and full-path affine-lift interface, together with an independently developed A-front return certificate. It is reusable beyond the particular D route graph.

## RouteBlock / RoutePartial / RouteReplayExact / RouteHalt

- `RouteAllFront.lean`: `all_valid_return` and `all_valid_halt` provide arbitrary A/E/B protected-front certificates, exact primitive return times, and terminal F1 certificates.
- `RouteBlock.lean`: `walk_lift`, `arithmeticStep_sound`, `blockReplay_sound`, and `blank_replay` compose certified walks and accelerated replay.
- `RoutePartial.lean`: `arithmeticStep_shift`, `partial_lift_sound`, and `blockPartial_sound` cover partial prefixes and exact early stopping, not only completed paths.
- `RouteReplayExact.lean`: `linearPartial_lift` and `blockPartial_eq_linear` establish exact equality between the accelerated and direct partial arithmetic evaluators for every `n≥2` and suffix.
- `RouteHalt.lean`: `blankBlock_halt` extracts source halting from a positive `blockPartial L 9 []` result, using the source blank-to-I9 prefix at 36 primitive steps.
- `RouteMembership.lean`: `routeTest_iff_path`, `routeTest_mod_invariant`, `small_test_sound`, `graph_mod_halts`, and `root_section_halts` connect executable graph membership to source halting. The current `root_section_halts` is specialized to the A-start `blank` constant.
- `CountedReplay.md` adds generic quadratic-clock block composition and exact partial/terminal lifting.
- The concrete route graph has 107 return layers, 373 edges, 274 vertices, and 1,057,916,215,296 source-certified halting cylinders. Those are prepared-section cylinders, not proof that a genuine blank root enters one.
- The 2^30-return I9 computation is exact computational replay, not an all-time decision.

**Distinct strength:** the D-specific operational pipeline: arbitrary A/E/B fronts, partial/early-stop lifting, exact accelerated/direct evaluator equality, terminal extraction, a checked finite graph, and an exact clock extension.

## Relationship and recommended integration

1. The full-path affine statement `ABEGraph.path_shift` is the natural abstract theorem for arbitrary validated finite graphs. The RoutePartial partial-prefix theorem is stronger in *stopping behavior* for the concrete `Walk` interface; at a completed path it should specialize to the same `3^L→8^L` law. Whether the two graph abstractions are literally interconvertible is the one binder-level question still requiring the packed declarations.
2. Use RouteAllFront + RouteBlock/RoutePartial/RouteReplayExact as the concrete D root-analysis engine. Its A/E/B front coverage and terminal adapter are already connected to the 107-layer graph.
3. Retain `ABEReturn.a_valid_return` as an independent A-front oracle and `ABEGraph.path_sound/path_shift` as the generic graph theorem library. Do not replace the RouteBlock evaluator with a second copy of the ABE arithmetic; use the A proof for differential checking or future graph generalization.
4. The ABE graph package does not currently add a blank-root decision. The RouteBlock package also does not decide the all-time fate of the four authentic roots. The remaining gap is a root-specific all-time phase/return invariant, not another proof of the affine lift.

## Four-root integration point

Agent36's already source-compiled `DAllBlankSource.lean` and `DAllBlankHalting.lean` provide all six D0 blank-start prefixes and all-time halting iff statements. Agent3's `DTableWitness.lean` maps the four designated holdouts to D0 starts A/B/C/F: D0/I9, D3/I5, D2/I15, D1/I39. `RouteMembership.root_section_halts` can be generalized by replacing its fixed `blank` argument with an arbitrary `CryptidBoundary.Cfg`; then the same terminal result can be composed with each source prefix. An `ObsEq` lemma identifying `init (replicate (n-2) true)` with `sect n []` handles any explicit trailing-blank delimiter.

Agent32's universal prepared-F first-event theorem and the source-verified one-sided rank increment bound (A/B output-rank increase at most 2; at most 5 including the newly scanned bit) reduce the remaining task to the sequence of successive F0 sections and exclusion or production of an F1 halt. More bounded replay without a new invariant does not close this gap.