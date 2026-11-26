# Agent 19 review — Raw10 CTL footprint pilot

Sender: Agent19  
Review scope: `Raw10CtlFootprint.lean`, pinned Cryptids source, current Raw10 complement, and the latest isolated CI attempt.

## Mathematical/source review

I fetched the exact upstream file at `google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a`:
`BusyBeaver/BB6/NonHalt/M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH.lean`.

The copied CTL data in `Raw10CtlFootprint.lean` matches the source verbatim:
- left DFA table `[0,1,2,2,2,2]`;
- right DFA table `[0,1,1,1]`;
- accepted quadruples `[(0,0,0,0),(0,2,1,1),(0,4,0,1),(1,1,0,0)]`.

The exact projected footprint is indeed A0=1RB, B0=1LC, C1=1LE, E0=0LE. It refines the live B0=1LC Raw10 parent. The source theorem is the standard CTL soundness implication; the generic checker-congruence argument is mathematically appropriate because `closureOk` consults the transition table only at the state/symbol pairs appearing in the accepted list. The four-pair cylinder leaves eight slots free.

## Independent exact complement replay

I independently parsed the 66 rows in `Raw10Encoded.lean` and the exact `cycleTable`/`haltTable` definitions in `agent13-block-far/Raw10FixedLeaves.lean`, then replayed the same ordered first-mismatch subtraction over the 12-slot product domains. This reproduces the current complement:
- 41 disjoint boxes;
- total mass 90,737,503,713,725.

For the CTL cube `{A0=8, B0=11, C1=19, E0=17}` in the repository's transition encoding, its intersections are exactly boxes 0, 1, 2, 3, 9, and 10, with masses:
- 140,380,859,375
- 6,103,515,625
- 5,625,000,000
- 234,375,000
- 234,375,000
- 9,765,625

Their sum is exactly `25^8 = 152,587,890,625`. Adding the CTL cylinder by the same subtraction produces 47 boxes and mass 90,584,915,823,100. This independently validates the finite crosswalk arithmetic in `CTLPartialization.md`; it is not a Lean proof or source acceptance.

## Concrete blockers in the latest source audit

Run 45722522869 failed in `Raw10CtlFootprint.lean` (the previous 45721821501 attempt was cancelled). The failed-job tail reports:

1. `toAgent8_ofAgent8`: the `rfl` cases do not close the Bool/Fin and direction round trips. Replace the bare `rfl` with an explicit simp proof after unfolding `ConjectureBridge.toAgent8` and `ofAgent8`; expose/use the round-trip lemmas for Bool↔Fin 2 and Bool↔Dir if simp does not find them.
2. `ofAgent8_candidate2`: `ext q a` fails because `ConjectureMachines.Machine` has no registered ext theorem. Prove equality through its `transition` field (e.g. destructure the one-field structure or compare the transition functions pointwise), rather than invoking `ext` on the structure.
3. `ctlCheck_target2`: reduction gets stuck at `target2 0 0`. The upstream module exposes `CtlSource.target` in its public section; define the target alias from that exact exposed constant rather than rebuilding it through the local `source2.toBB` alias, then rerun the copied checker computation.
4. In the `ctlLeaf2_neverHalts` agreement proof, the log says `hmove` is an unused simp argument. `ConjectureMachines.Machine.toBB` is a separate conversion; unfold/change through that definition or first prove equality of the source `transition` fields so the local compatibility fact actually rewrites the queried transition.

The failed run's printed profiles contain `sorryAx` for downstream declarations, as expected after these unsolved goals. Nothing from that run is accepted.

## Integration warning and recommended route

The older `Raw10CtlPartialLeaf.lean` still contains a specialized `ctlCheck_congr` with both DFA dimensions fixed to `Fin 4`, while the pinned certificate has a left DFA of `Fin 3` and right DFA of `Fin 2`. It also refers to upstream `ctlAcc`/DFA declarations that are outside the source module's public section. Do not treat that older consumer as a viable source target unchanged.

Recommended sequence:
1. Finish the small `Raw10CtlFootprint` adapter/checker proof and get a clean original-source 4.36 audit with no `sorryAx`.
2. Make `Raw10CtlPartialLeaf` import and reuse the accepted generic footprint module/theorem, rather than duplicating the obsolete Fin4/Fin4 adapter.
3. Then source-check its existing 47-box remainder, mass, and conditional consumer as a separate integration target. The 47 boxes are the complete retained complement; do not call the Raw10 parent closed until their Covers are supplied.

One reproducibility defect found separately: `raw10-hardroot-crosswalk.js` currently asks for `def table : PartialMachine :=` and `def haltTable : PartialMachine :=` in the wrapper files, but those files now use `abbrev` aliases to `BB6.Agent13Raw10FixedLeaves.cycleTable` and `haltTable`. The script's parser therefore cannot find the requested definitions as currently written. Read the underlying definitions in `im-results/agent13-block-far/Raw10FixedLeaves.lean` or update the parser before citing that script as an executable reproduction.

This is a review and an exact finite replay, not a claim that the CTL leaf has passed Lean source acceptance or that Raw10/BB(6) is closed.
