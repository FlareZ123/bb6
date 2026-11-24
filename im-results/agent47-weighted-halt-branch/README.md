# Weighted TNF early-halt margins and read-one regression

This is an intermediate proof aid for the global weighted-TNF certificate. It is deliberately under `im-results/`: it does not determine BB(6), close the first-one cylinder, or improve the universal bound.

## Reusable six-state margin lemmas

`WeightedReadOneHalt.lean` proves three wrappers around the existing weighted-TNF soundness results:

- `first_hole_weighted_halt_of_margin`: if a first hole is reached after (n) ordinary moves and (n+6\le B), its halt child satisfies `WeightedBound B`.
- `first_hole_tnf_cover_of_margin`: the same margin discharges the halt branch of a complete first-hole TNF expansion; callers still supply every ordinary-child proof.
- `last_hole_sound_of_margin`: the same margin discharges a last-hole node when all other rows are ordinary.

The proof uses only the exact finite domain of `possibleDelays`: every possible delay belongs to `List.range 6), hence is at most five. It avoids re-enumerating the delay set at every early node.

## Read-one regression

The parent partial table has A/0 = 1RB and B/0 = 0LA, with A/1 as its first hole. Assigning A/1 = halt gives `readOneHalter`.

The formal results establish:

1. Every compatible completion of `readOneHalter` halts after two ordinary moves, so it is a `Cover (DecidedBelow 3)`.
2. Its possible incoming zero-prefix delays are exactly `[0, 1, 2, 3, 4, 5]`. The five-step path is F→E→D→C→B→A; the one-step path B→A is already forced.
3. Consequently, the weighted halt-branch threshold is exactly (B\ge8), not (B\ge3).
4. A compatible completion can be re-rooted along the one-step zero prefix to produce a genuine four-step blank-start halter. Thus the raw score-three cover is not a weighted-bound-three leaf.

This is a concrete regression against confusing raw blank-start time with the weighted score needed after re-rooting.

## Verification

The manual workflow target `weighted-halt-branch` compiles the full weighted first-write source closure and this file using Lean 4.36.0-rc2.

- Successful run: [45389596381](https://github.com/FlareZ123/bb6/actions/runs/45389596381)
- The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound` for the generic wrappers and read-one theorems; no `sorryAx` appears.

The local result is source-connected through the existing `WeightedTNFCertificate` and `BlankDelaySource` imports. It is not an upper-bound certificate for the full first-one cylinder.


## Importing complete nonhalting machines

`WeightedNonhaltLeafAdapter.lean` adds a generic adapter for an existing full-machine nonhalting proof:

- `forgetHaltRows m` retains every ordinary row and makes every halting row unassigned.
- Its canonical `weightedTNFDefaultCompletion` is definitionally equal to the original complete machine (m).
- If (m) never halts, its sparse known run is defined at every finite time. The existing `weightedTNFKnownRunForever_iff` theorem then proves that every compatible completion of the erased table also never halts.
- `forgetHaltRows_nonhaltCertificate` packages this as a `WeightedTNFCertificate B ... 6` for any 1RB-rooted nonhalting machine, without changing the certificate inductive type.

The adapter passed the Agent13 weighted source-closure workflow [run 46](https://github.com/FlareZ123/bb6/actions/runs/45391368847), with no `sorryAx`.

`CryptidsWeightedLeaves.lean` instantiates the adapter for the six pinned Cryptids nonhalting machines using their existing `literal_r1_never` through `literal_r6_never` proofs. The combined upstream-source/weighted-TNF build is being checked in [shared-source run 46](https://github.com/FlareZ123/bb6/actions/runs/45391698785).

These are standalone certificates for the erased-row cylinders. They do not, by themselves, prove that those cylinders are descendants of a particular canonical first-hole expansion tree; that requires a refinement-path argument or a separate cover/graft composition.


### Exploratory Cryptids run-support trace

`simulate_cryptids_first_visits.py` parses the six pinned RLE definitions and deterministically records first visits to state/symbol rows. The current trace visits all 11 ordinary rows before the unique halt row for each machine, after respectively 53, 36, 39, 16, 23, and 63 moves.

This is reproducible computational evidence, not a Lean theorem and not a proof of a canonical TNF refinement path. It suggests that the erased-row leaves may be reached after the corresponding sequence of first-hole refinements; formalizing that path remains open.
