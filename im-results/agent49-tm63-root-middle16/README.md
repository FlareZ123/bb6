# TM63 root continuation through middle 16

**Status: uncompiled source-level composition candidate.** This file connects the current middle-15 root endpoint to Agent 41's new m=2, n=32k+16 counted source row. It does not establish a halting witness or BB(6) value.

## New root arithmetic

At middle 11, the exact root index is

`tm63Index1 = 16*r+15`, where `r = tm63RootResidueSixK = tm63RootMiddleK/2`.

The existing definition is `tm63RootMiddleK = 31*2^(A-3)-1`, with `A = tm63FirstSection.exponent >= 5`. Therefore `4 | 2^(A-3)`, so

- `tm63RootMiddleK ≡ -1 ≡ 3 (mod 4)`,
- `r = tm63RootMiddleK/2` is odd,
- writing `r=2k+1` gives `16r = 32k+16`.

This is the exact residue required by `m2Even_residue16_counted_increment_source`.

## Composed source transition

The middle-15 candidate endpoint from `TM63RootResidueThree.lean` is

`S1(L, 16*r, 2, A15, 0, B15, H15)`.

Agent 41's generic residue-16 source theorem gives the next state

`S1(L, 16*r-1, 1, A15+B15+2, 0, 2^B15-1, H15+5+3*B15)`.

The new `TM63RootResidueSixteen.lean` packages this transition and adds its exact primitive cost to `tm63MiddleFirst15Moves`. The proof explicitly establishes `r` odd and the source theorem's width/positivity hypotheses; it does not assume a finite-tape approximation.

## Dependencies and validation

- `TM63RootResidueThree.lean` (candidate blank-root path through middle 15)
- `M2EvenSixteenQ4Prefix.lean` and `M2EvenResidueSixteen.lean` (Agent 41's candidate source row)
- the shared q4 endpoint and S1 counted-drain dependencies

The new module contains `#print axioms` checks for the root parity lemma and composed root theorem. It has **not** been compiled locally or in CI. The two upstream source branches also remain unverified; do not describe this as an accepted root checkpoint until the current source closure compiles under Lean 4.36.0-rc2 and the exported theorems are free of transitive `sorryAx`.

All material belongs in `im-results/`, not `results/`, until it becomes part of a source-verified mathematical result.