# Authentic root boundary-phase diagnostic

**Status:** exact source-formula replay over the existing root interval (n=33\ldots10000), not an all-time proof.

The boundary carry at the first digit of the moving word was recomputed from the actual signed-coordinate affine corrections, not guessed from the universal carry rectangle.

For each root state:
1. Compute (q,g), sector (s\in\{LO,LE,RO,RE\}), (x=2g-\gamma_s), (y=6q).
2. Select output branch L iff (g>0), using the conditional branch-selection lemma.
3. Set drain parameter (b=q+3,q+2,q-1,q+1) in sectors LO,LE,RO,RE respectively.
4. Compute the parity-correct drain length (L\equiv b\pmod2), (3^{L-1}\le2b-1<3^{L+1}), (N=(2b-1+3^L)/4), and its ternary digit counts (n_1,n_2).
5. Use the source correction table in `SignedCoordinateNormalForm.md` / `DrainDigitTransducer.md` to obtain (C,F).
6. With (K=3^k>B(\ell)), compute the exact carry entering digit (k+1):
   - L: (a=\lfloor(x_{<k+1}-3y_{<k}+C)/3^{k+1}\rfloor), (b=\lfloor(3y_{<k}+F)/3^{k+1}\rfloor).
   - R: (a=\lfloor(-x_{<k+1}-3x_{<k}-3y_{<k}+C)/3^{k+1}\rfloor), (b=\lfloor(3x_{<k}+3y_{<k}+F)/3^{k+1}\rfloor).
7. The previous digit pair is ((x_k,y_k)).

## Results

- **9,968** root states processed (indices 33 through 10,000).
- **262** distinct complete phases when sector, output branch, previous digit pair, and actual carry pair are included: 114 L phases and 148 R phases.
- Ignoring sector, there are 30 distinct L and 40 distinct R ((\text{previous pair},\text{carry pair})) states.
- Actual carry pairs observed:
  - L: `(-2,1), (-1,0), (-1,1), (0,0)`.
  - R: `(-3,1), (-2,0), (-2,1), (-1,-1), (-1,0), (-1,1), (0,0)`.
- Maximum absolute carry coordinate: 2 for L, 3 for R.
- The affine update reconstructed from these (C,F) values agrees with the exact high-level root recurrence at every processed state; sector transitions also agree at every state. No actual phase leaves the full universal carry rectangles.
- The raw unconstrained reset-language counterexample starts ((00,-2,-2)) for L and ((00,-4,-2)) for R are absent from these observed authentic boundary phases.
- The phase alone is not a deterministic transition state: among the 262 observed phases, only 12 have one observed successor, 19 have two, and 231 have three or more (maximum 25). A useful next phase must retain additional word/drain information.

The index-38 RO/R witness reproduces the independently recorded actual phase ((x_k,y_k)=(1,1)), carries ((-2,0)), with (q=44634), drain parameter (44633), parity-correct (L=11), (N=66603), (n_1=5,n_2=1), and corrections (C=88,F=-24).

Machine-readable phase list and counts: [ActualBoundaryPhases.json](ActualBoundaryPhases.json).

## Interpretation

The universal 225/270-state rectangles remain necessary for proving that a common reset word synchronizes every possible transducer start. The authentic root itself uses a much smaller observed boundary-phase subset. The raw nonclosure witnesses do not falsify the root orbit: their starting carries are absent from this observed subset, and their input words are unconstrained.

This is a candidate phase set extracted from a finite interval. It is not yet proved invariant. The observed phase-to-phase relation has substantial branching, so sector + previous pair + actual carry is not enough. The next step is to compose the 263-state reset recognizer with the actual drain transducer phase and moving-window shift, then test whether that augmented state closes.


**Coordinate convention:** this extraction uses the branch-selector coordinate (g=p-3q) from `RootRayGapCocycle.md), with (x=2g-\gamma_s). It is not using the separate ratio-four gap (p-4q) plotted in Agent 8's `RootGapScaleDynamics.md`. The terminal distance is (h=g-9,g-5,(g-1)/2,(g-2)/2) by sector, so (x=2h) on LO/LE and (x=4h) on RO/RE.
