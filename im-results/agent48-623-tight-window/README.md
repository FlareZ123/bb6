# Correction-only #623 S-indexed reset window

**Status:** reproducible finite diagnostic and an algebraic buffer refinement; not an all-time #623 theorem.

## 1. Drop the terminal term from the window buffer

The prior S-window envelope was

`B_old(ell)=max(34 ell+140, 36 ell+88)`.

Agent 1's exact weighted-correction formalization gives, for the drain statistics (D=L-2E), (E\le R\le L),

- `correction_buffer_closed`: `|C|,|F| ≤ 34L+122`;
- `one_extra_digit_carry_bound_closed`: the boundary carry quotient remains in `[-1,1]` even when the correction has magnitude exactly (K).

Since the mass depth gives (L\le\ell_S), the carry buffer needs only

[
B_{corr}(\ell_S)=34\ell_S+122.
]

The former second term (36\ell_S+88) was used to turn central-block nonmonochromaticity into the branch-selection inequality. It is unnecessary for that implication. The existing source-backed branch data in `im-results/agent32-623-phase-automaton/BranchSelection.lean` give

[
x=2g-\gamma,\quad |\gamma|\le18,\quad |T|\le5\ell_q+22,
]
with (q=\min(a,d)\le S=a+d), hence (\ell_q\le\ell_S).

If the central x-block is nonmonochromatic, the middle-block certificate gives (|x|>B_{corr}(\ell_S)). Therefore

[
2|g|=|2g|\ge|x|-|\gamma|
>34\ell_S+122-18
=34\ell_S+104,
]
so
[
|g|>17\ell_S+52>5\ell_S+22\ge|T|.
]

Thus the exact output-side test (g\ge T) reduces to the sign test (g>0), and its complement to (g<0), without requiring the extra (36\ell_S+88) term. The correction-only buffer is enough both for the source carry rectangle and for the conditional branch-selection step. This does not prove the central x-block property; that remains the core phase-invariant obligation.

Exact source references:

- `im-results/agent1-machine623-3euclidean-correction-bounds/SignedCoordinateNormalForm.lean`, theorems `correction_buffer_closed` and `one_extra_digit_carry_bound_closed`;
- `im-results/agent1-machine623-3euclidean-correction-bounds/DrainDigitTransducerCarry.lean`, which proves the three-state digit transducer and exact weighted output statistics;
- `im-results/agent32-623-phase-automaton/BranchSelection.lean` and `.md`, for (x=2g-\gamma), the threshold (T), and the source-depth bound (|T|\le5\ell+22);
- `im-results/agent41-623-3euclidean/MonotoneMassWindow.md`, which proves (\ell_{S'}-\ell_S\in\{0,1\}).

## 2. Sharper moving-window shift

Now (B=34\ell_S+122). Since (S\ge20), (\ell_S\ge4), so (B\ge258). From (\ell_{S'}-\ell_S\in\{0,1\}),

[
B'=34\ell_{S'}+122\le B+34.
]

As (B\ge144), (4(B+34)\le5B), and therefore

[
(B')^3\le(B+34)^3\le\frac{125}{64}B^3<3B^3.
]

With (3^j>B^3), this yields (j'\le j+1); monotonicity (B'\ge B) yields (j'\ge j). Likewise (B'\le B+34<3B) gives (k'-k\in\{0,1\}). Hence

[
\boxed{k'-k\in\{0,1\},\qquad j'-j\in\{0,1\}.}
]

Moreover, (k'-k=1) forces (j'-j=1): if (k'=k+1), minimality gives (B<3^k\le B'<3^{k+1}), so (B^3<3^{3k}\le(B')^3), hence (j\le3k<j'). Since (j'\le j+1\le3k+1), necessarily (j=3k) and (j'=3k+1).

Minimality of (k) also gives (3^{k-1}\le B<3^k), hence (j\in\{3k-2,3k-1,3k\}). The phase (r=j-3k\in\{-2,-1,0\}) has only these possible transitions:

- (-2\to-2) or (-2\to-1);
- (-1\to-1) or (-1\to0);
- (0\to0) or (0\to-2).

Thus the next required interval ([k'+2,j'-2)) contains the old output subinterval ([k+3,j-2)), with at most one low-symbol shift and one high-symbol extension. The coupled window-index phase has only three possible transition types: ((0,0),(0,1),(1,1)).

These are paper derivations from the cited source lemmas and exact window definitions, not new Lean theorems in this directory.

## 3. Finite diagnostic

Run from the repository root:

```sh
node im-results/agent48-623-tight-window/tight_mass_window_scan.js
```

The script uses the existing 263-state DFA at `im-results/agent32-623-phase-automaton/ResetPatternDFA.json` and the same explicit JavaScript transcription of the #623 high-level recurrence as `synchronizing_word_scan.js`. It recomputes the S-indexed windows for root indices 33 through 10,000 using both the old envelope and (B_{corr}), and checks next-state shifts.

Observed output:

| Quantity | Old envelope | Correction-only buffer |
| --- | ---: | ---: |
| States checked | 9,968 | 9,968 |
| DFA failures | 0 | 0 |
| Minimum word length | 8 | 7 |
| Maximum word length | 16 | 16 |
| First reset end | 3–12 | 3–12 |

More precisely:

- Relative to the old envelope, (k) decreases by one on 723 states and (j) decreases by one on 1,550 states.
- Actual transition-shift histograms:
  - old envelope: ((0,0):9955,(0,1):8,(1,1):5);
  - correction-only buffer: ((0,0):9954,(0,1):9,(1,1):5).
- The correction-only (r=j-3k) transition counts are:
  (-2\to-2:3022, -2\to-1:4, -1\to-1:2840, -1\to0:5, 0\to0:4092, 0\to-2:5).
- The first-acceptance histogram for the correction-only buffer is:
  `3:2176, 4:4215, 5:2255, 6:860, 7:298, 8:102, 9:39, 10:14, 11:6, 12:3`.

The finite diagnostic therefore survives the strictly smaller correction-only buffer, with 9,968/9,968 windows accepted and first reset by symbol 12. It does not prove that the reset DFA accepts every future S-window. The recurrence replay is computational, and no original-source root theorem or global BB(6) conclusion is claimed.

## 4. Next useful use

Agent 32 can use (B_{corr}=34\ell_S+122) and the three-state coupled shift phase in the finite product-state closure. Preserve the full carry rectangles, source branch/sector, weighted drain interface, and the low/high boundary state. The remaining obligation is to prove central x-block nonmonochromaticity for every authentic root state, not merely for the scanned prefix.
