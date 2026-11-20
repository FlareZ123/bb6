# Correction-only #623 S-indexed reset window

**Status:** reproducible finite diagnostic and an algebraic buffer refinement; not an all-time #623 theorem.

## 1. Drop the terminal term from the window buffer

The prior S-window envelope was

`B_old(ell)=max(34 ell+140, 36 ell+88)`.

Agent 1's exact weighted-correction formalization gives, for the drain statistics (D=L-2E), (E\le R\le L),

- `correction_buffer_closed`: `|C|,|F| ≤ 34L+122`;
- `one_extra_digit_carry_bound_closed`: the boundary carry quotient remains in `[-1,1]` even when the correction has magnitude exactly (K).

The branch drain input satisfies (b\le q+3\le S+3\le\tau(\ell_S)=(3^{\ell_S}-1)/2). Thus (2b-1<3^{\ell_S}), and the parity-correct drain length condition (3^{L-1}\le2b-1) forces (L\le\ell_S). The carry buffer therefore needs only

[
B_{corr}(\ell_S)=34\ell_S+122.
]

The former second term (36\ell_S+88) was used to turn central-block nonmonochromaticity into the branch-selection inequality. It is unnecessary for that implication. The current source-derived branch data in `im-results/agent32-623-phase-automaton/BranchSelection.lean` give

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

It also sharpens the terminal-strip contradiction. The sector-specific terminal h bounds in `RootRayGapCocycle.md` (from the TerminalRatio4 branches with K=n+6) are
[
|h|\le6n+44\ (LO),\quad |h|\le6n+31\ (LE),\quad
|h|\le(6n+19)/2\ (RO),\quad |h|\le(9n+25)/2\ (RE).
]
For the output state's central coordinate (x=2h) in LO/LE and (x=4h) in RO/RE, and (n\le\ell_q\le\ell_S), these imply
[
|x'|\le12\ell_S+88,\ 12\ell_S+62,\ 12\ell_S+38,\ 18\ell_S+50
]
in LO, LE, RO, RE respectively. The largest is (18\ell_S+50<34\ell_S+122=B_{corr}). Thus a terminal successor would have (|x'|<B_{corr}), contradicting the central-block certificate (|x'|>B_{corr}). This is the sector-sensitive reason the uniform (36\ell_S+88=4(9\ell_S+22)) term can be dropped.

Caveat: the combined D/r depth wrapper used in the terminal-window table is still an integration/CI obligation in the repository. Treat this terminal-strip refinement as conditional on that wrapper until it is compiled against the pinned source. The branch-selection inequality and terminal h table both use the combined D/r depth wrapper; neither should be treated as source-CI certified until that wrapper is included in a successful pinned-source run.

Exact source references:

- `im-results/agent1-machine623-3euclidean-correction-bounds/SignedCoordinateNormalForm.lean`, theorems `correction_buffer_closed` and `one_extra_digit_carry_bound_closed`;
- `im-results/agent1-machine623-3euclidean-correction-bounds/DrainDigitTransducerCarry.lean`, which proves the three-state digit transducer and exact weighted output statistics;
- `im-results/agent32-623-phase-automaton/BranchSelection.lean` and `.md`, for (x=2g-\gamma), the threshold (T), and the source-depth bound (|T|\le5\ell+22);
- `im-results/agent49-parity623/TerminalRatio4Source.lean`, for the four original-source terminal-ratio branches;
- `im-results/agent8-623-inverse/RootRayDrainDepthSource.lean`, for the unified full-drain depth package used to bound the terminal-window parameter.
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

## 3. Finite next-state diagnostic

Run from the repository root:

```sh
node im-results/agent48-623-tight-window/tight_mass_window_scan.js
```

The script replays source transitions (D_n\to D_{n+1}) for (n=33,\ldots,10000), and tests the **next-state** S-indexed word (x',y') on ([k_{S'}+2,j_{S'}-2)). DFA acceptance means that an accepting state was visited at least once; the final DFA state need not itself be accepting. The old-envelope first-hit histogram matches the existing `MassWindowResetDiagnostic.md`, which validates the transition indexing.

| Quantity | Old envelope | Correction-only buffer |
| --- | ---: | ---: |
| Source transitions checked | 9,968 | 9,968 |
| Next-state DFA failures | 0 | 0 |
| Minimum word length | 8 | 7 |
| Maximum word length | 16 | 16 |
| First reset end | 3–12 | 3–12 |

More precisely:

- Relative to the old envelope, target (k) decreases by one on 723 transitions and target (j) decreases by one on 1,549 transitions. The old-minus-new histograms are (k: 0\mapsto9245,1\mapsto723) and (j:0\mapsto8419,1\mapsto1549).
- Source-to-target transition-shift histograms:
  - old envelope: ((0,0):9955,(0,1):8,(1,1):5);
  - correction-only buffer: ((0,0):9954,(0,1):9,(1,1):5).
- The correction-only target (r'=j'-3k') histogram is (-2:3027,-1:2844,0:4097).
- The correction-only (r\to r') transition counts are:
  (-2\to-2:3022, -2\to-1:4, -1\to-1:2840, -1\to0:5, 0\to0:4092, 0\to-2:5).
- The first-acceptance histogram for the correction-only buffer is:
  `3:2176, 4:4215, 5:2255, 6:860, 7:298, 8:102, 9:39, 10:14, 11:6, 12:3`.

The finite prefix transitions (n=9,\ldots,32) have the same pass/fail set under both envelopes: passes at 28, 31, 32; failures at 9–27, 29, 30. The main diagnostic therefore establishes 9,968/9,968 next-state windows accepted, with first reset by symbol 12. It does not prove acceptance for every future S-window. The recurrence replay is computational; no original-source root theorem or global BB(6) conclusion is claimed.

## 4. Actual next-state S-window boundary phases

Run:

```sh
node im-results/agent48-623-tight-window/s_window_boundary_phases.js
```

For each source transition (D_n\to D_{n+1}), the tested word belongs to the target state and starts at (k'+2). The script computes the source carry entering (k+1), then consumes source input digits (k+1,\ldots,k'+1) (one or two digits) to obtain the actual transducer phase entering the target word at (k'+2). It validates the source carry convention by recomputing the q-indexed phases and checking exact set equality with `agent32-623-phase-automaton/ActualBoundaryPhases.json`: 262/262 **q-indexed diagnostic** phases match. This is not the S-window phase set; the S-indexed transition inventory below has 1,318 keys.

For the correction-only S-window over the 9,968 source transitions (D_{33}\to D_{34},\ldots,D_{10000}\to D_{10001}):

- 1,318 distinct transition boundary phases, keyed by source sector/branch, target sector/branch, previous input pair, carry, source/target (r), and the ((k,j)) shift;
- 28 distinct previous-pair/carry combinations in L and 37 in R;
- observed start carries are L: ((-2,1),(-1,0),(-1,1),(0,0)); R: ((-3,1),(-2,0),(-2,1),(-1,0),(0,0));
- source sector/branch counts: RO/R 1,643; RE/L 1,304; LO/R 1,304; RE/R 1,632; RO/L 1,293; LE/R 1,293; LO/L 775; LE/L 724;
- target (r') counts: (-2:3027,-1:2844,0:4097);
- zero branch-vs-threshold mismatches, zero violations of the full universal carry rectangles, zero affine-update mismatches, zero transducer digit mismatches on the tested target interval, and zero reset-DFA failures;
- the (D_{38}\to D_{39}) sample has source RO/R, target RE/R, previous pair ((1,2)), carry ((-2,0)), (r=r'=0), and shift ((0,0)). Its drain data are (b=44633,L=11,n_1=5,n_2=1,C=88,F=-24,T=35).

The observed carry pairs are diagnostics only; retain the full universal rectangles L: ([-2,2]\times[-2,2]), R: ([-4,1]\times[-2,2]). The phase inventory is not a closure proof. A finite product still needs the reset-DFA state and the weighted drain/transducer interface. The script writes `SWindowBoundaryPhases.json` when run.

## 5. Post-reset output interface and S-window product diagnostic

Agent 49's corrected reset-pattern construction is available at `im-results/agent49-parity623/ResetPostStateDFA.json` and `reset_poststate_dfa.js`.

The corrected minimal common-reset language has **8,088** minimal words, by witness length:
- length 3: 159;
- length 4: 1,626;
- length 5: 3,087;
- length 6: 3,216.

The earlier 29,445 count is withdrawn: it was an order-dependent DFS overcount with 21,357 redundant candidates. The 263-state recognizer's accepted language is unchanged. The corrected construction uses a 10,480-state Aho trie and validates all 8,088 patterns against 225 L-start and 270 R-start transducer states with zero failures. Direct first-witness selection was checked against all 597,871 words of lengths 0–6 with zero mismatches.

The new finite output interfaces are:
- `post_reset_pair`: 395 DFA states, 54 labels, returning the common L/R post-reset transducer-state pair at the first reset;
- `post_reset_pair_and_length`: 736 DFA states, 186 labels, returning the same pair together with the witness length. The witness's second symbol is recoverable from the rolling last-five buffer at index (6-L) when the witness length (L) is known.

I applied these output DFAs to the 9,968 correction-only S-window target words from the same root replay:
- no word lacked an output label;
- all 54 pair labels occurred;
- first-witness length histogram: (3:5228, 4:3876, 5:761, 6:103).

Combining each 1,318-field S-window transition key with the post-reset label gives the following **finite-trace** product diagnostics. Consecutive product keys are linked in the order of the root replay.

| Output interface | Observed product pairs | Consecutive edges | Nodes with multiple successors | Maximum outdegree |
| --- | ---: | ---: | ---: | ---: |
| 395-state pair output | 8,091 | 9,948 | 1,450 | 8 |
| 736-state pair+length output | 8,890 | 9,958 | 914 | 6 |

The witness-length refinement reduces observed branching, but neither product is a closed transition system: even the refined product has 914 observed nodes with multiple successors. The 1,318 transition keys and the post-reset label alone therefore do not constitute a Markov state. A proof still needs a finite abstraction of the weighted drain/root-language data that determines the next boundary phase.

Reproducibility note: `s_window_boundary_phases.js` now reads Agent 49's `ResetPostStateDFA.json`, populates consecutive S-window phase and post-reset product graphs, and exports their node/edge counts, outdegree histograms, post-reset label distributions, and failure counts in `SWindowBoundaryPhases.json`. The script still records only edges observed along the finite root prefix; it does not enumerate all possible transitions and does not establish all-time closure.

## 6. Next useful use

Agent 32 can compose the 1,318 S-window transition inventory with Agent 49's 395-state/54-label or 736-state/186-label post-reset interface. Prefer the pair+length output when the second symbol must be recovered from the rolling buffer. Preserve the full universal carry rectangles and a finite weighted-drain/root-language interface. The remaining obligation is to prove central x-block nonmonochromaticity for every authentic root state, not merely for the scanned prefix.
