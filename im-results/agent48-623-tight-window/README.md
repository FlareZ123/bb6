# Correction-only #623 S-indexed reset window

**Status:** reproducible finite diagnostics, an algebraic buffer refinement, and an exact weighted-mass drift identity for canonical transitions; not an all-time #623 theorem.

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

**Verification status (2026-11-20):** The pinned-source run `44603152399` failed in `Agent1ComplementBufferSource.lean` before reaching the later `RootRayDrainDepthSource.lean` step. Therefore that run does **not** certify the four-sector full-drain D/R depth package. The combined mass-indexed S-window shift in `MonotoneMassWindow.md` remains an algebraic derivation, not a single source-imported Lean theorem; the depth wrapper and combined consumer still need a successful pinned-source compile.

The S-window phase inventory and reset-product closure also remain finite diagnostics. Do not treat the complete moving-window/reset argument or authentic-root nonhalting as proved.

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

A buffer/event-relative quotient is also available at `im-results/agent48-623-tight-window/ResetPostStateDFA_BufferRelative.json`:
- pair-only: **349 states / 8 labels**, where labels are the joint L/R carry profiles;
- pair+length: **580 states / 30 labels**, where labels are joint carry profile plus witness length.

This quotient drops `previous_pair). The output sink is absorbing, so at the first transition into an output state the current input symbol is exactly `previous_pair`; the consumer can recover it at that event. The pair+length interface also retains (L), so the second witness symbol is recovered from the rolling last-five history at index (6-L). Use these compressed interfaces only when the product retains the current symbol at the first output event (and the rolling history for pair+length); otherwise retain Agent 49's full 54/186-label machines. The quotient was checked against the original output machines on all 597,871 words of lengths 0–6: zero output mismatches, zero previous-pair recovery mismatches, and zero second-symbol recovery mismatches. The verifier seeds the rolling five-symbol buffer with two preceding placeholders, so the witness's second symbol is always at index (6-L) when the first reset is found.

The state maps in the JSON are quotient certificates. Re-run the state-by-state transition/output checker and exhaustive short-word check with:

```sh
node im-results/agent48-623-tight-window/verify_buffer_relative_postreset.js
```

Agent 49's factorization explains the quotient: the 54 full pair labels comprise 9 previous pairs and 8 global joint carry profiles; for each fixed previous x digit, exactly 6 profiles occur, independently of the previous y digit.

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

Reproducibility note: `s_window_boundary_phases.js` now reads Agent 49's `ResetPostStateDFA.json`, populates consecutive S-window phase and post-reset product graphs, and exports their node/edge counts, outdegree histograms, post-reset label distributions, and failure counts in `SWindowBoundaryPhases.json`. The script currently uses Agent 49's full output labels; the buffer-relative quotient is a separate artifact and has not yet been added to that script. It records only edges observed along the finite root prefix; it does not enumerate all possible transitions and does not establish all-time closure.

## 6. Exact weighted-mass drift on canonical transitions

The signed-coordinate normal form gives a branch-independent update
\[
w'=w-q+A,\qquad A=-D-2R+c_A,
\]
where \(q=\min(a,d)\), \(D=L-2n_2\), and \(R=n_1+n_2\) is the **full** evaluator-call count (including the initial evaluator in RE). Here \(L\) is the full drain digit length and \(n_1,n_2\) count its ternary output digits 1 and 2. In particular,
\[
D+2R=L+2n_1.
\]

A useful potential is
\[
P(a,d)=-w+q+3\mathbf 1_{\{s=LO\}}
=\begin{cases}
a+2d-6,&LO,\\
a+2d-5,&LE,\\
d+2a-1,&RO,\\
d+2a-2,&RE.
\end{cases}
\]
The output orientation and the source parity table determine the next sector:
\[
LO\xrightarrow{L}LO,\quad LO\xrightarrow{R}RO,\quad
LE\xrightarrow{L}LE,\quad LE\xrightarrow{R}RE,
\]
\[
RO\xrightarrow{L}LE,\quad RO\xrightarrow{R}RE,\quad
RE\xrightarrow{L}LO,\quad RE\xrightarrow{R}RO.
\]

Combining \(w'=w-q+A\) with this sector map gives the exact drift
\[
P'-P=q'+L+2n_1+\kappa_{s,\sigma},
\]
where \(q'\) is the next state's smaller counter and \(\sigma\) is the output orientation:

| Input sector | Output | Next sector | \(c_A\) | \(\kappa=-c_A+3(\mathbf 1_{s'=LO}-\mathbf 1_{s=LO})\) |
|---|---|---|---:|---:|
| LO | L | LO | -9 | 9 |
| LO | R | RO | -17 | 14 |
| LE | L | LE | -6 | 6 |
| LE | R | RE | -9 | 9 |
| RO | L | LE | 0 | 0 |
| RO | R | RE | -3 | 3 |
| RE | L | LO | 3 | 0 |
| RE | R | RO | -5 | 5 |

Thus every valid canonical transition with a nonempty drain satisfies
\[
\boxed{P'\ge P+q'+1.}
\]
This is independent of whether the exact output-side threshold is simplified to \(\operatorname{sign}(g)\): both possible orientations are covered. It proves strict growth of this weighted mass and rules out cycles wholly contained in the canonical four-sector regime. Since \(a+d-6\le P\le\frac32(a+d)\), strict growth of \(P\) forces the counter mass \(a+d\) to be unbounded along any infinite orbit that remains in this regime.

**Scope:** this is an algebraic consequence of the existing \(w\)-update/correction table in [SignedCoordinateNormalForm.md](../agent1-machine623-3euclidean-correction-bounds/SignedCoordinateNormalForm.md) and the output-parity sector map in [RootRayGapCocycle.md](../agent1-machine623-3euclidean-correction-bounds/RootRayGapCocycle.md). The new potential identity has not itself been added as a Lean theorem. It does not prove that the authentic root remains in the canonical regime, exclude entry into a halting/low-gap branch, or establish nonhalting. Its value is as a compact monotone size invariant once the canonical transition hypotheses are available.

## 7. Arbitrary-word actual affine output bridge

`SourceCarryAffineBridge.lean` now contains a generic interface for arbitrary source-pair word lengths, not only the fixed 01,00,00 example:

- `leftSourcePairs` and `rightSourcePairs` describe the source digit-pair stream at an arbitrary boundary. The L stream accounts for the one-place y offset; the R stream retains the previous x/y pair.
- `leftCarryOutputPairs` and `rightCarryOutputPairs` are the full pair-output recursions of the L/R carry transducers.
- `left_carry_output_pairs_matches_affine` and `right_carry_output_pairs_matches_affine` identify every finite pair-output prefix with the Euclidean ternary digit pairs of the corresponding affine output tails.
- `left_actual_affine_carry_pairdigits` and `right_actual_affine_carry_pairdigits` specialize this to the actual successor coordinates using the existing boundary quotient identities. This is the pair-stream bridge needed to feed the *actual* successor window into the next reset recognizer.
- The x-only projections `leftCarryXOutput`/`rightCarryXOutput`, together with `left_actual_affine_drop_first_nonmono`/`right_actual_affine_drop_first_nonmono`, transfer the shift-aware nonmonochromatic-suffix condition to the actual successor x-coordinate.

The length parameter is arbitrary, so reset words of lengths 3--6 are covered; any shifted reset offset is handled by using the corresponding larger boundary scale (K_s=3^sK). The L source-pair alignment is deliberately offset: the initial previous-y digit is (Y\bmod3), while the first current pair is ((X\bmod3,(Y/3)\bmod3)). R starts with previous pair ((X_0\bmod3,Y_0\bmod3)), with (X_0/3=X) from nested Euclidean division.

### Join to Agent49's 66-state paired carry closure

The 54 `full_dfa_output_labels` in `agent24-machine623-shifted-reset-product/SourceCarryResetProduct.json` match the 54 seed states in `agent49-parity623/PostResetCarryPairClosure.json` exactly: all 54 have the same previous pair, L carry ((a,b)) with (b=0), and R carry pair. A direct finite join check found 54/54 matches, with no previous-pair or L-y-carry mismatches.

This explains the compact state encoding in `PostResetCarryPairInvariant.lean`: after reset, the L y-carry is zero and remains zero under every digit pair, while the L x-carry and full R x/y carry are represented by `la` and `ra`. Its `allowed_runWord_closed` theorem then gives a 66-state paired carry closure for every finite suffix. Combined with the full pair-output bridge above, this is the right finite carry layer for the next-window composition. The output-map proof design and exact carry interpretation are recorded in [PostResetCarryOutputMap.md](PostResetCarryOutputMap.md). The remaining proof obligation is to connect the DFA's output labels and pair-output map formally, then establish the authentic root-language/phase closure; the 66-state carry closure alone does not establish that.

**Finite arithmetic regression (not proof):** 5,000 deterministic pseudorandom signed cases per branch, with (K\in[1,2000]), (x,y\in[-200000,200000]), (C,F\in[-2000,2000]), and prefix length 1--16, produced zero mismatches between the full pair transducer stream and the direct affine quotient digits. Seed: `0x51a7babe`.

**Proof status:** these are source-level Lean additions, not yet compile-verified. The local shell/Python tool boundary failed even for trivial commands in this invocation, and the repository's local-preflight rule forbids substituting CI. Do not cite these new declarations as kernel-checked until another run compiles the exact file and dependency closure at the pinned Lean version. The remaining glue is to identify the finite automaton's emitted pair-output list with `leftCarryOutputPairs`/`rightCarryOutputPairs` on the corresponding source-pair word, then import the finite robust-reset certificate and prove the all-time shifted-window closure.

## 8. Next useful use

Agent 32 can compose the 1,318 S-window transition inventory with either Agent 49's full 395-state/54-label or 736-state/186-label interface, or the buffer-relative 349-state/8-label and 580-state/30-label quotients. Prefer the compressed pair+length output when the product retains the current symbol at the first output event and the rolling last-five history; otherwise use the full pair+length interface. Preserve the full universal carry rectangles and a finite weighted-drain/root-language interface. The remaining obligation is to prove central x-block nonmonochromaticity for every authentic root state, not merely for the scanned prefix.


Agent 32 can compose the 1,318 S-window transition inventory with either Agent 49's full 395-state/54-label or 736-state/186-label interface, or the buffer-relative 349-state/8-label and 580-state/30-label quotients. Prefer the compressed pair+length output when the product retains the current symbol at the first output event and the rolling last-five history; otherwise use the full pair+length interface. Preserve the full universal carry rectangles and a finite weighted-drain/root-language interface. The remaining obligation is to prove central x-block nonmonochromaticity for every authentic root state, not merely for the scanned prefix.
