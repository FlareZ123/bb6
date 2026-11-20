# Tighter #623 S-indexed reset window

**Status:** reproducible finite diagnostic and source-bound refinement; not an all-time #623 theorem.

## Mathematical refinement

The prior S-window envelope was

`B_old(ell)=max(34 ell+140, 36 ell+88)`.

Agent 1's exact weighted-correction formalization gives, for the drain statistics (D=L-2E), (E\le R\le L),

- `correction_buffer_closed`: `|C|,|F| ≤ 34L+122`;
- `one_extra_digit_carry_bound_closed`: the boundary carry quotient remains in `[-1,1]` even when the correction has magnitude exactly (K).

Since the mass depth gives (L\le\ell_S), the correction part needs only (34\ell_S+122), not (34\ell_S+140). Keep the existing centered-terminal bound (36\ell_S+88). This gives

[
B_{new}(\ell_S)=\max(34\ell_S+122,36\ell_S+88)\le B_{old}(\ell_S).
]

The exact references are:

- `im-results/agent1-machine623-3euclidean-correction-bounds/SignedCoordinateNormalForm.lean`, theorems `correction_buffer_closed` and `one_extra_digit_carry_bound_closed`;
- `im-results/agent1-machine623-3euclidean-correction-bounds/DrainDigitTransducerCarry.lean`, which proves the three-state digit transducer and exact weighted output statistics;
- `im-results/agent41-623-3euclidean/MonotoneMassWindow.md`, which proves (\ell_{S'}-\ell_S\in\{0,1\}).

### Sharper moving-window shift

The old proof bounded (j'-j\le3) using only (B'\le B+36<3B). The same facts give a much stronger bound.

For (S\ge20), (\ell_S\ge4), since (\tau(3)=13<S+3). Hence (B_{new}\ge B_{new}(4)=258>144). From (\ell_{S'}-\ell_S\in\{0,1\}), each affine term increases by at most 36, so (B'\le B+36). Since (B\ge144),

[
4(B+36)\le5B,qquad
(B')^3\le(B+36)^3\le\frac{125}{64}B^3<3B^3.
]

As (3^j>B^3), this implies (3^{j+1}>3B^3>(B')^3), hence (j'\le j+1). Monotonicity (B'\ge B) gives (j'\ge j). The same (B'\le B+36<3B) argument gives (k'-k\in\{0,1\}). Therefore

[
\boxed{k'-k\in\{0,1\},\qquad j'-j\in\{0,1\}.}
]

There is a further coupling: (k'-k=1) forces (j'-j=1). Indeed, if (k'=k+1), minimality gives (B<3^k\le B'<3^{k+1}), so (B^3<3^{3k}\le(B')^3). Hence (j\le3k<j'). Since (j'\le j+1\le3k+1), necessarily (j=3k) and (j'=3k+1).

Also, minimality of (k) gives (3^{k-1}\le B<3^k), hence
[
3^{3k-3}\le B^3<3^{3k}
\quad\Longrightarrow\quad
j\in\{3k-2,3k-1,3k\}.
]
Thus the phase (r=j-3k\in\{-2,-1,0\}) is a three-state window-index phase. Its only possible shift types are:

- (r\mapsto r) or (r+1) when (k'=k);
- (r=0\mapsto-2) when (k'=k+1) (then (j'=j+1)).

The next required interval ([k'+2,j'-2)) contains the old output subinterval ([k+3,j-2)). It needs at most one low-symbol shift and one high-symbol extension, and the coupled shift phase has only three possible transition types: ((0,0),(0,1),(1,1)). This replaces the previous zero-to-three high-extension phase.

These are paper derivations from the cited source lemmas and exact window definitions, not new Lean theorems in this directory.

## Finite diagnostic

Run from the repository root:

```sh
node im-results/agent48-623-tight-window/tight_mass_window_scan.js
```

The script uses the existing 263-state DFA at `im-results/agent32-623-phase-automaton/ResetPatternDFA.json` and the same explicit JavaScript transcription of the #623 high-level recurrence as `synchronizing_word_scan.js`. It recomputes the S-indexed windows for root indices 33 through 10,000 with both envelopes.

Observed output:

| Quantity | Old envelope | Tighter envelope |
| --- | ---: | ---: |
| States checked | 9,968 | 9,968 |
| DFA failures | 0 | 0 |
| Minimum word length | 8 | 7 |
| Maximum word length | 16 | 16 |
| First reset end | 3–12 | 3–12 |

More precisely:

- The low exponent (k) is unchanged on all 9,968 states.
- The high exponent (j) decreases by one only at indices 33, 34, and 35; it is unchanged at the other 9,965 states.
- The observed shift histogram is ((0,0):9955,(0,1):8,(1,1):5), consistent with the proved three-type restriction.
- The first-acceptance histogram is unchanged:
  `3:2196, 4:4210, 5:2241, 6:866, 7:290, 8:105, 9:37, 10:14, 11:6, 12:3`.
- The three shorter windows at indices 33–35 still accept by symbol 4.

The finite diagnostic therefore survives the sharper correction buffer and saves one high digit at the start of the proposed invariant. It does not prove that the reset DFA accepts every future S-window. The recurrence replay is computational, and no original-source root theorem or global BB(6) conclusion is claimed.

## Next useful use

Agent 32 can use the smaller S-window envelope and the three-type coupled shift phase in the finite product-state closure. Preserve the full carry rectangles, source branch/sector, weighted drain interface, and the low/high boundary state; these arithmetic tightenings do not remove the need to prove reset acceptance for every authentic root state.
