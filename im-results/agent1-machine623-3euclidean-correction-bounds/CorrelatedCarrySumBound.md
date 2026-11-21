# Correlated source-carry sum bound and a surviving closure counterexample

**Status:** intermediate source-arithmetic lemma plus a finite counterexample to a proposed universal closure property. This is not a blank-root result.

## 1. Exact joint correction bound

Use the formal `corrC` and `corrF` definitions in `SignedCoordinateNormalForm.lean). Write (L) for the drain digit length and (n_1,n_2) for the counts of output digits 1 and 2. The drain-statistics identity gives
[
D=L-2n_2,\qquad R_{\mathrm{full}}=R_{\mathrm{dig}}=n_1+n_2,\qquad n_1+n_2\le L.
]
Substituting these into the eight sector/output correction rows gives:

| Sector/output | (C+F) | Lower bound |
|---|---:|---:|
| LO/L | (-6L-4n_1+8n_2-38) | (-10L-38) |
| LE/L | (-6L-4n_1+8n_2-20) | (-10L-20) |
| RO/L | (-6L-4n_1+8n_2) | (-10L) |
| RE/L | (-6L-4n_1+8n_2-18) | (-10L-18) |
| LO/R | (6L+4n_1-8n_2+18) | (18-2L) |
| LE/R | (6L+4n_1-8n_2+6) | (6-2L) |
| RO/R | (6L+4n_1-8n_2-14) | (-14-2L) |
| RE/R | (6L+4n_1-8n_2-2) | (-2-2L) |

Therefore, uniformly over all rows,
[
C+F\ge -10L-38.
]
If (L\le\ell) and (K=3^k>34\ell+122), then
[
10L+38\le10\ell+38<34\ell+122<K,
]
so
[
\boxed{C+F>-K.}
]

**RO/L clarification:** the constants table in `DrainDigitTransducer.md` gives (c_C=c_F=0) for RO/L. These are only the additive constants. The full corrections are (C=-18D-16R_{\mathrm{full}}) and (F=12D+12R_{\mathrm{full}}), as specified by `SignedCoordinateNormalForm.lean).

This is a joint bound and is stronger than separately applying (|C|,|F|<K).

## 2. Consequence for the boundary carries

With the source-carry formulas and denominator (3K) from `StartCarryRectangleInclusion.md), put
[
\begin{aligned}
A_L&=x_{K1}-3y_K+C,&B_L&=3y_K+F,\\
A_R&=-x_{K1}-3x_K-3y_K+C,&B_R&=3x_K+3y_K+F.
\end{aligned}
]
Then
[
A_L+B_L=x_{K1}+C+F>-K
]
because (x_{K1}\ge0), while
[
A_R+B_R=-x_{K1}+C+F>-4K
]
because (x_{K1}<3K).

For integer floors, (lfloor u/N\rfloor+\lfloor v/N\rfloor\ge\lfloor(u+v)/N\rfloor-1). Taking (N=3K) yields
[
\boxed{c_0+c_1\ge-2\quad(L),\qquad c_0+c_1\ge-3\quad(R).}
]

Thus the 108 L source-derived rectangle starts reduce to 99 necessary starts, and the 180 R starts reduce to 153. These are necessary conditions from the exact correction formulas and existing mass-index buffer; they do not encode the full dependence on the root's low residues.

## 3. The reset language is still not closed under this stronger start restriction

I tested the one-step language-inclusion claim against `SourceDerivedResetProduct.json`:
- input words are read by the 252-state source-derived reset DFA;
- the input must reach its accepting state by position 12;
- the carry start is restricted by the new (c_0+c_1) inequalities above;
- the L/R source transducer emits the target digit-pair stream;
- offset 1 or 2 is dropped, and the first 13 remaining output symbols are checked by the same reset DFA.

The claim “a source-derived reset by position 12 implies a target reset in the first 13 symbols” is false even after also requiring both input coordinate blocks to be nonmonochromatic.

A concrete L/offset-1 witness is:

- initial transducer state ((p_x,p_y,c_0,c_1)=(0,0,-2,0)), which lies in the source-derived L rectangle and satisfies (c_0+c_1=-2);
- input word
  [
  (00)^9,\ 01,\ 10,\ 10,\ 00,\ 00
  ]
  (14 digit pairs);
- the input reset DFA first accepts at position 12; the substring (00,01,10,10) is a reset witness;
- both input coordinate blocks contain 0 and 1, so neither is all-0 nor all-2;
- the L transducer output is
  [
  10,\ (20)^9,\ 21,\ 00,\ 00,\ 00;
  ]
- after dropping offset 1, the 13-symbol target prefix is
  [
  (20)^9,\ 21,\ 00,\ 00,\ 00,
  ]
  whose source-derived reset-DFA state is 189, not the accepting state 3.

This is a counterexample to closure of the **current finite over-approximation**, not a claim about the authentic blank-root orbit. It shows that neither the rectangular start set, nor the improved carry-sum restriction, nor “reset by 12 plus input-coordinate nonmonochromaticity” is by itself a sufficient root invariant.

## 4. Research consequence

The next useful object is the authentic root prefix language: the relation among (x_K,y_K), the boundary digit pair, the weighted drain statistics ((L,n_1,n_2)), sector, and the phase-selected offset. Further arbitrary-word reset products over the same rectangular starts will not close this gap. The finite witness above should be retained as a regression against any proposed universal closure theorem.

Relevant existing source:
- `im-results/agent1-machine623-3euclidean-correction-bounds/SignedCoordinateNormalForm.lean`
- `im-results/agent1-machine623-3euclidean-correction-bounds/DrainDigitTransducer.md`
- `im-results/agent24-machine623-shifted-reset-product/StartCarryRectangleInclusion.md`
- `im-results/agent24-machine623-shifted-reset-product/SourceDerivedResetProduct.json`
