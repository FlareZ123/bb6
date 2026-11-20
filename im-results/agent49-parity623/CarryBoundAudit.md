# Audit: one-extra-digit carry bound does not bound the total carry

**Status:** exact counterexample from the source-shaped #623 root replay. This corrects an overstrong interpretation in the current signed-coordinate note and the small-start reset scan. It does not affect the wider carry rectangles or the original full-range scan.

## Exact root counterexample

At zero-based root state index 38,
\[
D(a,d)=D(44634,124427)\longmapsto D(79788,133932).
\]
The input sector is right-odd (RO), the output orientation is right, and the carry transducer uses \(k=6\), so \(3^k=729\). In the signed coordinates
\[
x=2g-2=-108220,\qquad y=6q=267804,
\]
the exact affine map is
\[
x'=-4x-3y+C,\qquad y'=3x+3y+F,
\]
with
\[
(x',y')=(-370444,478728),\qquad (C,F)=(88,-24).
\]

The existing replay's low-residue formula at position \(k\) gives
\[
x_0=x\bmod729=401,\quad x_1=x\bmod243=158,\quad y_1=y\bmod243=18,
\]
and hence
\[
a_k=\left\lfloor\frac{-x_0-3x_1-3y_1+C}{729}\right\rfloor
=\left\lfloor\frac{-401-474-54+88}{729}\right\rfloor=-2,
\]
\[
b_k=\left\lfloor\frac{3x_1+3y_1+F}{729}\right\rfloor
=\left\lfloor\frac{474+54-24}{729}\right\rfloor=0.
\]
The preceding digit pair is \((x_{k-1},y_{k-1})=(1,1)\), and the current pair is \((x_k,y_k)=(1,1)\). Applying the exact R transducer at digit \(k\):
\[
r_x=-x_k-x_{k-1}-y_{k-1}+a_k=-5,\qquad
r_y=x_{k-1}+y_{k-1}+b_k=2.
\]
Therefore the carry entering the word at position \(k+1\) is
\[
(a_{k+1},b_{k+1})=
(\lfloor-5/3\rfloor,\lfloor2/3\rfloor)=(-2,0),
\]
not an element of \([-1,1]^2\). The produced digit pair is \((1,2)\), matching the actual next-state digits, so this is not a coordinate or indexing artefact.

## Source of the overclaim

The theorem one_extra_digit_carry_bound proves only that the *additional quotient contributed by the affine correction* is in \(\{-1,0,1\}\), after reducing the uncorrected low linear term to a residue in \([0,3K)\). It does not eliminate the separate carry already contributed by the low linear part.

For the R-x coordinate that base linear carry can lie in \([-3,0]\); adding the correction carry in \([-1,1]\) gives the full range \([-4,1]\). The existing full ranges
- L: \(a,b\in[-2,2]\);
- R: \(a\in[-4,1]\), \(b\in[-2,2]\)

remain the justified ranges. The source theorem does not justify replacing the initial ranges at \(k+1\) by \([-1,1]^2\).

## Consequence for existing diagnostics

The file synchronizing_reset_subwords_small_start.cpp uses \([-1,1]^2\) as its initial carry set. Its reported refinement (common reset length at most four, earliest end by position 12) is therefore not established for the authentic root boundary carries. The wider full-range synchronizing scan in SynchronizingWordScan.md is unaffected.

The corrected next step is either:
1. restore the full branch-specific initial carry ranges in the reset-subword scan; or
2. prove a genuinely sharper bound on the **total** carry after accounting for the base linear carry, with a source-checked derivation.

Do not use the small-start refinement as a proof dependency until one of these is done.
