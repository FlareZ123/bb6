# U5 second-cone zero-left sieve

**Status:** exact source-predecessor reduction plus finite M32 quotient check. The earlier 13/16 exclusion claim is withdrawn: it used the wrong coordinate order for the M32 state. The source reduction to Z3 below remains an intermediate derivation, not yet Lean-compiled.

## Starting family

The exceptional Side source is
\[
Z_0=(0,K_0,C_0)=(0,33+32u+16v,\;33+32v),\qquad v\ge u.
\]
All parameters are natural. In particular, K0,C0≥33 and K0≡1 (mod 4).

Use the exact source predecessor lemmas in im-results/agent21-c-source-bridge/CBack.lean:
- reached_high_pred;
- reached_hub_prev;
- reached_one_high_or_reset;
- reached_high_kzero_prev;
- reached_zero_hub.

Use Agent 48's reached_middle_zero_mod4 in im-results/agent48-c-middle-zero/KZeroMod4.lean, which says every reachable (a,0,c) has a≡1 (mod 4).

## Forced source reduction

Assume Z0 is reachable.

1. Apply reached_high_pred K0-2 times, then reached_hub_prev, to obtain
   \[
   (K_0-1,1,C_0+K_0-1)\in\mathrm{Reach}.
   \]
   The high branch of reached_one_high_or_reset gives (K0,0,C0+K0). By reached_high_kzero_prev, this implies a second zero-left state with middle
   \[
   K_1=(K_0-3)/2=15+16u+8v\equiv3\pmod4.
   \]
   Its right counter C1=C0+K0 is even. Repeating the high-predecessor/hub/one chain from (0,K1,C1), the reset branch is impossible (its right parameter is even), while the high branch forces a middle-zero state with left coordinate K1≡3 (mod 4), contradicting Agent 48. Hence the first high branch is impossible and the reset branch forces
   \[
   R_1=(K_0+1,L_1,0),\qquad L_1=(C_0+K_0-2)/2=32+16u+24v.
   \]

2. Apply reached_zero_hub, reached_hub_prev, and reached_one_high_or_reset to R1. The high branch gives a middle-zero state with left coordinate K0+L1-2≡3 (mod 4), so it is impossible. Thus
   \[
   R_2=(K_0+L_1-1,L_2,0),\qquad L_2=(L_1-2)/2=15+8u+12v.
   \]

3. Apply reached_zero_hub to R2, obtaining a hub
   \[
   H=(A_3,2,L_2-2),\qquad A_3=K_0+L_1+L_2-6=74+56u+52v\equiv2\pmod4.
   \]
   Its possible immediate source classes are:
   - the high source (A3+1,1,L2-1);
   - the zero-left even source (0,(A3-2)/2,L2+1).

   The high source is impossible: reached_one_high_or_reset has even reset parameter L2-1, so it forces the high branch and then a middle-zero state with left coordinate A3+2≡0 (mod 4), contradicting Agent 48. Therefore the zero-left even source is forced:
   \[
   Z_3=(0,K_3,C_3),
   \]
   where
   \[
   K_3=36+28u+26v,\qquad C_3=16+8u+12v.
   \]

Thus Z0 reachable implies Z3 reachable.

## Correct M32 quotient check

**Coordinate order matters.** The source state is Z3=(0,K3,C3), so the M32 quotient cell is
\[
(q(0),q(K_3),q(C_3))=(0,q(K_3),q(C_3)),
\]
not (q(K3),q(C3),0). The previous table used the latter, permuted cell and is withdrawn.

Put L=(2u+3v) mod 16. Since K3≥36 and C3≥16, the correct quotient representatives and exact M32 membership are:

| L mod 16 | q(K3) | q(C3) | seen(0,qK,qC) |
|---:|---:|---:|:---:|
| 0 | 36 | 16 | yes |
| 1 | 34 | 20 | yes |
| 2 | 32 | 24 | yes |
| 3 | 30 | 28 | **no** |
| 4 | 28 | 32 | yes |
| 5 | 26 | 36 | yes |
| 6 | 24 | 8 | **no** |
| 7 | 22 | 12 | yes |
| 8 | 20 | 16 | **no** |
| 9 | 18 | 20 | yes |
| 10 | 16 | 24 | yes |
| 11 | 14 | 28 | **no** |
| 12 | 12 | 32 | yes |
| 13 | 10 | 36 | yes |
| 14 | 8 | 8 | yes |
| 15 | 38 | 12 | yes |

The corrected finite computation therefore excludes only L≡3,6,8,11 (mod 16), i.e. 4 of the 16 parameter residue classes. If Z0 is reachable, this quotient argument leaves the other 12 classes; it does not establish the earlier claimed 3-class remainder.

The M32 graph census remains 31,570 reachable quotient states / 189,834 representative edges. The table above is a computational observation pending exposure as a small Lean theorem against the generated CCert.seen bitset. It is not itself a source-reachability theorem.

## Reproducibility and next step

- Source predecessor lemmas: im-results/agent21-c-source-bridge/CBack.lean.
- Middle-zero invariant: im-results/agent48-c-middle-zero/KZeroMod4.lean.
- Finite quotient transition and certificate generator: tools/agent43_c32_certificate.py, im-results/agent43-c-quotient-kernel/M32HighAll.lean.
- A source-only proof should first formalize the reduction Z0 ⇒ Z3, then check the 16 correct cells (0,q(K3),q(C3)). The 12 seen classes need an exact source-predecessor argument; no stronger quotient expansion is recommended.
