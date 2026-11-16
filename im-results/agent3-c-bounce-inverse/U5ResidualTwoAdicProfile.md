# Exact two-adic profile of the U5 terminal q-fan

**Status:** exact arithmetic lemma derived from the U5 residual identity. This is an intermediate structural reduction, not a blank-root exclusion by itself.

## Setup

For a U5 residual parameter (w), write (E=201+3360w). The exact residual lift used by the y=3 terminal argument gives

```
211*t + 1360 + 22155*w = 20 * 2^E.
```

The exact odd/odd q-fan for (X_t=(44t-1,42t-1)) has parent parameters satisfying

```
43*t - 1 = 4^q * U,     U >= 4,     U is even.
```

## A global valuation identity

Multiplying the residual identity by 43 and subtracting 211 gives

```
211*(43*t - 1) + 952665*w + 58691 = 860 * 2^E
                                     = 215 * 2^(E+2).
```

Put (A(w)=952665w+58691). For every (wge0),

```
0 < A(w) <= 952665*(w+1) < 2^203*(w+1)
                         <= 2^203 * 2^(3360*w)
                          = 2^(E+2).
```

Here (2^{203}>952665), and (w+1le2^wle2^{3360w}). Thus (v_2(A(w))<E+2). Since (215) and (211) are odd, the displayed identity implies the exact equality

```
v2(43*t - 1) = v2(952665*w + 58691).
```

This is not merely a congruence lower bound: the valuations are equal for every natural residual parameter (w).

## Consequence for the q-fan depth

A q-fan parent requires (2^{2q+1}mid 43t-1), because (U) is even. Therefore every possible q satisfies

```
2*q + 1 <= v2(952665*w + 58691),
q <= floor((v2(952665*w + 58691) - 1)/2).
```

If (A(w)) is odd, there is no q-fan parent at all. In particular, since (A(w)equiv w+1pmod2), every even (w) has no q-fan parent.

Modulo eight, (A(w)equiv w+3pmod8), giving the first global split:

| (wmod8) | (v_2(A(w))) | q-fan possibilities |
|---:|---:|---|
| 0, 2, 4, 6 | 0 | none |
| 1 | exactly 2 | q=0 only |
| 3 | exactly 1 | q=0 only |
| 5 | at least 3 | q=0 and possibly higher q |
| 7 | exactly 1 | q=0 only |

Representative exact profiles:
- (w=413) and (w=1021): (v_2(A)=3), hence (qle1).
- (w=1125): (v_2(A)=5), hence (qle2).
- (w=5): (v_2(A)=10), hence (qle4).

The (w=413,1021,1125) cylinder proofs are instances of this global valuation control, but their source-parent chains still require their additional congruence hypotheses. The valuation identity does **not** imply that all odd (w) are excluded, and it does not close the full U5 family.

## Research use

The remaining terminal problem is now separated into two parts:

1. the arithmetic, which fixes the exact finite q-fan depth from the single affine integer (A(w));
2. the original-section source-parent analysis for each admissible q.

This gives a principled way to prioritize the unresolved (w)-classes: (wequiv1,3,7pmod8) have only q=0, while (wequiv5pmod8) is the only odd class in which higher q branches can occur. The next useful advance is a uniform source-parent exclusion for these classes, not another finite quotient census.

No Lean compilation is claimed for this note; the identity and valuation argument are elementary arithmetic derived directly from the exact residual equation.


## The q-fan depth is unbounded across residual parameters

There is no uniform finite upper bound on (q) as (w) varies. For each (rge0), the odd coefficient (952665) is invertible modulo (2^{2r+1}), so there is a unique residue (w_rpmod{2^{2r+1}}) satisfying

```
952665*w_r + 58691 = 0 (mod 2^(2*r+1)).
```

Every (w=w_r+2^{2r+1}n) then has (v_2(A(w))ge2r+1). By the valuation identity, (2^{2r+1}mid43t-1), so the exact q-fan admits (q=r) with even (U=(43t-1)/4^r). Taking (n) sufficiently large makes (Uge4). Since every natural (w) has a nonempty U5 residual lift, this yields infinitely many genuine residual parameters admitting the q=r branch, for every r.

The first unique residue classes are:

| r | modulus (2^{2r+1}) | (w_r) |
|---:|---:|---:|
| 0 | 2 | 1 |
| 1 | 8 | 5 |
| 2 | 32 | 5 |
| 3 | 128 | 5 |
| 4 | 512 | 5 |
| 5 | 2048 | 1029 |
| 6 | 8192 | 3077 |
| 7 | 32768 | 19461 |
| 8 | 131072 | 19461 |

Thus the q-fan depth is genuinely unbounded over the residual family. No proof strategy that handles only a fixed finite list of q-values can close all U5 residuals. A complete treatment must control q parametrically, establish a q-uniform source-parent obstruction, or find a different invariant that bypasses the fan.
