# Mod-7 restriction on the six-bit restart slack

Status: exact necessary condition; not yet an exclusion.

## Setup

For a high-depth restart, write the restart energy from the source potential as
[
I_0=98P-D_0,qquad D_0=49d_0+14M-55,qquad P=2^n,
]
where (M=m_0+n). After (s) depth-two steps, the exact depth-two identity gives
[
I_0=8^s R
]
for an integer (R>0). The restart bounds in `HighDepthRestartPotential.md` give (I_0<98P).

The unresolved six-bit slack is the case (3s>n). Put
[
r=3s-n,qquad 8^s=2^{n+r},qquad I_0=R2^{n+r}.
]
Then
[
D_0=(98-2^rR)P.
]
Since (D_0=49d_0+14M-55), one has (D_0equiv1pmod7). Since (P=2^n) and (2^3equiv1pmod7), this forces
[
R,2^{n+r}equiv -1equiv6pmod7.
]
Also (R2^r<98), hence (1le Rlelfloor97/2^rfloor). In particular (rle6).

## Exact residue table

The required residue is (Requiv6,3,5pmod7) when (n+requiv0,1,2pmod3), respectively. Combining this with (R2^r<98) gives:

| (r=3s-n) | (nmod3) | Allowed (R) | (K=98-2^rR), where (D_0=KP) |
|---:|---:|---|---|
| 1 | 0 | 3, 10, 17, 24, 31, 38, 45 | 92, 78, 64, 50, 36, 22, 8 |
| 1 | 1 | 5, 12, 19, 26, 33, 40, 47 | 88, 74, 60, 46, 32, 18, 4 |
| 1 | 2 | 6, 13, 20, 27, 34, 41, 48 | 86, 72, 58, 44, 30, 16, 2 |
| 2 | 0 | 5, 12, 19 | 78, 50, 22 |
| 2 | 1 | 6, 13, 20 | 74, 46, 18 |
| 2 | 2 | 3, 10, 17, 24 | 86, 58, 30, 2 |
| 3 | 0 | 6 | 50 |
| 3 | 1 | 3, 10 | 74, 18 |
| 3 | 2 | 5, 12 | 58, 2 |
| 4 | 0 | 3 | 50 |
| 4 | 1 | 5 | 18 |
| 4 | 2 | 6 | 2 |
| 5 | 0 | none | none |
| 5 | 1 | none | none |
| 5 | 2 | 3 | 2 |
| 6 | 0 | none | none |
| 6 | 1 | none | none |
| 6 | 2 | none | none |

Consequences:

- (r=6) is impossible.
- (r=5) is possible only when (nequiv2pmod3), and then (R=3), (D_0=2P).
- For (r=4), (R) is uniquely determined by (nmod3).
- All remaining cases are a finite list of exact values (D_0=KP), not a free interval.

## What this does and does not prove

This does **not** eliminate (3s>n). It reduces the slack case to the table above. A further contradiction must use source-restart constraints on (d_0,M,b_p,d_p,t), or the five-shallow profile equations; the mod-7 congruence alone is insufficient.

The derivation uses only the restart energy identity and the fact that (D_0equiv1pmod7). It is independent of the unfinished PR #99 list-to-Finset bridge.
