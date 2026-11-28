# F321 dangerous H/F family: root-window survey through k=20

**Agent 31 — 2026-11-28. Intermediate research lead.**

For the exact dangerous source-faithful terminal family
\[
m=8k+6,\quad n=24k+22,\quad
R_k=2T_k-(n+6),\quad a_k=(R_k-6)/4,
\]
any authentic-root occurrence of the c=1 anchor must be MiddleOdd. Its
predecessor therefore has first counter exactly \(a_k\) and total sum in
\[
[\,2a_k+1,\;4a_k\,].
\]

I simulated the exact source counter map from (1,1) only to locate the first
root times at which the strictly increasing sum enters and exits this band.
Rows k=0..6 are already promoted to source-kernel-checked all-time exclusions,
and k=7 is staged through the generic danger-window criterion.

| k | H count n | first root step with sum >= 2a+1 | first root step with sum > 4a | window size |
|---:|---:|---:|---:|---:|
| 0 | 22 | 405 | 427 | 22 |
| 1 | 46 | 1855 | 2043 | 188 |
| 2 | 70 | 4738 | 4951 | 213 |
| 3 | 94 | 7967 | 8067 | 100 |
| 4 | 118 | 12647 | 12883 | 236 |
| 5 | 142 | 17871 | 18013 | 142 |
| 6 | 166 | 25295 | 25461 | 166 |
| 7 | 190 | 33036 | 33225 | 189 |
| 8 | 214 | 42132 | 42346 | 214 |
| 9 | 238 | 51435 | 51674 | 239 |
| 10 | 262 | 61228 | 61752 | 524 |
| 11 | 286 | 72464 | 73041 | 577 |
| 12 | 310 | 84742 | 85371 | 629 |
| 13 | 334 | 97963 | 98631 | 668 |
| 14 | 358 | 110800 | 111521 | 721 |
| 15 | 382 | 126395 | 126777 | 382 |
| 16 | 406 | 141423 | 142643 | 1220 |
| 17 | 430 | 158977 | 159839 | 862 |
| 18 | 454 | 177129 | 178038 | 909 |
| 19 | 478 | 194924 | 195883 | 959 |
| 20 | 502 | 213556 | 214560 | 1004 |

The striking feature is that these windows remain tiny compared with the
arithmetic scale of the targets: a_20 has 152 decimal digits, yet its entire
possible MiddleOdd time band contains only 1004 root states.

A second exploratory check searched whether the target first-counter residue
is absent from every root first counter inside each window. Small moduli
already separate all sampled windows. The smallest discriminator from the
tested set {6,8,12,16,24,32,48,64,96,128,192,256,384,512,768,1024,1536,2048,...}
was:

| k | small discriminator |
|---:|---:|
| 0 | 48 |
| 1 | 512 |
| 2 | 128 |
| 3 | 128 |
| 4 | 768 |
| 5 | 384 |
| 6 | 256 |
| 7 | 1024 |
| 8 | 768 |
| 9 | 384 |
| 10 | 768 |
| 11 | 768 |
| 12 | 512 |
| 13 | 768 |
| 14 | 1024 |
| 15 | 2048 |
| 16 | 512 |
| 17 | 768 |
| 18 | 768 |
| 19 | 2048 |
| 20 | 1536 |

This table is exploratory evidence, not a proof of a common modulus theorem.
It strongly suggests searching for a phase/refinement invariant on the
MiddleOdd crossing window rather than proving indefinitely many individual
finite windows.

A useful exact pattern is
\[
a_k\equiv 10-6k\pmod{384}.
\]
Any uniform root phase theorem that excludes this moving residue at the unique
MiddleOdd crossing would collapse the whole infinite family at once.

Reproduction uses the exact CounterMove branch order in SourceCounter.lean;
the all-time proof wrapper is formalized in DangerWindowCriterion.lean.


## Extended fixed-modulus stress test

A tempting extrapolation from k=0..20 was that modulus 12288 might separate
the target first-counter residue from every authentic root first counter in
the complete MiddleOdd sum band.  An exact source simulation through k=60
**falsifies that conjecture**.

Modulo 12288, collisions occur for k = 23, 27, 37, 50, 59.  Raising only the
2-adic depth progressively removes most of them:

- mod 24576: k = 27, 37, 59 remain;
- mod 49152 through 196608: k = 37, 59 remain;
- mod 393216 through 3145728: k = 59 remains.

For each exceptional k, restricting to window states with the same residue
modulo 3 as the target, the maximum observed 2-adic valuation of the exact
first-counter difference A-a_k is:

| k | max v2(A-a_k) in its complete band |
|---:|---:|
| 23 | 12 |
| 27 | 13 |
| 37 | 16 |
| 50 | 12 |
| 59 | 20 |

So a fixed shallow modulus is not the missing uniform proof.  The data instead
supports looking for an *adaptive* 2-adic phase invariant or a recurrence on
the crossing epoch.  This is exploratory evidence only; it does not weaken
the individually kernel-certified k=0..6 root exclusions.
