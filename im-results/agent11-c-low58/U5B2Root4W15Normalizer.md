# U5 B2: root4 w = 15 (mod 16) normalizer cylinders

**Status:** additional five infinite root-index exclusions derived 2026-11-19. The arithmetic and affine gate paths were checked with exact BigInt / symbolic affine execution, but this composition has **not** been Lean-formalized or compiled. This complements `U5B2Root4W7Normalizer.md`; keep both in `im-results/`.

## Proposed root-index residues

Let
[
\mathcal R_{15}=\{3380,2356,1332,564,308\}
\subseteq\mathbb Z/4096\mathbb Z.
]
For (r\bmod4096\in\mathcal R_{15}), together with
[
E=201+3360(6657+8192r),\qquad
18018+211u+22155r=20\cdot2^{E-13},
]
the proposed conclusion is
[
\neg CReach(734+10944u,\;34881+518816u).
]
All five residues are (52\pmod{64}) and (4\pmod{16}); they are disjoint from the previously recorded root4 and root32 cylinders.

## Root equation to w

As in `U5B2Root4W7Normalizer.md`, `root_equation_mod1680` gives (u=542+840w) with (w) odd. Put (R=(r-4)/16). Dividing the exact root equation by eight gives
[
27625+44310R+22155w=5\cdot2^{E-14}.
]
The right side is divisible by 512. For (w=512t+16c+15), reduction modulo 512 and division by two gives
[
179975+22155R+177240c\equiv0\pmod{256},
]
or
[
7+139R+88c\equiv0\pmod{256}.
]
The following five rows solve this congruence and give the root-index residues:
| (c\bmod32) | (R\bmod256) | (r\bmod4096) |
|---:|---:|---:|
| 7 | 211 | 3380 |
| 15 | 147 | 2356 |
| 23 | 83 | 1332 |
| 29 | 35 | 564 |
| 31 | 19 | 308 |

Thus (w=16s+15), with (s=32t+c).

## D-parent and four-sector normalization

The P4 low-valuation inverse and the even/odd three-divisible parent classification are the same as in the W7 note. Since (w\equiv15\pmod{16}), (D_x+D_y+1\equiv4\pmod8), so the only possible D-parent depth is (n=0). Its coordinates are
[
P=(a,k)=
(5087207147+5202534960s,\;
 4346624554+4445163240s).
]

Applying the exact source-certified `fullForcedNormalize` to (P), with (s=32t+c), gives:
| (c) | path | normalized (x(t)) | normalized (y(t)) | ((x+y)\bmod4) |
|---:|:---:|---:|---:|---:|
| 7 | ARO | 51782397258 + 207705130080t | 30324044531 + 121633218000t | 1 |
| 15 | ARO | 103708679778 + 207705130080t | 60732349031 + 121633218000t | 1 |
| 23 | ARO | 155634962298 + 207705130080t | 91140653531 + 121633218000t | 1 |
| 29 | ARORR | 365499997042 + 390154957080t | 28486720475 + 30408304500t | 1 |
| 31 | ARO | 207561244818 + 207705130080t | 121548958031 + 121633218000t | 1 |

Here A is `evenAffineGate`, R is `sixEvenRightGate`, and O is `oddLowGate`. In every row the normalized right coordinate is odd and at least five, and the sum is 1 modulo four. Therefore `fullForcedExcluded_sound` excludes (P), which propagates to (D), P4, and B2.

## Validation boundary

The normalizer/filter themselves have original-source CI evidence (four-sector closure, CI 42366675885). The new residue mapping, parent composition, and five affine normalizer paths have not been Lean-compiled. In particular, the D-parent classification and B2-to-P4 implication are still in the uncompiled `U5B2Root32.lean` closure. No CI was dispatched because the current Critic gate requires exact-source local preflight first; local shell/Python access returned ClientError in this invocation.

Formalization should reuse the same pattern as the W7 note: solve the root congruence, show the D-parent is depth zero, then prove the five affine paths and invoke `fullForcedExcluded_sound`.
