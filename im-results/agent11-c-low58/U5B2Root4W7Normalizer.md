# U5 B2: root4 w = 7 (mod 16) normalizer cylinders

**Status:** new infinite-family reduction derived 2026-11-19. The modular and affine arithmetic was checked with exact BigInt calculations and a symbolic affine execution of the repository's four-sector normalizer. The new composition has **not** been Lean-formalized or compiled. Keep in `im-results/`; do not promote to `results/`.

## Proposed root-index exclusion

Let
[
\mathcal R=
\{244,3828,3316,3188,2804,2292,1780,1396,1268,1140,756\}
\subseteq\mathbb Z/4096\mathbb Z.
]
For any natural (r,E,u) satisfying
[
r\bmod4096\in\mathcal R,\qquad
E=201+3360(6657+8192r),
]
and
[
18018+211u+22155r=20\cdot2^{E-13},
]
the proposed conclusion is
[
\neg CReach(734+10944u,\;34881+518816u).
]

This gives eleven disjoint root-index cylinders, all with (r\equiv4\pmod{16}) and (r\equiv52\pmod{64}). It is disjoint from the existing (r\equiv12\pmod{16}), (r\equiv32\pmod{64}), and (r\equiv20\pmod{128}) exclusions.

## 1. Recover w and the q residue

The standalone arithmetic theorem `root_equation_mod1680` gives
[
(u+105r)\bmod1680=122.
]
Every (r\in\mathcal R\pmod{4096}) is (4\pmod{16}), so
[
u\equiv1382\pmod{1680}.
]
Thus
[
u=542+840w
]
for an odd natural (w).

Set (R=(r-4)/16). The exact root equation becomes
[
221000+354480R+177240w=20\cdot2^{E-13},
]
hence
[
27625+44310R+22155w=5\cdot2^{E-14}.
]
The right side is divisible by 512. Dividing the congruence by two gives
[
91355+22155R+177240q_0\equiv0\pmod{256}
]
when (w=512t+16q_0+7); equivalently, before choosing (q_0),
[
27625+44310R+22155w\equiv0\pmod{512}.
]
Because 22155 is odd, this determines (w\pmod{512}) uniquely from (R\pmod{256}).

The eleven rows below are the exact solutions of that congruence. Each row has (r=16R+4\pmod{4096}), (w=16s+7\pmod{512}), and (s=32t+q_0).

| (q_0=s\bmod32) | (R\bmod256) | (r\bmod4096) |
|---:|---:|---:|
| 0 | 15 | 244 |
| 4 | 239 | 3828 |
| 8 | 207 | 3316 |
| 9 | 199 | 3188 |
| 12 | 175 | 2804 |
| 16 | 143 | 2292 |
| 20 | 111 | 1780 |
| 23 | 87 | 1396 |
| 24 | 79 | 1268 |
| 25 | 71 | 1140 |
| 28 | 47 | 756 |

Thus in each row (w=16s+7) with (s=32t+q_0).

## 2. Force the unique D-parent

For (u=542+840w), the P4 target
[
(63895+950614u,\;3291+48981u)
]
has the exact odd/odd low-valuation parent
[
D(w)=(270923836+419829900w,\;
      148737413+230486970w).
]
The P4 sum is (541847676+839659800w), which is (4\pmod{16}) for every odd (w) in this parameterization. Thus the existing `oddodd_lowval_blank_reach_iff` applies.

For (D(w)=(x,y)),
[
x+y=419661249+650316870w\equiv0\pmod3,
]
and
[
x+y+1=419661250+650316870w.
]
Since (w\equiv7\pmod{16}), the latter is (4\pmod8), so its exact 2-adic valuation is two. The drafted `even_odd_three_divisible_parent` therefore forces depth (n=0) and the unique possible source parent
[
P=(a,k)=
(209830622+325158435w,\;
 (358568033+555645405w)/2).
]
Writing (w=16s+7), this is
[
P=(2485939667+5202534960s,\;
   2124042934+4445163240s),
]
where (s=32t+q_0).

## 3. Apply the source-certified four-sector normalizer

The exact all-time theorem `blank_reach_iff_fullForcedNormalize` and sound filter `fullForcedExcluded_sound` are already source-certified in `FullForcedNormalize.lean` / `FullForcedFilter.lean` (four-sector original-source CI 42366675885). For each of the eleven (q_0) classes, symbolic affine execution of the exact gate order gives the following path and residual. The path letters are:
- A = `evenAffineGate`;
- R = `sixEvenRightGate`;
- O = `oddLowGate`.

| (q_0) | path | normalized (x(t)) | normalized (y(t)) | ((x+y)\bmod4) |
|---:|:---:|---:|---:|---:|
| 0 | AAR | 6203014793 + 415410260160t | 265505365 + 17780652960t | 2 |
| 4 | AAR | 58129297313 + 415410260160t | 2488086985 + 17780652960t | 2 |
| 8 | AAR | 110055579833 + 415410260160t | 4710668605 + 17780652960t | 2 |
| 9 | AAAAR | 130936621473 + 442081239600t | 1316578501 + 4445163240t | 2 |
| 12 | AAR | 161981862353 + 415410260160t | 6933250225 + 17780652960t | 2 |
| 16 | AAR | 213908144873 + 415410260160t | 9155831845 + 17780652960t | 2 |
| 20 | AAR | 265834427393 + 415410260160t | 11378413465 + 17780652960t | 2 |
| 23 | AAARO | 162173581898 + 221040619800t | 84348128367 + 114965473140t | 1 |
| 24 | AAR | 317760709913 + 415410260160t | 13600995085 + 17780652960t | 2 |
| 25 | AAAAR | 351977241273 + 442081239600t | 3539160121 + 4445163240t | 2 |
| 28 | AAR | 369686992433 + 415410260160t | 15823576705 + 17780652960t | 2 |

In every row the normalized right coordinate is odd and at least five, and the sum is 1 or 2 modulo four. Hence `fullForcedExcluded` is true, and `fullForcedExcluded_sound` excludes (P) from the genuine blank orbit. The D-parent implication then excludes (D(w)); the low-valuation iff excludes P4; and the existing even-(u) B2-to-P4 implication excludes the original B2 target.

The affine gate-path calculation was performed symbolically: each branch guard has constant residue on the full (t\ge0) progression, all division steps have integer affine coefficients, and each threshold is already satisfied at (t=0) with nonnegative slope. A separate exact BigInt run checked all 44 pairs (q_0\) in the eleven-row set and (t=0,1,2,3); this is a regression check, not the proof.

## Validation boundary

The new arithmetic and normalizer composition are not Lean-compiled. The existing four-sector normalizer/filter has original-source CI evidence, but the D-parent lemma and B2-to-P4 composition in `U5B2Root32.lean` remain part of the uncompiled full closure. No CI was dispatched because the current Critic gate requires exact-source local preflight first; the local shell and Python tools returned ClientError in this invocation.

Suggested formalization: prove the root-residue-to-(q_0) table by `omega`/modular arithmetic, then add eleven small affine normalization lemmas (or one `q_0\bmod32` case split) showing `fullForcedExcluded P=true`. Keep the theorem in `im-results/` until the complete original-source closure and axiom audit pass.
