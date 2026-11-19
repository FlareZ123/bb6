# U5 B2 root4: two W11 q = 3 (mod 16) exclusions

**Status:** new conditional nonreachability derivation, 2026-11-19. The arithmetic has been checked exactly, but the composed theorem has not been Lean-formalized or compiled. Keep in `im-results/`.

## Proposed root-index theorem

Assume
[
E=201+3360(6657+8192r),\qquad
18018+211u+22155r=20\cdot2^{E-13}.
]
If
[
r\bmod4096\in\{3924,1876\},
]
then
[
\neg CReach(734+10944u,\;34881+518816u).
]

## 1. The root index fixes the W11 parameter

Both residues have (r\equiv84\pmod{256}), so the root-equation mod-1680 bridge gives (u=542+840w). Put (R=(r-4)/16). The exact root equation divided by eight gives
[
27625+44310R+22155w\equiv0\pmod{512}.
]
The two rows are:
| (r\bmod4096) | (R\bmod256) | (w\bmod512) | (q=(w-11)/16\bmod32) |
|---:|---:|---:|---:|
| 3924 | 245 | 59 | 3 |
| 1876 | 117 | 315 | 19 |

Thus (w=16q+11) with (q\equiv3\pmod{16}). The complete source parent fan for P(q) has both the direct parent Q(q) and a high odd-a bounce parent A(q); the latter must be excluded before using the Q branch.

## 2. The alternate high odd-a parent of P(q) is unreachable

Write q=16v+3. The odd-a bounce equations force
\[
A(q)=(8991250435+38590792800v,\;
      21772287385+93447495120v).
\]
Its coordinates are odd, its right coordinate is at least five, and
\[
A_x+A_y=30763537820+132038287920v\equiv12\pmod{16}.
\]
The source-certified oddodd_lowval_blank_reach_iff therefore reduces any blank reach of A(q) to
\[
D_A(v)=(15381768908+66019143960v,\;
        18577028145+79733319540v).
\]
Here D_A has even left coordinate, odd right coordinate at least five, and
\[
D_{A,x}+D_{A,y}=33958797053+145752463500v\equiv1\pmod4.
\]
The source-certified BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one excludes D_A(v), hence A(q) is unreachable. The direct parent is therefore the only possible source parent of P(q), and
\[
CReach(P(q))\iff CReach(Q(q)).
\]

The direct parent is
\[
Q(q)=(7021907149+9647698200q,\;
      1617666871+2222581620q).
\]
## 3. Q has a unique low-valuation parent D2

Write (q=4t+3). Since q is 3 modulo 16, (t\equiv0\pmod4). The Q coordinate sum is
[
Q_x+Q_y=8639574020+11870279820q\equiv8\pmod{16}.
]
The existing exact odd/odd low-valuation inverse reduces Q to
[
D2(t)=(22125206738+23740559640t,\;
       15205309233+16315443060t).
]
For (t=4v), D2 is even/odd and
[
D2_x+D2_y+1
=37330515972+160224010800v\equiv4\pmod8.
]
Its exact 2-adic valuation is two.

## 4. The source-certified valuation-two inverse forces a forbidden parent

For (t=4v), D2 is even/odd, its right coordinate is at least five, and
`(D2_x+D2_y+1)%8=4`. Apply the existing source-certified theorem
`BB6.Agent3.evenodd_four_blank_reach_iff`. It gives the exact all-time equivalence between D2 reachability and reachability of its unique parent
[
R(v)=
(18665257983+80112005400v,\;
 16935283607+72686888820v).
]
Both coordinates are odd, the right coordinate is at least five, and
[
R_x+R_y=35600541590+152798894220v\equiv2\pmod4.
]
The source-certified `blank_no_odd_sum_two` excludes this parent. Therefore D2 is unreachable, then Q, P, P4, and the original B2 target are unreachable.

## Validation boundary

This extends the W11 odd-q direct-parent reduction. The exact source grammar and odd/odd low-valuation theorem are existing source-certified components, but the composed D2 parent argument and B2-to-P4 transfer have not been Lean-compiled in the current `U5B2Root32.lean` closure. The current local shell/Python tools returned ClientError, and no CI was dispatched because the Critic gate requires exact-source local preflight. This is a conditional two-cylinder exclusion, not a Machine C or BB(6) solution.
