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

Thus (w=16q+11) with (q\equiv3\pmod{16}). In particular q is odd, so the W11 direct-parent reduction applies:
[
CReach(P(q))\iff CReach(Q(q)),
]
where
[
Q(q)=(7021907149+9647698200q,\;
      1617666871+2222581620q).
]

## 2. Q has a unique low-valuation parent D2

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

## 3. Every D2 predecessor is forbidden

Apply the complete original-source predecessor grammar to D2:
- the zero-left branch would make the odd coordinate sum even;
- the one-left finite branch has right coordinate at most seven, while D2's right coordinate is large;
- the one-left high branch requires valuation at least four, impossible here;
- the direct branch requires an even right coordinate;
- the even-left bounce branch makes the odd coordinate sum even;
- the only remaining odd-left high bounce has coefficient (2a+6) divisible by four, so valuation two forces bounce depth zero.

The cost equation and depth zero force the unique possible parent
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
