# U5 B2 root4: two W11 q = 9 (mod 16) exclusions

**Status:** new conditional nonreachability derivation, 2026-11-19. It uses the existing source-certified odd/odd sum-16 two-parent iff and the complete source predecessor grammar. The composition is not Lean-compiled; keep in `im-results/`.

## Proposed root-index theorem

Under
[
E=201+3360(6657+8192r),\qquad
18018+211u+22155r=20\cdot2^{E-13},
]
the B2 target is blank-unreachable if
[
r\bmod4096\in\{3156,1108\}.
]

## 1. Recover q = 9 (mod 16)

As in the W11 reduction, (r\equiv84\pmod{256}) gives (u=542+840w), with (w=16q+11). For q=16m+9,
[
w=256m+155.
]
The exact root equation divided by eight gives
[
27625+44310R+22155w\equiv0\pmod{512},
\qquad r=16R+4.
]
For m even, (w\equiv155\pmod{512}), which forces (R\equiv197\pmod{256}) and (r\equiv3156\pmod{4096}). For m odd, (w\equiv411\pmod{512}), which forces (R\equiv69\pmod{256}) and (r\equiv1108\pmod{4096}).

The W11 odd-q parent reduction therefore applies:
[
CReach(P(q))\iff CReach(Q(q)),
]
where
[
Q(q)=(7021907149+9647698200q,\;
      1617666871+2222581620q).
]

## 2. Q is in the exact odd/odd sum-16 two-parent sector

For q=8t+1 (equivalent to q=9 mod16 with t odd),
[
Q(q)=
(16669605349+77181585600t,\;
 3840248491+17780652960t).
]
Its coordinates are odd, its right coordinate is at least 64, and
[
Q_x+Q_y=20509853840+94962238560t\equiv16\pmod{32}.
]
Apply the source-certified `oddodd_sum16_blank_reach_iff`. It says Q is reachable iff at least one of the following two exact source parents is reachable:
[
P_0(t)=
(10254926918+47481119280t,\;
 7047587703+32630886120t),
]
[
P_2(t)=
(2563731728+11870279820t,\;
 10893185295+50436305850t).
]

## 3. Both possible parents have no source predecessor

For P0,
[
P_{0,x}+P_{0,y}
=17302514621+80112005400t\equiv5\pmod8.
]
For P2, t is odd, so
[
P_{2,x}+P_{2,y}
=13456917023+62306585670t\equiv5\pmod8.
]
Thus both targets have odd coordinate sum and sum-plus-one congruent to six modulo eight, so
[
v_2(P_{i,x}+P_{i,y}+1)=1.
]

Apply the complete original-source grammar `section_preimage_all_iff` to either target:
- the zero-left nonexceptional branch and the even-left bounce branch require the odd coordinate sum to be even;
- the one-left high branch requires 16 to divide sum-plus-one, impossible at valuation one, and its finite outputs have right coordinate at most seven;
- the k=0 branch has right coordinate two;
- the direct branch requires an even right coordinate;
- the odd-left high bounce branch has coefficient (2a+6) divisible by four, also impossible at valuation one.

Hence neither P0 nor P2 has any source predecessor. Both are distinct from the initial section state, so both are blank-unreachable. The exact sum-16 iff then excludes Q, the W11 parent reduction excludes P, and the P4/B2 implications exclude the original B2 target.

## Validation boundary

`oddodd_sum16_blank_reach_iff` is an existing source-certified theorem. The no-predecessor arithmetic for P0/P2 and the composed W11/B2 reduction have not been Lean-compiled. The full `U5B2Root32.lean` dependency closure remains uncompiled; no CI was dispatched because the Critic gate requires exact-source local preflight first. This adds two conditional root-index cylinders, not a global Machine C or BB(6) solution.
