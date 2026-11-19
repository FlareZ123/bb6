# U5 B2 root4: odd q in the w = 11 (mod 16) sector

**Status:** exact source-parent reduction, not a reachability exclusion. Derived 2026-11-19; not Lean-formalized or compiled. Keep in `im-results/`.

Assume the same exact B2 residual root equation and the root4 parameterization
[
u=542+840w,\qquad w=16q+11,
]
with (q) odd.

As in the W7/W15 reductions, P4's odd/odd low-valuation inverse gives
[
D(w)=(270923836+419829900w,\;
      148737413+230486970w).
]
Here (D_x+D_y+1=419661250+650316870w\equiv4\pmod8), so (v_2(D_x+D_y+1)=2). The drafted even/odd three-divisible parent classification forces depth zero and the unique possible parent
[
P(q)=(x,y)=
(3786573407+5202534960q,\;
 3235333744+4445163240q).
]
It has (x) odd, (y) even, (x+y\equiv7\pmod8), (x\equiv3\pmod4), and (y\equiv0\pmod8).

## Exact parent fan for P(q), q odd

Suppose (P(q)) is blank-reachable. Since (x>5), it has a positive-length source predecessor ((a,b)). Apply the complete original-source grammar `section_preimage_all_iff`.

- The (a=0) recursive branch would make (x+y) divisible by eight, impossible because (x+y) is odd. Its exceptional (k=1) output is ((0,4)), not this target.
- The (a=1) finite outputs have right coordinate at most seven, while (y\ge12). Its high branch requires (16\mid x+y+1). But
  [
  x+y+1=7021907152+9647698200q
        =8(877738394+1205962275q).
  ]
  For odd (q), the factor in parentheses is odd, so this has exact valuation three; the (a=1) high branch is impossible.
- The (a\ge2,b=0) branch has right output two, impossible.
- The even-(a) bounce branch makes (x+y) even, impossible.
- The odd-(a) bounce branch has a (y=3) exception, also impossible. In its high branch, (4\mid(2a+6)), so (2^{n+2}\mid x+y+1). The valuation-three identity gives (n\le1). The cost equation has odd right side (x+2y), while (2b+a+7+3n) has parity (n); hence (n) is odd and therefore (n=1).

For this sole possible odd-(a) bounce depth, the two source equations force
[
a=1755476785+2411924550q,
\]
[
b=4250882050+5840468445q.
]
For odd (q), (a) is odd, (b\ge5) is odd, and
[
a+b=6006358835+8252392995q\equiv2\pmod4.
]
This contradicts the source-certified blank-image obstruction `blank_no_odd_sum_two`.

Consequently **every** possible predecessor of (P(q)) is the direct parent
[
Q(q)=(x+y-2,(y-2)/2)
]
with
[
Q(q)=
(7021907149+9647698200q,\;
 1617666871+2222581620q).
]
The direct edge (Q(q)\to P(q)) is genuine by the direct branch of `section_preimage_all_iff`. Thus the exact reduction is
[
CReach(P(q))\iff CReach(Q(q))
\qquad(q\text{ odd}).
]

## Remaining dyadic split

The direct parent (Q(q)) is odd/odd and
[
Q_x+Q_y=8639574020+11870279820q
       =4(2159893505+2967569955q).
]
For odd (q):
- if (q\equiv3\pmod4), the parenthesized factor is (2\pmod4), so (v_2(Q_x+Q_y)=3) and the existing odd/odd low-valuation inverse applies;
- if (q\equiv1\pmod4), the parenthesized factor is divisible by four, so (16\mid Q_x+Q_y); the low-valuation inverse does not apply and a higher-valuation parent fan remains.

Even (q) is not covered: the (a=1) branch or higher odd-(a) bounce depths may survive. This note is a source-grammar reduction only; it does not exclude the w=11 sector or decide Machine C/BB(6).

## Validation boundary

The exact preimage grammar `section_preimage_all_iff` and `blank_no_odd_sum_two` are existing source-certified lemmas. The arithmetic and branch elimination above are manually derived; the composed theorem has not been Lean-formalized or compiled. The D-parent classification and B2-to-P4 implication are still in the uncompiled `U5B2Root32.lean` closure. No CI was dispatched because the current Critic gate requires exact-source local preflight first.
