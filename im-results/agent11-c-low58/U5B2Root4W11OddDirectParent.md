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

## Root-index form of the odd-q branch

All W11 candidates have `r ≡ 4 (mod 16)`, so write `r=16R+4`. The divided root equation modulo 32 is
`9+22R+11w ≡ 0 (mod 32)`.
If `r ≡ 84 (mod 256)`, then `R ≡ 5 (mod 16)`, so `11w ≡ 9 (mod 32)`, hence `w ≡ 27 (mod 32)`. This is exactly `w=16q+11` with q odd. The complementary `r ≡ 212 (mod 256)` gives `w ≡ 11 (mod 32)`, i.e. q even, which is not covered by the reduction below.

## Exact parent fan for P(q): two candidates

Suppose P(q) is blank-reachable. Since x>5, it has a positive-length source predecessor (a,b). The complete original-source grammar section_preimage_all_iff leaves exactly two candidates:

- the direct parent
  \[
  Q(q)=(x+y-2,(y-2)/2)
      =(7021907149+9647698200q,\;
        1617666871+2222581620q);
  \]
- the high odd-a bounce parent
  \[
  A(q)=(a,b)=
  (1755476785+2411924550q,\;
   4250882050+5840468445q).
  \]

The other branches are excluded as follows. The zero-left recursive branch makes x+y divisible by eight, impossible because x+y is odd; its exceptional output is (0,4). The one-left finite outputs have right coordinate at most seven, while y≥12. Its high branch requires 16 | x+y+1, but
\[
x+y+1=8(877738394+1205962275q)
\]
has exact 2-adic valuation three for odd q. The k=0 branch has right output two. The even-a bounce branch makes x+y even. In the odd-a bounce branch the y=3 exception is impossible; the high branch has 4 | (2a+6), so the same valuation-three identity forces n≤1. Its cost equation forces n odd, hence n=1, and the two source equations give exactly A(q) above.

The final exclusion of A(q) depends on q's residue; it is **not** valid for every odd q.

- If \(q\equiv1\pmod4\), then
  \[
  a+b=6006358835+8252392995q\equiv2\pmod4.
  \]
  Since b is odd and at least five, the source-certified theorem blank_no_odd_sum_two excludes A(q).

- If \(q\equiv3\pmod{16}\), write q=16v+3. Then
  \[
  A(q)=
  (8991250435+38590792800v,\;
   21772287385+93447495120v).
  \]
  Its coordinates are odd, its right coordinate is at least five, and
  \[
  A_x+A_y=30763537820+132038287920v\equiv12\pmod{16}.
  \]
  Thus the source-certified oddodd_lowval_blank_reach_iff applies and reduces A(q) to
  \[
  D_A(v)=
  (15381768908+66019143960v,\;
   18577028145+79733319540v).
  \]
  Here \(D_{A,y}\) is odd and at least five, while
  \[
  D_{A,x}+D_{A,y}
  =33958797053+145752463500v\equiv1\pmod4.
  \]
  The source-certified theorem BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one excludes D_A(v), hence A(q) is unreachable.

Consequently the exact reduction
\[
CReach(P(q))\iff CReach(Q(q))
\]
is justified for \(q\equiv1\pmod4\) and, by the separate low-valuation argument above, for \(q\equiv3\pmod{16}\). It is **not established here** for q≡7, 11, or 15 (mod 16). In particular, oddness of q alone is insufficient.
## Remaining dyadic split

On the q-sectors where the alternate A(q) parent has been excluded (q≡1 mod4 or q≡3 mod16), the remaining direct parent Q(q) is odd/odd and
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
