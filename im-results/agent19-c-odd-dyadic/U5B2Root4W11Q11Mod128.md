# W11 q = 11 (mod 128): both source-parent branches excluded

**Status:** exact paper-level infinite blank-orbit exclusion for the W11 parent family. The arithmetic and source-theorem composition below have not yet been assembled into a Lean theorem. Keep this in im-results/.

## Statement

Let
\[
P(q)=
(3786573407+5202534960q,\;
 3235333744+4445163240q).
\]
For every natural \(s\),
\[
\boxed{\neg CReach(P(128s+11)).}
\]

This is a new branch closure inside the W11 reduction. It does not by itself decide the full W11 sector, Machine C, or BB(6).

The exact residual root equation translates this family into
\[
\boxed{r\equiv11092\pmod{16384}}.
\]

## 1. Root-equation translation

Use the W11 root4 parameterization
\[
r=16R+4,\qquad u=542+840w,\qquad w=16q+11,
\]
and the exact residual equation
\[
E=201+3360(6657+8192r),\qquad
18018+211u+22155r=20\cdot2^{E-13}.
\]

The already derived root congruence
\[
(u+105r)\bmod1680=122
\]
gives \(u\equiv1382\pmod{1680}\), hence \(u=542+840w\) with \(w\) odd when \(r\equiv4\pmod{16}\).

Substitution and division by eight give the exact equality
\[
27625+44310R+22155w=5\cdot2^{E-14}.
\]
Since \(E\ge201\), the right side is zero modulo \(2048\).

Now
\[
r\equiv11092\pmod{16384}
\quad\Longleftrightarrow\quad
R\equiv693\pmod{1024}.
\]
Reducing the displayed equality modulo \(2048\) then yields
\[
27625+44310\cdot693+22155w\equiv0\pmod{2048},
\]
whose unique solution is
\[
w\equiv187\pmod{2048}.
\]
As \(w=16q+11\), this is exactly \(q\equiv11\pmod{128}\).

Conversely, \(q\equiv11\pmod{128}\) gives \(w\equiv187\pmod{2048}\), and the same root congruence forces \(R\equiv693\pmod{1024}\). Thus, among exact root-equation solutions in this W11 root4 branch,
\[
q\equiv11\pmod{128}
\quad\Longleftrightarrow\quad
r\equiv11092\pmod{16384}.
\]

## 2. The existing P(q) parent fan

The complete source-grammar reduction in U5B2Root4W11OddDirectParent.md shows that, for odd \(q\), every source predecessor of \(P(q)\) is one of exactly two states:
\[
Q(q)=
(7021907149+9647698200q,\;
 1617666871+2222581620q),
\]
or
\[
A(q)=
(1755476785+2411924550q,\;
 4250882050+5840468445q).
\]

The two branches must both be excluded. The earlier blanket exclusion of \(A(q)\) for \(q\equiv1\pmod4\) does not apply here, because \(q\equiv3\pmod4\).

Set \(q=128s+11\).

## 3. Direct parent Q(q): three exact inverse edges to the sum-one obstruction

For this parameterization,
\[
Q(q)=
(113146587349+1234905369600s,\;
 26066064691+284490447360s).
\]
Its coordinates are odd and its sum is \(8\pmod{16}\). The source-certified oddodd_lowval_blank_reach_iff therefore gives the exact parent
\[
D_Q=
(69606326018+759697908480s,\;
 47836195353+522094177920s).
\]

Here \(D_Q\) is even/odd, its right coordinate is at least five, and
\[
D_{Q,x}+D_{Q,y}+1\equiv4\pmod8.
\]
The source-certified evenodd_four_blank_reach_iff gives the unique parent
\[
R_Q=
(58721260683+640896043200s,\;
 53278728017+581495110560s).
\]

This is odd/odd with right coordinate at least five and sum \(12\pmod{16}\). A second application of oddodd_lowval_blank_reach_iff gives
\[
T_Q=
(55999994348+611195576880s,\;
 54639361181+596345343720s).
\]
Its right coordinate is odd and at least five, and
\[
T_{Q,x}+T_{Q,y}\equiv1\pmod4.
\]
The source-certified blank_no_odd_sum_one theorem excludes \(T_Q\). Reversing the exact reachability equivalences excludes \(R_Q,D_Q,Q(q)\).

## 4. Alternate parent A(q): three exact inverse edges to the sum-two obstruction

For the same parameterization,
\[
A(q)=
(28286646835+308726342400s,\;
 68496034945+747579960960s).
\]
It is odd/odd, its right coordinate is at least five, and its sum is \(4\pmod{16}\). Apply oddodd_lowval_blank_reach_iff:
\[
D_A=
(48391340888+528153151680s,\;
 58443687915+637866556320s).
\]

The target \(D_A\) is even/odd and satisfies
\[
D_{A,x}+D_{A,y}+1\equiv4\pmod8.
\]
The exact evenodd_four_blank_reach_iff gives
\[
R_A=
(53417514399+583009854000s,\;
 55930601156+610438205160s).
\]

Now \(R_A\) has odd left coordinate, even right coordinate at least six, and total sum \(3\pmod8\). The source-certified unique even-right predecessor theorem applies, giving
\[
T_A=
(109348115553+1193448059160s,\;
 27965300577+305219102580s).
\]
Both coordinates of \(T_A\) are odd, its right coordinate is at least five, and
\[
T_{A,x}+T_{A,y}\equiv2\pmod4.
\]
The source-certified blank_no_odd_sum_two theorem excludes \(T_A\). Hence \(R_A,D_A,A(q)\) are also blank-unreachable.

## 5. Lift to the B2 root-index cylinder

Let
\[
B(u)=(734+10944u,\;34881+518816u)
\]
be the B2 residual state. The source-side argument below proves the stronger parameterized exclusion
\[
\boxed{\forall s\in\mathbb N,\quad
\neg CReach(1725015902+18827182080s,\;
81776850433+892529541120s).}
\]
Equivalently, \(B(u)\) is blank-unreachable for every
\[
u=157622+1720320s.
\]
This source exclusion does not itself require the root equation.

For the root connection, suppose \(r,E,u\) satisfy the exact root equation and
\[
r\equiv11092\pmod{16384}.
\]
The root calculation above gives \(u=542+840w\), with
\[
w=2048s+187,\qquad u=157622+1720320s
\]
for some natural \(s).

The established source-accepted implication b2_even_reach_implies_p4_reach applies because \(u\) is even. Thus B2 reachability would imply reachability of
\[
P4(u)=(63895+950614u,\;3291+48981u).
\]
In terms of \(w\),
\[
P4(w)=(515296683+798515760w,\;
       26550993+41144040w).
\]
For \(w=2048s+187\), this is
\[
P4_s=(149837743803+1635360276480s,\;
      7720486473+84262993920s).
\]
It is odd/odd, its right coordinate is at least five, and its sum is \(4\pmod{16}\). The source-certified oddodd_lowval_blank_reach_iff therefore reduces it to
\[
D_s=(78779115136+859811635200s,\;
     43249800803+472037314560s).
\]

The target \(D_s=(x,y)\) is even/odd, \(x>5\), \(y\ge5\), and
\[
(x+y)\equiv0\pmod3,\qquad x+y+1\equiv4\pmod8.
\]
The source-accepted even_odd_three_divisible_parent theorem in U5B2Root32.lean says that any original-section predecessor \((a,k)\) has \(a\) odd, an even depth \(n\), and
\[
x+y+1=2^n(2a+6),\qquad
2k+a+7+3n=x+2y.
\]
Because \(2a+6\) is divisible by four and \(x+y+1\) has exact 2-adic valuation two, necessarily \(n=0\). Solving the two equations gives
\[
(a,k)=
(61014457967+665924474880s,\;
 52132129384+568980894720s)
=P(128s+11).
\]
Consequently, B2 reachability would imply \(P(128s+11)\) reachability, contradicting the two-branch exclusion above.

Thus the W11 root4 cylinder
\[
\boxed{r\equiv11092\pmod{16384}}
\]
is excluded at the paper-argument level for the B2 residual, not merely for the intermediate P(q) state.

## 6. Conclusion

For every exact B2 root-equation solution in this W11 root4 cylinder, the B2 state is not blank-reachable. This is an infinite conditional root-index exclusion. The class has r≡20 (mod 64), so it is disjoint from the separate root32 high-stop domain r≡32 (mod 64); it is not an additional member of the nine-class root32 union. It does not close the other root-index residues, decide Machine C, or determine BB(6).

## Exact dependencies and validation boundary

The branch closure uses the existing source-level results:
- oddodd_lowval_blank_reach_iff from OddOddLowVal.lean;
- evenodd_four_blank_reach_iff from EvenOddFourExact.lean;
- the unique even-right reachability equivalence from EvenRightUnique.lean;
- blank_no_odd_sum_one from M0EvenEvenSumZero.lean;
- blank_no_odd_sum_two from HighSumTwo.lean.

The P(q) two-parent fan and the upstream B2-to-P(q) composition are not yet one compiled Lean theorem. The formulas above were independently reconstructed with exact integer arithmetic, including the root congruence modulo \(2048\). No claim of kernel verification is made.

The local shell and Python execution boundaries both returned ClientError when tested. In accordance with the current Critic acceptance gate, no CI substitute was dispatched and no workflow was added. The next useful step is one exact-source Lean composition after local preflight becomes available, not another residue-class enumeration.
