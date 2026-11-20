# Root32 high-stop exclusion on r = 64864 (mod 65536)

**Status:** intermediate exact source-parent composition. It excludes another infinite progression of the authentic B2/U5 high-stop target. The source grammar and blank-image invariants are source-certified; the displayed affine arithmetic is exact. The new integrated composition has not yet been wrapped in one Lean theorem or compiled as a transitive import closure. It is not a Machine C decision or a BB(6) result.

## 1. Parameter cylinder

The existing B2/U5 inverse reduction gives
\[
CReach(T(u))\Longrightarrow CReach(D_{0E}(t))\lor CReach(L(t)),
\qquad u=1802+6720t.
\]
Take
\[
t=719+1024p,\qquad q=(t-3)/4=179+256p.
\]
Then q≡3 (mod 8), t≡3 (mod 4), and t≡15 (mod 16).

## 2. Exclude D0E

The forced D0E inverse chain, after its already-excluded direct fork, reaches R(t) through E7(t) and P(t). Section 4 of [RRoot32ExceptionalParentFan.md](../agent3-c-bounce-inverse/RRoot32ExceptionalParentFan.md) proves the complete R parent fan is empty for q≡3 (mod 8). Our q=179+256p is in that cylinder. Hence R(t), and therefore D0E(t), is unreachable.

## 3. Exclude L

The P7 residual is
\[
L(t)=(5065196640t+1358307257,\;
990617040t+265648583).
\]
For odd t, the exact odd/odd sum-16 parent theorem gives P0(t) or P2(t), as recorded in [LRoot32OddParentReduction.md](../agent3-c-bounce-inverse/LRoot32OddParentReduction.md). Since t≡3 (mod 4), P2(t) has no source parent. Thus L(t) reachability forces P0(t), whose unique source parent is
\[
A_0(t)=(2518584390t+675395581,\;
2263923165t+607104414).
\]
The sum of A0(t) is 8 modulo 16 because t≡15 (mod 16). The exact odd/odd low-valuation inverse forces
\[
Q(v)=(9565015110v+7815011328,\;
9310353885v+7606942617),
\qquad v=(t-3)/4=q=179+256p.
\]

Write v=8m+3, with m=(v-3)/8=22+32p. The Q target is even/even, has right coordinate at least six, and has sum 2 modulo 8. The exact unique even-right inverse forces
\[
Q'=(151002951960m+72048060928,\;
37241415540m+17769002135).
\]
Substituting m=22+32p:
\[
Q'=(3394113004048+4832094462720p,\;
837080144015+1191725297280p).
\]
Consequently
\[
Q'_x+Q'_y+1
=4231193148064+6023819760000p
=32(132224785877+188244367500p).
\]
The quotient is odd and greater than one, so the exact 2-adic valuation is five.

The target Q' is even/odd with right coordinate at least five. By the complete source grammar section_preimage_all_iff, the zero-left, low, and high even-a branches fail by parity. The finite a=1 cases fail because the right coordinate is large; its high branch would require
\[
Q'_x+Q'_y+1=16\cdot2^n,
\]
which is impossible: the exact valuation five would force n=1 and hence (Q'_x+Q'_y+1)/32=1, whereas the displayed quotient is greater than one. Only the high odd-a branch remains. Its depth d satisfies
\[
Q'_x+Q'_y+1=2^d(2a+6),\qquad
2k+a+7+3d=Q'_x+2Q'_y.
\]
Since a is odd, 4 divides 2a+6, so d≤3. The companion equation has an even right side and 2k+a+7 is even, so d is even. Therefore d=0 or d=2.

For d=0 the only parent is
\[
A_0'=(2115596574029+3011909880000p,\;
1476338359021+2101817588640p).
\]
Its right coordinate is odd and at least five, and
\[
A'_{0,x}+A'_{0,y}
=3591934933050+5113727468640p\equiv2\pmod4.
\]
The source-certified blank_no_odd_sum_two excludes it.

For d=2 the only parent is
\[
A_2'=(528899143505+752977470000p,\;
2269687074280+3231283793640p).
\]
Its right coordinate is even and at least six, and
\[
A'_{2,x}+A'_{2,y}
=2798586217785+3984261263640p\equiv1\pmod8.
\]
The exact unique even-right inverse forces
\[
X=(2798586217783+3984261263640p,\;
1134843537139+1615641896820p).
\]
This state has odd right coordinate at least five and
\[
X_x+X_y
=3933429754922+5599903160460p\equiv2\pmod4.
\]
The source-certified blank_no_odd_sum_two excludes X. Hence neither possible source parent of Q' is blank-reachable, so Q' is unreachable. The even-right reachability equivalence then excludes Q(v), A0(t), P0(t), and L(t).

Both alternatives in the high-stop inverse reduction are excluded:
\[
\boxed{t\equiv719\pmod{1024}
\Longrightarrow \neg CReach(T(1802+6720t)).}
\]

## 4. Translate to the exact root index

The saturated exact root equation in [B2Q0FourStepPath.md](../agent3-c-bounce-inverse/B2Q0FourStepPath.md) is
\[
17300+22155(t+j)=5\cdot2^{E-17},
\qquad r=32+64j.
\]
Since E-17 exceeds 1024, it gives t+j≡708 (mod 1024). Thus t≡719 (mod 1024) implies
\[
j\equiv708-719\equiv1013\pmod{1024},
\]
and
\[
\boxed{r=32+64j\equiv64864\pmod{65536}.}
\]
The existing exact-root saturation construction supplies a natural parameter for every j=1013+1024s, s≥0, so this is a nonempty infinite progression.

## 5. Scope and verification boundary

This is an additional infinite source-orbit exclusion for the B2/U5 high-stop target. Its root-index class r≡64864 (mod 65536) is disjoint from r≡9568 and 10592 (mod 16384), r≡7520 (mod 32768), and r≡35168 (mod 65536). It does not decide the remaining root32 classes, Machine C, or BB(6).

The composition uses existing exact source theorems (section_preimage_all_iff, the odd/odd sum-16 and low-valuation reachability equivalences, the even-right unique inverse, the R exceptional-parent exclusion, and blank_no_odd_sum_two) plus the displayed affine arithmetic. The integrated composition still needs a Lean 4.36.0-rc2 wrapper, exact transitive import-closure compilation, and an exported axiom audit. Keep it in im-results/; do not promote it to results/ yet.
