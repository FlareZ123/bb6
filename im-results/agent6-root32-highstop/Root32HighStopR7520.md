# Root32 high-stop exclusion on r = 7520 (mod 32768)

**Status:** intermediate exact source-parent composition. It excludes another infinite progression of the authentic B2/U5 high-stop target. The source grammar and existing blank-image theorems are source-certified, and the displayed affine arithmetic is exact, but this new composition has not yet been wrapped in one Lean theorem or compiled as an integrated import closure. It is not a Machine C decision or a BB(6) result.

## 1. Parameter cylinder

The existing B2/U5 reduction gives
\[
CReach(T(u))\Longrightarrow CReach(D_{0E}(t))\lor CReach(L(t)),
\qquad u=1802+6720t.
\]
Take
\[
t=79+512s,\qquad q=(t-3)/4=19+128s.
\]
Then t is odd, t≡3 (mod 4), t≡15 (mod 16), and q≡3 (mod 8).

## 2. Exclude D0E

The forced inverse chain from D0E, after its already-excluded direct fork, reaches R(t) through E7(t) and P(t). The complete exceptional R parent fan in [RRoot32ExceptionalParentFan.md](../agent3-c-bounce-inverse/RRoot32ExceptionalParentFan.md), Section 4, proves
\[
q\equiv3\pmod8\Longrightarrow \neg CReach(R(3+4q)).
\]
Our q=19+128s is in this cylinder. Therefore R(t), and hence D0E(t), is unreachable.

## 3. Exclude L

The P7 residual is
\[
L(t)=(5065196640t+1358307257,\;
990617040t+265648583).
\]
For odd t, the exact odd/odd sum-16 parent theorem gives exactly P0(t) or P2(t), as recorded in [LRoot32OddParentReduction.md](../agent3-c-bounce-inverse/LRoot32OddParentReduction.md). Since t≡3 (mod 4), P2(t) has no source parent. Thus L(t) reachability forces P0(t), whose unique source parent is
\[
A_0(t)=(2518584390t+675395581,\;
2263923165t+607104414).
\]
The sum of A0(t) is 8 modulo 16 because t≡15 (mod 16). The exact odd/odd low-valuation inverse therefore forces
\[
Q(v)=(9565015110v+7815011328,\;
9310353885v+7606942617),
\qquad v=(t-3)/4=q=19+128s.
\]

Write v=8m+3, where
\[
m=(v-3)/8=2+16s.
\]
The Q target is even/even, its right coordinate is at least six, and its sum is 2 modulo 8. The exact unique even-right inverse therefore forces
\[
Q'=(151002951960m+72048060928,\;
37241415540m+17769002135).
\]
Substituting m=2+16s gives
\[
Q'=(374053964848+2416047231360s,\;
92251833215+595862648640s).
\]
In particular,
\[
Q'_x+Q'_y+1
=466305798064+3011909880000s
=16(29144112379+188244367500s).
\]
The quotient is odd and strictly greater than one.

The target Q' is even/odd, with right coordinate at least five. Apply the complete source grammar section_preimage_all_iff:

- The zero-left branch requires x+y even, but Q'_x+Q'_y is odd.
- The finite a=1 cases have right coordinate at most seven. Its high a=1 branch requires x+y+1=16·2^n. The displayed quotient is odd and greater than one, so it is not a power of two.
- The low branch requires an even right coordinate.
- The high even-a branch requires an even target sum.
- Only the high odd-a branch remains.

In that branch the depth d satisfies
\[
Q'_x+Q'_y+1=2^d(2a+6),\qquad
2k+a+7+3d=Q'_x+2Q'_y.
\]
Since a is odd, 4 divides 2a+6. The displayed sum-plus-one has exact 2-adic valuation four, so d≤2. The second equation has an even right side, while 2k+a+7 is even; hence d is even. Thus d=0 or d=2, with no other possible source parents.

For d=0 the unique parent is
\[
A_0'=(233152899029+1505954940000s,\;
162702366121+1050908794320s).
\]
Its right coordinate is odd and at least five, and
\[
A'_{0,x}+A'_{0,y}
=395855265150+2556863734320s\equiv2\pmod4.
\]
The source-certified blank_no_odd_sum_two excludes it.

For d=2 the unique parent is
\[
A_2'=(58288224755+376488735000s,\;
250134703255+1615641896820s).
\]
Its right coordinate is odd and at least five, and
\[
A'_{2,x}+A'_{2,y}
=308422928010+1992130631820s\equiv2\pmod4.
\]
The same blank_no_odd_sum_two theorem excludes it.

Thus Q' has no blank-reachable source parent and is not the initial state. It is unreachable. The even-right reachability equivalence then excludes Q(v), hence A0(t), P0(t), and L(t).

Both alternatives in the high-stop inverse reduction are now excluded:
\[
\boxed{t\equiv79\pmod{512}
\Longrightarrow \neg CReach(T(1802+6720t)).}
\]

## 4. Translate to the exact root index

The saturated exact root equation from [B2Q0FourStepPath.md](../agent3-c-bounce-inverse/B2Q0FourStepPath.md) is
\[
17300+22155(t+j)=5\cdot2^{E-17},
\qquad r=32+64j.
\]
Since E-17 exceeds 1024, reduction modulo 1024 gives
\[
t+j\equiv708\pmod{1024}.
\]
For t≡79 (mod 512), this implies
\[
j\equiv708-79\equiv117\pmod{512}.
\]
Therefore
\[
\boxed{r=32+64j\equiv7520\pmod{32768}.}
\]
The exact-root saturation construction supplies a natural parameter for every j=117+512s, s≥0, so this is a nonempty infinite progression.

## 5. Scope and verification boundary

This is an additional infinite source-orbit exclusion for the B2/U5 high-stop target. Its root-index class r≡7520 (mod 32768) is disjoint from the previously recorded classes r≡9568 and 10592 (mod 16384), and from the Agent 6 class r≡35168 (mod 65536). It does not decide the remaining root32 classes, Machine C, or BB(6).

The composition uses existing exact source theorems (section_preimage_all_iff, the odd/odd sum-16 and low-valuation reachability equivalences, the even-right unique inverse, the R exceptional-parent exclusion, and blank_no_odd_sum_two) plus the displayed affine arithmetic. The new integrated composition still needs a Lean 4.36.0-rc2 wrapper, exact transitive import-closure compilation, and an exported axiom audit. Keep it in im-results/; do not promote it to results/ yet.
