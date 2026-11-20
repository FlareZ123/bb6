# Root32 high-stop exclusion on r = 11616 (mod 32768)

**Status:** intermediate exact source-parent composition. It excludes another infinite progression of the authentic B2/U5 high-stop target. The source grammar and blank-image invariants are source-certified; the affine arithmetic below is exact. The new integrated composition has not yet been wrapped in one Lean theorem or compiled as a transitive import closure. It is not a Machine C decision or a BB(6) result.

## 1. Parameter cylinder

The existing B2/U5 inverse reduction gives
\[
CReach(T(u))\Longrightarrow CReach(D_{0E}(t))\lor CReach(L(t)),
\qquad u=1802+6720t.
\]
Take
\[
t=15+512n,\qquad q=(t-3)/4=3+128n.
\]
Then q≡3 (mod 8), t≡3 (mod 4), and t≡15 (mod 16).

## 2. Exclude D0E

The forced D0E inverse chain, after its already-excluded direct fork, reaches R(t) through E7(t) and P(t). Section 4 of [RRoot32ExceptionalParentFan.md](../agent3-c-bounce-inverse/RRoot32ExceptionalParentFan.md) proves the complete R parent fan is empty for q≡3 (mod 8). Our q=3+128n is in that cylinder. Hence R(t), and therefore D0E(t), is unreachable.

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
\qquad v=(t-3)/4=q=3+128n.
\]

Write v=8m+3, where m=(v-3)/8=16n. The Q target is even/even, has right coordinate at least six, and has sum 2 modulo 8. The exact unique even-right inverse forces
\[
Q'=(151002951960m+72048060928,\;
37241415540m+17769002135).
\]
Substituting m=16n:
\[
Q'=(72048060928+2416047231360n,\;
17769002135+595862648640n).
\]
Its sum-plus-one is
\[
Q'_x+Q'_y+1
=89817063064+3011909880000n
=8(11227132883+376488735000n),
\]
with odd quotient, so its exact 2-adic valuation is three.

The target Q' is even/odd, with right coordinate at least five. By the complete source grammar section_preimage_all_iff, the zero-left, low, and high even-a branches fail by parity. The a=1 high branch would require 16 to divide the sum-plus-one, but its valuation is only three. In the high odd-a branch the depth d is even by the companion equation, and d≤1 because 4 divides 2a+6. Hence d=0 is the only possible source depth.

The unique depth-zero parent is
\[
A=(44908531529+1505954940000n,\;
31338766831+1050908794320n).
\]
It is odd/odd, with right coordinate at least five, and
\[
A_x+A_y
=76247298360+2556863734320n\equiv8\pmod{16}.
\]
The exact odd/odd low-valuation inverse forces
\[
B=(38123649178+1278431867160n,\;
34731208003+1164670330740n).
\]
B has even left and odd right coordinate at least five, and
\[
B_x+B_y
=72854857181+2443102197900n\equiv1\pmod4.
\]
The source-certified blank_no_odd_sum_one excludes B. Thus A, Q', Q(v), A0(t), P0(t), and L(t) are unreachable.

Both alternatives in the high-stop inverse reduction are excluded:
\[
\boxed{t\equiv15\pmod{512}
\Longrightarrow \neg CReach(T(1802+6720t)).}
\]

## 4. Translate to the exact root index

The saturated exact root equation in [B2Q0FourStepPath.md](../agent3-c-bounce-inverse/B2Q0FourStepPath.md) is
\[
17300+22155(t+j)=5\cdot2^{E-17},
\qquad r=32+64j.
\]
Since E-17 exceeds 1024, it gives t+j≡708 (mod 1024). Thus t≡15 (mod 512) implies
\[
j\equiv708-15\equiv181\pmod{512},
\]
and
\[
\boxed{r=32+64j\equiv11616\pmod{32768}.}
\]
The existing exact-root saturation construction supplies a natural parameter for every j=181+512s, s≥0, so this is a nonempty infinite progression.

## 5. Scope and verification boundary

This is an additional infinite source-orbit exclusion for the B2/U5 high-stop target. Its root-index class r≡11616 (mod 32768) is disjoint from r≡9568 and 10592 (mod 16384), r≡7520 (mod 32768), and r≡35168 and 64864 (mod 65536). It does not decide the remaining root32 classes, Machine C, or BB(6).

The composition uses existing exact source theorems (section_preimage_all_iff, the odd/odd sum-16 and low-valuation reachability equivalences, the even-right unique inverse, the R exceptional-parent exclusion, and blank_no_odd_sum_one) plus the displayed affine arithmetic. The integrated composition still needs a Lean 4.36.0-rc2 wrapper, exact transitive import-closure compilation, and an exported axiom audit. Keep it in im-results/; do not promote it to results/ yet.
