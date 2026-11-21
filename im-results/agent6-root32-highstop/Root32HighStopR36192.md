# Root32 high-stop exclusion: exact r = 167264 (mod 262144)

**Status:** intermediate exact source-parent composition. It excludes another infinite progression of the authentic B2/U5 high-stop target. Existing source grammar and blank-image theorems supply the inverse constraints; the affine arithmetic below is exact. The new composition has not yet been wrapped in one Lean theorem or compiled as a transitive import closure. It is not a Machine C decision or a BB(6) result.

## 1. Parameter cylinder

The existing B2/U5 inverse reduction gives
\[
CReach(T(u))\Longrightarrow CReach(D_{0E}(t))\lor CReach(L(t)),
\qquad u=1802+6720t.
\]
Take
\[
t=1167+4096p,\qquad q=(t-3)/4=291+1024p.
\]
Then q≡3 (mod 8), t≡3 (mod 4), and t≡15 (mod 16).

## 2. Exclude D0E

The forced D0E inverse chain, after its already-excluded direct fork, reaches R(t) through E7(t) and P(t). Section 4 of [RRoot32ExceptionalParentFan.md](../agent3-c-bounce-inverse/RRoot32ExceptionalParentFan.md) proves the complete R parent fan is empty for q≡3 (mod 8). Our q=291+1024p is in that cylinder. Hence R(t), and therefore D0E(t), is unreachable.

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
\qquad v=(t-3)/4=q=291+1024p.
\]

Write v=8m+3, where m=(v-3)/8=36+128p. The Q target is even/even, has right coordinate at least six, and has sum 2 modulo 8. The exact unique even-right inverse forces
\[
Q'=(151002951960m+72048060928,\;
37241415540m+17769002135).
\]
After substitution,
\[
Q'=(5508154331488+19328377850880p,\;
1358459961575+4766901189120p).
\]
Its sum-plus-one is
\[
Q'_x+Q'_y+1
=6866614293064+24095279040000p
=8(858326786633+3011909880000p),
\]
where the quotient is odd. Thus its exact 2-adic valuation is three.

The target Q' is even/odd, with right coordinate at least five. By section_preimage_all_iff, the zero-left, low, and high even-a branches fail by parity, and the a=1 high branch fails because the sum-plus-one is not divisible by 16. In the high odd-a branch, the depth d is even by the companion equation and d≤1 because 4 divides 2a+6. Hence d=0 is the only possible source depth.

The unique depth-zero parent is
\[
A=(3433307146529+12047639520000p,\;
2395883554051+8407270354560p).
\]
It is odd/odd, with right coordinate at least five, and
\[
A_x+A_y
=5829190700580+20454909874560p\equiv4\pmod{16}.
\]
The exact odd/odd low-valuation inverse forces
\[
B=(2914595350288+10227454937280p,\;
2655239452168+9317362645920p).
\]
B is even/even, its right coordinate is at least six, and
\[
B_x+B_y
=5569834802456+19544817583200p
=8(696229350307+2443102197900p).
\]
The quotient is 3 modulo 4. The exact even-even sum-zero parent theorem therefore leaves exactly two parents:
\[
\begin{aligned}
D={}&(5569834802454+19544817583200p,\;
1327619726083+4658681322960p),\\
E={}&(1392458700612+4886204395800p,\;
3416307777001+11987987916660p).
\end{aligned}
\]
Both have odd right coordinate at least five and coordinate sum congruent to 1 modulo 4:
\[
D_x+D_y=6897454528537+24203498906160p\equiv1\pmod4,
\]
\[
E_x+E_y=4808766477613+16874192312460p\equiv1\pmod4.
\]
The source-certified blank_no_odd_sum_one excludes both D and E. Thus B is unreachable, hence A, Q', Q(v), A0(t), P0(t), and L(t) are unreachable.

Both alternatives in the high-stop inverse reduction are excluded:
\[
\boxed{t\equiv1167\pmod{4096}
\Longrightarrow \neg CReach(T(1802+6720t)).}
\]

## 4. Translate to the exact root index

The saturated exact root equation in [B2Q0FourStepPath.md](../agent3-c-bounce-inverse/B2Q0FourStepPath.md) is
\[
17300+22155(t+j)=5\cdot2^{E-17},
\qquad r=32+64j.
\]
Since E-17 exceeds 4096, reduce the exact root equation modulo 4096. The inverse is
\[
22155^{-1}\equiv291\pmod{4096},
\]
so
\[
t+j\equiv3780\pmod{4096}.
\]
With \(t\equiv1167\pmod{4096}\), this gives
\[
j\equiv3780-1167\equiv2613\pmod{4096},
\]
and therefore
\[
\boxed{r=32+64j\equiv167264\pmod{262144}.}
\]
The exact-root saturation construction supplies a natural parameter for every \(j=2613+4096s\), \(s\ge0\), so this is a nonempty infinite progression. It is contained in the coarser \(r\equiv36192\pmod{65536}\) cylinder; the earlier reduction modulo 1024 established only that necessary coarse residue, not the exact class.

## 5. Scope and verification boundary

This is an additional infinite source-orbit exclusion for the B2/U5 high-stop target. Its exact root-index class r≡167264 (mod 262144), which lies inside r≡36192 (mod 65536), is disjoint from r≡9568 and 10592 (mod 16384), r≡7520 and 11616 (mod 32768), and r≡35168 and 64864 (mod 65536). It does not decide the remaining root32 classes, Machine C, or BB(6).

The composition uses existing exact source theorems (section_preimage_all_iff, the odd/odd sum-16 and low-valuation reachability equivalences, the even-right unique inverse, the even-even sum-zero parent theorem, the R exceptional-parent exclusion, and blank_no_odd_sum_one) plus the displayed affine arithmetic. The integrated composition still needs a Lean 4.36.0-rc2 wrapper, exact transitive import-closure compilation, and an exported axiom audit. Keep it in im-results/; do not promote it to results/ yet.
