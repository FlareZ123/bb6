# Root32 high-stop exclusion on r = 35168 (mod 65536)

**Status:** intermediate exact source-parent composition. This file records one of five disjoint infinite root-index progressions for the authentic B2/U5 high-stop target; the other four are linked in the index below. The arithmetic is exact and the source-parent reductions use existing source-certified theorems, but the compositions have not yet been wrapped in one Lean theorem or compiled as an integrated import closure. They are not a Machine C decision or a BB(6) result.

## Index of excluded root-index progressions

| Parameter cylinder | Exact root-index class | Detailed derivation |
|---|---|---|
| t≡159 (mod 1024) | r≡35168 (mod 65536) | This file |
| t≡79 (mod 512) | r≡7520 (mod 32768) | [Root32HighStopR7520.md](Root32HighStopR7520.md) |
| t≡719 (mod 1024) | r≡64864 (mod 65536) | [Root32HighStopR64864.md](Root32HighStopR64864.md) |
| t≡15 (mod 512) | r≡11616 (mod 32768) | [Root32HighStopR11616.md](Root32HighStopR11616.md) |
| t≡1167 (mod 4096) | r≡167264 (mod 262144) | [Root32HighStopR36192.md](Root32HighStopR36192.md) |

All five are intermediate source-parent compositions, not yet integrated Lean theorems. They are pairwise disjoint and disjoint from the previously recorded r≡9568 and 10592 (mod 16384) classes. Their shared reduction and root-saturation equations are given below; each child note records the additional inverse-parent arithmetic.

## 1. Parameter cylinder and existing reduction

Use the existing B2/U5 root32 parameterization
\[
u=1802+6720t,\qquad T(u)=(1048576u+70538,3).
\]
The consolidated inverse analysis in [B2Q0FourStepPath.md](../agent3-c-bounce-inverse/B2Q0FourStepPath.md) gives
\[
CReach(T(u))\Longrightarrow CReach(D_{0E}(t))\lor CReach(L(t)).
\]
Both alternatives must be excluded.

Take
\[
t=159+1024n,\qquad q=(t-3)/4=39+256n=8M+7,
\]
where
\[
M=4+32n.
\]
In particular, q is odd, q≡3 (mod 4), and M≡4 (mod 8).

## 2. Exclude the D0E alternative

The forced inverse chain from D0E, after its already-excluded direct fork, is
\[
D_{0E}(t)\to E_7(t)\to P(t)\to R(t),
\]
with
\[
R(t)=(2861931660t+767469219,\;2092249530t+561067594).
\]
Thus it suffices to show R(t) is blank-unreachable.

### 2.1. The exceptional odd-a parent of R is excluded

The complete R parent fan in [RRoot32ExceptionalParentFan.md](../agent3-c-bounce-inverse/RRoot32ExceptionalParentFan.md) has only the direct parent R'(t) and the displayed odd-a high-bounce family. Its valuation parameter is bounded by
\[
d\le1+v_2(W(q)),\qquad W(q)=2023885048+2477090595q.
\]
Since q is odd, W(q) is odd, so d≤1; the source companion equation forces d odd, hence d=1. The resulting parent is
\[
A_R(q)=(4047770093+4954181190q,\;
9490563232+11615770845q).
\]
It has odd right coordinate at least five, and
\[
(A_R)_x+(A_R)_y
=13538333325+16569952035q\equiv2\pmod4
\]
because q≡3 (mod 4). The source-certified blank_no_odd_sum_two excludes this parent.

### 2.2. The direct R parent is also excluded

The direct parent is
\[
R'(q)=(16191080381+19816724760q,\;
3418908091+4184499060q).
\]
For q=8M+7 its coordinates are odd, its right coordinate is at least five, and its sum is 12 modulo 16. The exact odd/odd low-valuation inverse therefore forces the parent
\[
P_1(M)=
(93809277604+96004895280M,\;
63259839556+64740443880M).
\]
After M=4+32n this becomes
\[
P_1=
(477828858724+3072156648960n,\;
322221615076+2071694204160n).
\]
It is even/even, its right coordinate is at least six, and
\[
P_{1,x}+P_{1,y}=8S_0,\qquad
S_0=100006309225+642981356640n\equiv1\pmod4.
\]
The exact eveneven_sumzero_blank_reach_parent theorem from M0EvenEvenSumZeroParents.lean therefore leaves exactly two possible parents:

\[
\begin{aligned}
D_R={}&(800050473798+5143850853120n,\;
161110807537+1035847102080n),\\
E_R={}&(200012618448+1285962713280n,\;
461129735209+2964791172000n).
\end{aligned}
\]

The right coordinate of E_R is odd and at least five, and its coordinate sum is
\[
661142353657+4250753885280n\equiv1\pmod4.
\]
Thus blank_no_odd_sum_one excludes E_R.

For D_R,
\[
D_{R,x}+D_{R,y}+1
=961161281336+6179697955200n
=8(120145160167+772462244400n),
\]
where the quotient is odd. D_R is even/odd, with right coordinate at least five. The complete source grammar section_preimage_all_iff leaves only its odd-a high branch: the zero-left branch fails since D_R's sum is 7 modulo 8; the a=1 branch would require 16 dividing the displayed sum-plus-one; the low and even-a branches have the wrong right-coordinate or sum parity. In the odd-a branch the depth d satisfies
\[
D_{R,x}+D_{R,y}+1=2^d(2a+6),\\
2k+a+7+3d=D_{R,x}+2D_{R,y}.
\]
The odd a makes 4 divide 2a+6, so the valuation gives d≤1. The second equation has an even right side and all terms except 3d are even, so d is even. Hence d=0, and the only possible parent is
\[
A_R'=(480580640665+3089848977600n,\;
320845724100+2062848039840n).
\]
Its right coordinate is even and at least six, and its sum is 5 modulo 8. The exact unique even-right inverse forces
\[
X_R=(801426364763+5152697017440n,\;
160422862049+1031424019920n).
\]
This is odd/odd, with right coordinate at least five, and
\[
X_{R,x}+X_{R,y}
=961849226812+6184121037360n\equiv12\pmod{16}.
\]
The exact odd/odd low-valuation inverse forces
\[
Y_R=(480924613404+3092060518680n,\;
320673737725+2061742269300n).
\]
Its right coordinate is odd and at least five, while
\[
Y_{R,x}+Y_{R,y}
=801598351129+5153802787980n\equiv1\pmod4.
\]
blank_no_odd_sum_one excludes Y_R. Therefore D_R is unreachable, then P_1, then R'(q). Both parent alternatives of R are excluded, so R and hence D0E(t) are unreachable.

## 3. Exclude the L alternative

The P7 residual is
\[
L(t)=(5065196640t+1358307257,\;
990617040t+265648583).
\]
For odd t, the source-certified odd/odd sum-16 parent theorem gives exactly P0(t) or P2(t), as detailed in [LRoot32OddParentReduction.md](../agent3-c-bounce-inverse/LRoot32OddParentReduction.md). Since t≡3 (mod 4), P2(t) has no source parent. Thus L(t) reachability forces P0(t), whose unique source parent is
\[
A_0(t)=(2518584390t+675395581,\;
2263923165t+607104414).
\]
Here t≡15 (mod 16); the sum of A_0(t) is 8 modulo 16. The exact odd/odd low-valuation inverse therefore forces
\[
Q(v)=(9565015110v+7815011328,\;
9310353885v+7606942617),
\qquad v=(t-3)/4=39+256n.
\]
Writing v=8m+7 with m=4+32n gives
\[
Q=(380850600618+2448643868160n,\;
370710744132+2383450594560n).
\]
Its right coordinate is even and at least six, and its sum is 6 modulo 8. The exact unique even-right inverse forces
\[
Q'=(751561344748+4832094462720n,\;
185355372065+1191725297280n).
\]
But
\[
Q'_x+Q'_y+1
=936916716814+6023819760000n\equiv2\pmod4.
\]
The target Q' is even/odd with right coordinate at least five. By section_preimage_all_iff, every possible source branch is impossible: the zero-left and even-a branches require an even target sum, the low branch requires an even right coordinate, and both the a=1 and odd-a high branches require 4 to divide the sum-plus-one. Thus Q' has no source predecessor and is not the blank initial state. It is unreachable. The even-right reachability equivalence then excludes Q(v), hence A_0(t), P0(t), and L(t).

Both alternatives in the T(u) inverse reduction are now excluded:
\[
\boxed{t\equiv159\pmod{1024}
\Longrightarrow \neg CReach(T(1802+6720t)).}
\]

## 4. Translate to an infinite root-index progression

The exact root equation from [B2Q0FourStepPath.md](../agent3-c-bounce-inverse/B2Q0FourStepPath.md) is
\[
17300+22155(t+j)=5\cdot2^{E-17},
\qquad r=32+64j.
\]
Its saturation construction proves that every j≥0 has a unique natural t satisfying the equation. Also E-17 is far greater than 1024, so reduction modulo 1024 gives
\[
17300+22155(t+j)\equiv0\pmod{1024}.
\]
Since 22155^{-1}≡291 (mod 1024), this is
\[
t+j\equiv708\pmod{1024}.
\]
Consequently t≡159 (mod 1024) is equivalent to j≡549 (mod 1024), and hence
\[
\boxed{r=32+64j\equiv35168\pmod{65536}.}
\]
The saturation construction supplies a natural exact-root parameter for every j=549+1024s, s≥0, so this is a nonempty infinite progression.

## 5. Scope and verification boundary

This is a third infinite source-orbit exclusion for the B2/U5 high-stop target, disjoint from the already recorded progressions r≡9568 and 10592 (mod 16384). It does not exclude the remaining root32 classes, decide Machine C, or determine BB(6).

The derivation uses existing exact source theorems (section_preimage_all_iff, the odd/odd low-valuation and sum-16 reachability equivalences, the even-right unique inverse, eveneven_sumzero_blank_reach_parent, and the odd-sum-one/two blank-image exclusions) plus the displayed affine arithmetic. The new composition itself still needs a Lean 4.36.0-rc2 wrapper, exact transitive import-closure compilation, and an exported axiom audit. Keep it in im-results/; do not promote it to results/ yet.
