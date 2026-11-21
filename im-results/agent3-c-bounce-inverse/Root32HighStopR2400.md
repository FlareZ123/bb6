# Root32 high-stop attempted widening: exact residual and correction

**Correction:** the proposed extension to all \(t\equiv159\pmod{512}\) is **not proved**. The algebraic chain was correct through the final odd/odd inverse, but I initially treated \(M/2\pmod{16}\) as constant for \(M=4+16s\). In fact \(M/2=2+8s\), so the last residue depends on the parity of \(s\). For odd \(s\), the final target has sum \(3\pmod4\), not \(1\pmod4\), and the blank-image exclusion used in the even case does not apply. This file now records the valid reduction and the exact remaining family; it does **not** claim a new \(r\equiv2400\pmod{32768}\) exclusion.

## 1. Parameter and complete high-stop fork

Write
\[
T(u)=(1048576u+70538,3),\qquad u=1802+6720t.
\]
The same-parameter B2-to-\(T\) path and complete reverse parent reduction in [B2Q0FourStepPath.md](B2Q0FourStepPath.md) give
\[
CReach(T(u))\Longrightarrow CReach(D_{0E}(t))\ \lor\ CReach(L(t)).
\]

Take
\[
t=159+512s,\quad q=(t-3)/4=39+128s,\quad M=(q-7)/8=4+16s.
\]
Then \(t\equiv15\pmod{16}\), \(q\equiv7\pmod8\), and \(M\equiv4\pmod{16}\). The \(D_{0E}\) chain is \(D_{0E}\to E_7\to P\to R(t)\), where
\[
R(t)=(2861931660t+767469219,\;2092249530t+561067594).
\]

## 2. The L alternative is excluded throughout this cylinder

The exact two-parent theorem for \(L(t)\) gives \(P_0(t)\) or \(P_2(t)\). Since \(t\equiv3\pmod4\), \(P_2(t)\) has no source predecessor. The unique source parent of \(P_0(t)\) is \(A_0(t)\). Since \(t\equiv15\pmod{16}\), \(A_0(t)\) is odd/odd with sum \(8\pmod{16}\), so the exact odd/odd low-valuation inverse forces
\[
Q(q)=(9565015110q+7815011328,\;9310353885q+7606942617).
\]
Its right coordinate is even. The unique even-right inverse is
\[
Q'(q)=\left(
18875368995q+15421953943,\;
\frac{9310353885q+7606942615}{2}
\right).
\]
For \(q\equiv7\pmod8\), \(Q'_x\) is even and \(Q'_y\) is odd. Also
\[
Q'_x+Q'_y+1
=\frac{47061091875q+38450850503}{2}.
\]
The numerator is \(4\pmod8\), so the quotient is \(2\pmod4\). Its numerator is \(2\pmod3\), so the quotient is \(1\pmod3\); hence \(3\mid Q'_x+Q'_y\). The source-certified blank_no_even_odd_three_divisible theorem therefore excludes \(Q'(q)\). Reversing the exact reachability reductions excludes \(Q(q),A_0(t),P_0(t)\), and \(L(t)\), for every \(s\ge0\).

## 3. The odd-a parent of R is excluded throughout this cylinder

The complete parent fan in [RRoot32ExceptionalParentFan.md](RRoot32ExceptionalParentFan.md) leaves exactly two possible source-parent types for \(R(t)\): its direct parent \(R'(q)\), or an odd-\(a\) high-bounce parent. Here \(q\) is odd, so
\[
W(q)=2023885048+2477090595q
\]
is odd and the fan's odd-depth bound forces depth \(n=1\). The resulting affine parent has odd right coordinate and sum
\[
13538333325+16569952035q\equiv2\pmod4
\]
because \(q\equiv3\pmod4\). The source-certified blank_no_odd_sum_two theorem excludes this branch. This extension of the earlier \(q\equiv3\pmod8\) statement only uses \(q\) odd and \(q\equiv3\pmod4\), both true here.

## 4. Exact direct-R reduction and the parity split

The remaining direct parent is
\[
R'(q)=(16191080381+19816724760q,\;
       3418908091+4184499060q).
\]
Substitute \(q=8M+7\):
\[
R'(q)=(154908153701+158533798080M,\;
       32710401511+33475992480M).
\]
Its coordinates are odd and its sum is \(12\pmod{16}\). The exact odd/odd low-valuation inverse forces
\[
P_1(M)=(93809277604+96004895280M,\;
        63259839556+64740443880M).
\]
This is even/even, and
\[
P_{1,x}+P_{1,y}=8S,\qquad
S=19633639645+20093167395M\equiv1\pmod4.
\]
The even/even sum-zero parent theorem leaves exactly
\[
\begin{aligned}
D(M)&=(157069117158+160745339160M,\;
       31629919777+32370221940M),\\
E(M)&=(39267279288+40186334790M,\;
       90530838709+92649724125M).
\end{aligned}
\]
The E parent has odd right coordinate and sum
\[
E_x+E_y=129798117997+132836058915M\equiv1\pmod4,
\]
so blank_no_odd_sum_one excludes it.

For D,
\[
D_x+D_y+1
=188699036936+193115561100M
=8(120145160167+386231122200s).
\]
The quotient is odd, so the exact 2-adic valuation is three. D is even/odd. The complete original source grammar rules out the zero-left, \(a=1\), low, and even-\(a\) branches by parity or this valuation. In the odd-\(a\) high branch the companion cost equation forces the bounce depth \(n\) even; since \(2a+6\) is divisible by four, \(n\le1\), hence \(n=0\). The only possible parent is
\[
A(M)=(94349518465+96557780550M,\;
      62989719120+64464001245M).
\]
Its right coordinate is even and its sum is \(5\pmod8\). The unique even-right inverse forces
\[
X(M)=\left(
157339237583+161021781795M,\;
31494859559+32232000622M+\frac M2
\right).
\]
For \(M=4+16s\),
\[
X_x\equiv11\pmod{16},\qquad
X_y\equiv1+8s\pmod{16}.
\]
Thus the exact odd/odd low-valuation inverse gives
\[
Y_x=\frac{X_x+X_y-4}{2},\qquad
Y_y=\frac{X_x+3X_y-10}{4}.
\]

### Even s: the already-known excluded cylinder

If \(s\) is even, then \(X_y\equiv1\pmod{16}\). Consequently \(Y_y\equiv1\pmod4\) and \(Y_x+Y_y\equiv1\pmod4\). blank_no_odd_sum_one excludes Y, hence the entire direct-R branch. This is exactly \(t\equiv159\pmod{1024}\), already recorded by Agent 6 as
\[
r\equiv35168\pmod{65536}.
\]
This derivation does not strengthen that result.

### Odd s: the exact unresolved residual

If \(s=2n+1\), then
\[
t=671+1024n,\qquad M=20+32n,\qquad X_y\equiv9\pmod{16}.
\]
The low-valuation inverse now gives \(Y_y\equiv3\pmod4\) and \(Y_x+Y_y\equiv3\pmod4\), so blank_no_odd_sum_one does not apply. Expanding the exact formulas gives
\[
Y(n)=
(2026954872744+3092060518680n,\;
 1351544872375+2061742269300n).
\]
Here \(Y_x\equiv0\pmod8\), \(Y_y\equiv7+4n\pmod8\), and \(Y_x+Y_y\equiv3\pmod4\). None of the exclusions used in the even-s branch rules out this residual. The complete result of the present reduction is therefore
\[
CReach(T(1802+6720t))
\Longrightarrow CReach(Y(n))
\quad\text{when }t=671+1024n,
\]
after eliminating L, the odd-a R parent, and the E parent. The full reachability of this Y-family remains open, but two infinite subfamilies have now been excluded by further source-parent analysis: n≡7 (mod 8) and n≡13 (mod 16). See [Root32HighStopR2400Subfamilies.md](./Root32HighStopR2400Subfamilies.md), which translates them to r≡264544 (mod 524288) and r≡919904 (mod 1048576), respectively. The remaining n residues are still open.

## 5. Root-index interpretation

The exact saturated root equation
\[
17300+22155(t+j)=5\cdot2^{E-17},\qquad r=32+64j
\]
implies \(t+j\equiv708\pmod{1024}\).

- If \(s\) is even, \(t\equiv159\pmod{1024}\), giving the known \(r\equiv35168\pmod{65536}\) exclusion.
- If \(s\) is odd, \(t\equiv671\pmod{1024}\), giving \(j\equiv37\pmod{1024}\) and the unresolved root-index class
  \[
  r\equiv2400\pmod{65536}.
  \]

The proposed union \(r\equiv2400\pmod{32768}\) contains both classes, but only the \(35168\pmod{65536}\) half is excluded by the argument above. **Do not claim the wider class as a nonreachability result.**

## 6. Verification boundary

This is an exact paper-level reduction using the existing original-source parent grammar, reachability equivalences, and blank-image invariants. No new Lean theorem or integrated compile has been produced. Keep it in im-results/. The immediate mathematical target is the explicit Y(n) family above; a valid extension needs a new invariant or a complete source-parent analysis for this family.
