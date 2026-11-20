# Root32 high-stop exclusion on r = 224 (mod 1024)

**Status:** an infinite subfamily of the B2/U5 high-stop target is excluded by an exact original-source parent argument. The complete composition is not yet wrapped in one Lean 4.36.0-rc2 theorem; keep it in im-results/. This is not a global Machine C or BB(6) result.

## 1. Target and root parameter

The existing reverse reduction is

\[
CReach(T(1802+6720t))
\Longrightarrow
CReach(D_{0E}(t))\lor CReach(L(t)),
\]

where \(T(u)=(1048576u+70538,3)\). We prove both alternatives impossible for \(t\equiv1\pmod{16}\).

## 2. Exclude D0E for t = 1 mod 4

The source-parent chain in D0EInverseReduction.md gives

\[
CReach(D_{0E}(t))\Longrightarrow CReach(E_7(t))
\Longrightarrow CReach(P(t))
\Longrightarrow CReach(R(t)).
\]

For \(t\equiv1\pmod4\), the R target has even right coordinate and

\[
R_x(t)+R_y(t)\equiv6t+5\pmod8
\] which is \(3\pmod8\) for both odd residue classes \(t\equiv1,5\pmod8\). The exact even-right inverse therefore forces the direct parent

\[
R'(t)=
(4954181190t+1328536811,\;
 1046124765t+280533796).
\]

This state has odd right coordinate and

\[
R'_x(t)+R'_y(t)
=6000305955t+1609070607
\equiv2\pmod4
\]

when \(t\equiv1\pmod4\). The source-certified blank_no_odd_sum_two theorem excludes it. Hence D0E(t) is unreachable for every \(t\equiv1\pmod4\).

## 3. Exclude L for t = 1 mod 16

The exact odd/odd sum-16 parent theorem gives the two possible parents P0(t) and P2(t) of L(t).

The P0 parent has its unique source parent

\[
A_0(t)=
(2518584390t+675395581,\;
 2263923165t+607104414).
\]

Its coordinates are odd and its sum is

\[
A_{0,x}(t)+A_{0,y}(t)
=4782507555t+1282499995
\equiv2\pmod4
\]
for \(t\equiv1\pmod4\). Thus blank_no_odd_sum_two excludes P0(t).

It remains to exclude P2(t). Write \(t=16n+1\). The exact P2 target is

\[
P_2(t)=
(756976710t+202994478,\;
 3144727005t+843304966).
\]

Its coordinate sum plus one factors as

\[
\begin{aligned}
P_{2,x}+P_{2,y}+1
&=5(780340743t+209259889)\\
&=40(1560681486n+123700079).
\end{aligned}
\]

The final factor is odd, so this quantity has exact 2-adic valuation three. P2 is even/odd, so the complete source-parent grammar leaves only the odd-a high branch: its factor \(2a+6\) is divisible by four, and the companion cost equation forces the bounce depth to be even. The valuation bound therefore forces depth zero. The unique parent is

\[
A(n)=
(31213629720n+2474001577,\;
 40764630900n+3231016773).
\]

Both coordinates are odd, and

\[
A_x(n)+A_y(n)
=71977260620n+5705018350
\equiv2\pmod4.
\]

The source-certified blank_no_odd_sum_two theorem excludes A(n), hence P2(t). Both P0 and P2 are impossible, so L(t) is unreachable for \(t\equiv1\pmod{16}\).

Combining Sections 2 and 3,

\[
\boxed{t\equiv1\pmod{16}
\Longrightarrow
\neg CReach(T(1802+6720t)).}
\]

## 4. Translate to root indices

The exact root32 identity gives

\[
17300+22155(t+j)=5\cdot2^{E-17},
\qquad r=32+64j.
\]

Its right side is divisible by 256, so

\[
t+j\equiv196\pmod{256}.
\]

Thus \(t\equiv1\pmod{16}\) is equivalent to \(j\equiv3\pmod{16}\), which gives

\[
\boxed{r=32+64j\equiv224\pmod{1024}.}
\]

The exact-root saturation construction in B2Q0FourStepPath.md supplies a natural t for every j≥0. This is therefore a nonempty infinite root-index progression.

## 5. Scope

This excludes the authentic B2/U5 high-stop target on \(r\equiv224\pmod{1024}\), a larger progression than either of the two narrower cylinders already recorded in Root32HighStopR9568.md and Root32HighStopR10592.md. The other root-index classes, other stop families, and the global BB(6) problem remain open. The composed proof still requires an integrated Lean compile and axiom audit.
