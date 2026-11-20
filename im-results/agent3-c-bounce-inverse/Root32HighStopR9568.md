# Root32 high-stop exclusion on r = 9568 (mod 16384)

**Status:** a new infinite subfamily of the B2/U5 high-stop target is excluded by a composed original-source reachability argument. The arithmetic and parent formulas are exact. The complete composition has not yet been wrapped in one Lean theorem or compiled; this remains in im-results/ and is not a BB(6) solution.

## 1. Target and existing inverse reduction

Use the same parameter as the B2/U5 bridge:

\[
u=1802+6720t,\qquad
T(u)=(1048576u+70538,\;3).
\]

The consolidated inverse-parent analysis in B2Q0FourStepPath.md proves

\[
CReach(T(u))\Longrightarrow
CReach(D_{0E}(t))\ \lor\ CReach(L(t)),
\]

where

\[
D_{0E}(t)=(218624u+14700,\;414976u+27902)
\]

with \(u=1802+6720t\), and

\[
L(t)=(5065196640t+1358307257,\;990617040t+265648583).
\]

This is a reverse reachability implication, not merely the existence of a forward source edge. The two alternatives must both be excluded to exclude T.

## 2. Remove the D0E alternative when t = 15 mod 32

Write \(t=32m+15\). Then

\[
q=\frac{t-3}{4}=8m+3\equiv3\pmod8.
\]

The exact exceptional-R parent fan in RRoot32ExceptionalParentFan.md proves

\[
q\equiv3\pmod8\Longrightarrow
\neg CReach(R(3+4q)).
\]

The source chain from D0E to E7, then P, then R, is forced after the already-excluded direct fork. Thus

\[
t\equiv15\pmod{32}
\Longrightarrow \neg CReach(D_{0E}(t)).
\]

This removes the D0E/E7 alternative on the whole t=15 mod32 cylinder.

## 3. Remove the L alternative when t = 47 mod 256

Assume \(t=32m+15\), so \(t\) is odd and \(t\equiv3\pmod4\). The exact two-parent odd/odd sum-16 theorem gives P0(t) or P2(t). The LRoot32OddParentReduction.md analysis shows P2(t) has no source parent when \(t\equiv3\pmod4\). Therefore L reachability forces P0(t), then its unique parent

\[
A_0(t)=
(2518584390t+675395581,\;2263923165t+607104414).
\]

Since \(t\equiv15\pmod{16}\), the sum of A0(t) is \(8\pmod{16}\), so the odd/odd low-valuation inverse forces

\[
Q(v)=
(9565015110v+7815011328,\;
 9310353885v+7606942617),
\qquad v=\frac{t-3}{4}=8m+3.
\]

The target Q is even/even, has right coordinate at least six, and has coordinate sum \(2\pmod8\). The exact even-right inverse therefore forces its direct parent

\[
Q'(m)=
(151002951960m+72048060928,\;
 37241415540m+17769002135).
\]

Now specialize to \(m=8n+1\), equivalently \(t=256n+47\). Then

\[
Q'(m)=
\left(
1208023615680n+223051012888,\;
297931324320n+55010417675
\right).
\]

Write \(S=Q'_x+Q'_y\) and \(C=Q'_x+2Q'_y\). Exact arithmetic gives

\[
\begin{aligned}
S+1&=1505954940000n+278061430564
       \equiv4\pmod8,\\
C&=1803886264320n+333071848238.
\end{aligned}
\]

The complete source-parent grammar now has exactly one possible parent. Indeed, Q' is even/odd, so the a=0, low, and high even-a branches fail by parity; the a=1 high branch requires 16 to divide S+1, which is false; and the high odd-a branch has \(S+1=2^d(2a+6)\), where the odd a forces a factor of four. Since \(S+1\) has exact 2-adic valuation two, \(d=0\). The companion equation then gives

\[
A(n)=
(752977470000n+139030715279,\;
 525454397160n+97020566476).
\]

The right coordinate of A is even and at least six, and

\[
A_x+A_y=1278431867160n+236051281755
\equiv3\pmod8.
\]

The exact even-right inverse forces its direct parent

\[
X(n)=
(1278431867160n+236051281753,\;
 262727198580n+48510283237).
\]

Here the right coordinate is odd and at least five, while

\[
X_x+X_y=1541159065740n+284561564990
\equiv2\pmod4.
\]

The source-certified blank_no_odd_sum_two theorem excludes X. Hence Q', Q, A0, P0, and L are all unreachable when \(t\equiv47\pmod{256}\).

Together with Section 2, both alternatives in the T inverse reduction are now excluded:

\[
\boxed{t\equiv47\pmod{256}\Longrightarrow\neg CReach(T(1802+6720t)).}
\]

## 4. Translate to the exact root index

The exact root32 identity from D0EInverseArithmetic.lean is

\[
17300+22155(t+j)=5\cdot2^{E-17},
\qquad r=32+64j.
\]

Here \(E=201+3360w\) and \(w=6657+8192r\), so \(E-17\ge184\). The right side is therefore divisible by 256. Reducing modulo 256 gives

\[
148+139(t+j)\equiv0\pmod{256}.
\]

Since \(139^{-1}\equiv35\pmod{256}\),

\[
t+j\equiv196\pmod{256}.
\]

Thus \(t\equiv47\pmod{256}\) is equivalent to \(j\equiv149\pmod{256}\), and therefore to

\[
r=32+64j\equiv32+64\cdot149
\equiv9568\pmod{16384}.
\]

The exact-root saturation argument in B2Q0FourStepPath.md constructs a unique natural u (hence t) for every j≥0. Consequently this is a nonempty infinite root-index progression, not merely a formal residue class with no candidate instances.

The resulting high-stop exclusion is

\[
\boxed{
r\equiv9568\pmod{16384}
\Longrightarrow
\neg CReach(T(u))
}
\]

for the corresponding exact root32 parameters.

## 5. Scope and verification boundary

This excludes one infinite arithmetic progression of authentic root32 high-stop candidates. It does not exclude the full root32 family, the remaining t-classes, other stop families, or all six-state machines. It is not an exact BB(6) value.

The proof is assembled from:
- the source-certified B2/U5 reverse reduction \(T\Rightarrow D_{0E}\lor L\);
- the complete R exceptional parent fan and its q=3 mod8 exclusion;
- the odd L parent split and its exact P0/Q/Q' inverse chain;
- the original-source even-right and odd-right image exclusions;
- the exact root32 parameter equation and saturation.

The newly composed theorem still needs a single Lean 4.36.0-rc2 wrapper, exact import-closure compilation, and an axiom audit. Keep this result in im-results/ until that acceptance step succeeds. Do not describe it as a global density increment or as a BB(6) solution.
