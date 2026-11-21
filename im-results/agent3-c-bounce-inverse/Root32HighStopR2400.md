# Root32 high-stop extension: \(r\equiv2400\pmod{32768}\)

**Status:** intermediate exact source-parent composition. This strictly strengthens Agent 6's earlier \(r\equiv35168\pmod{65536}\) cylinder (the latter is contained in this one). The derivation below uses already source-certified parent/reachability theorems and exact affine arithmetic, but this wider composition has **not** yet been wrapped in Lean, compiled against its exact import closure, or axiom-audited. It is not a Machine C or BB(6) solution.

## 1. Parameter and the complete high-stop fork

Write the B2/U5 high-stop target as
\[
T(u)=(1048576u+70538,3),\qquad u=1802+6720t.
\]
The exact same-parameter B2-to-\(T\) path and its complete reverse parent reduction in [B2Q0FourStepPath.md](B2Q0FourStepPath.md) give
\[
CReach(T(u))\Longrightarrow CReach(D_{0E}(t))\ \lor\ CReach(L(t)).
\]
Both alternatives must be removed.

Take
\[
t=159+512s,\quad q=(t-3)/4=39+128s,\quad M=(q-7)/8=4+16s.
\]
Thus
\[
t\equiv15\pmod{16},\quad q\equiv7\pmod8,\quad M\equiv4\pmod{16}.
\]
The \(D_{0E}\) inverse chain is \(D_{0E}\to E_7\to P\to R(t)\), with
\[
R(t)=(2861931660t+767469219,\;2092249530t+561067594).
\]

## 2. Exclude the \(L(t)\) alternative

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
For \(q\equiv7\pmod8\), \(Q'_x\) is even and \(Q'_y\) is odd. Moreover,
\[
Q'_x+Q'_y+1
=\frac{47061091875q+38450850503}{2}.
\]
The numerator is \(4\pmod8\), since
\(47061091875\equiv3\), \(q\equiv7\), and
\(38450850503\equiv7\pmod8\). Hence
\[
Q'_x+Q'_y+1\equiv2\pmod4.
\]
The numerator is \(2\pmod3\): its coefficient is divisible by three and its constant is \(2\pmod3\). Division by two therefore gives
\[
Q'_x+Q'_y+1\equiv1\pmod3,
\quad\text{so}\quad 3\mid Q'_x+Q'_y.
\]
The source-certified blank_no_even_odd_three_divisible theorem (in U5B2Root32.lean) now excludes \(Q'(q)\): it has \(x>5\), even \(x\), odd \(y\ge5\), sum divisible by three, and sum-plus-one \(2\pmod4\). Reversing the exact reachability reductions excludes \(Q(q)\), \(A_0(t)\), \(P_0(t)\), and \(L(t)\).

## 3. Exclude the \(D_{0E}(t)\) alternative

The complete parent fan in [RRoot32ExceptionalParentFan.md](RRoot32ExceptionalParentFan.md) leaves exactly two possible source-parent types for \(R(t)\): its direct parent \(R'(q)\), or an odd-\(a\) high-bounce parent. Here \(q\) is odd, so the fan's valuation parameter
\[
W(q)=2023885048+2477090595q
\]
is odd and the odd-depth bound forces depth \(n=1\). Its unique affine parent has odd right coordinate and sum
\[
13538333325+16569952035q\equiv2\pmod4
\]
because \(q\equiv3\pmod4\). The source-certified blank_no_odd_sum_two theorem excludes this branch.

It remains to exclude the direct parent
\[
R'(q)=(16191080381+19816724760q,\;
       3418908091+4184499060q).
\]
Substitute \(q=8M+7\):
\[
R'(q)=(154908153701+158533798080M,\;
       32710401511+33475992480M).
\]
Its coordinates are odd and its sum is \(12\pmod{16}\). The exact odd/odd low-valuation inverse therefore forces
\[
P_1(M)=(93809277604+96004895280M,\;
        63259839556+64740443880M).
\]
This is even/even, and
\[
P_{1,x}+P_{1,y}=8S,\qquad
S=19633639645+20093167395M\equiv1\pmod4,
\]
where the last congruence uses \(M\equiv0\pmod4\). The exact even/even sum-zero parent theorem leaves precisely
\[
\begin{aligned}
D(M)&=(157069117158+160745339160M,\;
       31629919777+32370221940M),\\
E(M)&=(39267279288+40186334790M,\;
       90530838709+92649724125M).
\end{aligned}
\]

The \(E(M)\) parent has odd right coordinate and
\[
E_x+E_y=129798117997+132836058915M\equiv1\pmod4,
\]
so blank_no_odd_sum_one excludes it.

For \(D(M)\),
\[
D_x+D_y+1
=188699036936+193115561100M
=8(120145160167+386231122200s).
\]
The quotient is odd, so this has exact 2-adic valuation three. \(D\) is even/odd. In the complete original source grammar, its zero-left, \(a=1\), low, and even-\(a\) branches are impossible by parity or this valuation. In the odd-\(a\) high branch the companion cost equation forces the bounce depth \(n\) even; since \(2a+6\) is divisible by four and \(v_2(D_x+D_y+1)=3\), \(n\le1\), hence \(n=0\). The only possible parent is
\[
A(M)=(94349518465+96557780550M,\;
      62989719120+64464001245M).
\]
Its right coordinate is even and
\[
A_x+A_y=157339237585+161021781795M\equiv5\pmod8
\]
because \(M\equiv4\pmod8\). The unique even-right inverse forces
\[
X(M)=\left(
157339237583+161021781795M,\;
31494859559+32232000622M+\frac M2
\right).
\]
For \(M\equiv4\pmod{16}\), \(X_x\equiv11\) and \(X_y\equiv1\pmod{16}\). Thus \(X\) is odd/odd and \(X_x+X_y\equiv12\pmod{16}\). Its exact odd/odd low-valuation inverse is
\[
Y_x=\frac{X_x+X_y-4}{2},\qquad
Y_y=\frac{X_x+3X_y-10}{4}.
\]
The residues \(X_x\equiv11\), \(X_y\equiv1\pmod{16}\) give
\[
Y_y\equiv1\pmod4,\qquad Y_x+Y_y\equiv1\pmod4.
\]
In particular \(Y_y\) is odd and at least five. blank_no_odd_sum_one excludes \(Y\), then the exact inverse equivalences exclude \(X,A,D,P_1,R'(q)\). Both possible parent types of \(R(t)\) are excluded, so \(R(t)\), and therefore \(D_{0E}(t)\), is unreachable.

Combining Sections 2 and 3 gives
\[
\boxed{t\equiv159\pmod{512}\Longrightarrow
       \neg CReach(T(1802+6720t)).}
\]

## 4. Root-index translation and strict strengthening

The exact saturated root equation is
\[
17300+22155(t+j)=5\cdot2^{E-17},\qquad r=32+64j,
\]
and implies \(t+j\equiv708\pmod{1024}\). Therefore \(t\equiv159\pmod{512}\) is equivalent to \(j\equiv37\pmod{512}\), hence
\[
\boxed{r\equiv32+64\cdot37=2400\pmod{32768}.}
\]
The saturation construction supplies a natural exact-root parameter for every \(j=37+512n\), so this is a nonempty infinite progression. It strictly contains Agent 6's \(r\equiv35168\pmod{65536}\) class, since \(35168\equiv2400\pmod{32768}\).

## 5. Verification boundary

This is an exact paper-level composition of the existing original-source parent grammar, reachability equivalences, and blank-image invariants. It has not yet been formalized as a Lean theorem or compiled as an integrated import closure. Keep it in im-results/; do not promote it to results/ until a pinned Lean 4.36.0-rc2 compile and transitive axiom audit succeed.

The key existing dependencies are SectionAllInverse, OddOddLowVal, EvenRightUnique, EvenEvenParentFan, M0EvenEvenSumZero, HighSumTwo, LRoot32OddParentReduction.md, and RRoot32ExceptionalParentFan.md.
