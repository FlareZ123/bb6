# Root32 P7 direct-parent residual: exact odd-parameter reduction

**Status:** intermediate original-source reachability reduction. The source grammar used below is certified by BB6.Agent46.section_preimage_all_iff and the two-parent reachability theorem by BB6.Agent3.oddodd_sum16_blank_reach_iff. The affine calculations and branch eliminations in this note have not yet been wrapped in a new Lean theorem or compiled as an integrated module. This is not a Machine C nonreachability proof or a BB(6) result.

## 1. Starting family and the two exact parents

The P7 direct-parent branch in the B2/U5 root32 analysis reduces to

\[
L(t)=(5065196640t+1358307257,\;990617040t+265648583).
\]

For odd \(t\), both coordinates are odd, the right coordinate is at least 64, and

\[
L_x+L_y=6055813680t+1623955840\equiv16\pmod{32}.
\]

The source-certified theorem oddodd_sum16_blank_reach_iff therefore gives exactly two possible source parents:

\[
\begin{aligned}
P_0(t)&=(3027906840t+811977918,\;2009261940t+538813249),\\
P_2(t)&=(756976710t+202994478,\;3144727005t+843304966).
\end{aligned}
\]

Thus \(L(t)\) is blank-reachable iff at least one of \(P_0(t)\) and \(P_2(t)\) is blank-reachable.

## 2. The P0 parent has one exact source parent

Write \(S_0=P_{0,x}+P_{0,y}\). Direct arithmetic gives

\[
S_0=5037168780t+1350791167,\qquad
S_0\equiv3\pmod8,\qquad S_0+1\equiv4\pmod8
\]

for every odd \(t\). Also \(P_{0,x}\) is even and \(P_{0,y}\) is odd and greater than five.

Apply the complete grammar section_preimage_all_iff to a putative source edge into \(P_0(t)\):

- The \(a=0\) recursive branch requires \(P_{0,x}+P_{0,y}=8\cdot2^n\), impossible because \(S_0\) is odd. The exceptional \(a=0,k=0,1\) cases have right coordinate at most four.
- The finite \(a=1,k\le3\) cases have right coordinate at most seven. The high \(a=1\) branch requires \(16\mid S_0+1\), contradicted by \(S_0+1\equiv4\pmod8\).
- The low \(a\ge2\) branch has even right coordinate, contrary to \(P_{0,y}\) odd.
- The high even-\(a\) branch requires \(S_0\) even, also impossible.
- In the high odd-\(a\) branch, the \(y=3\) exception is impossible. The remaining equation is
  \[
  S_0+1=2^n(2a+6).
  \]
  Since \(a\) is odd, \(2a+6=2(a+3)\) is divisible by four. Since \(S_0+1\) has exact 2-adic valuation two, necessarily \(n=0\).

The second source equation then fixes the only possible predecessor:

\[
A_0(t)=
(2518584390t+675395581,\;2263923165t+607104414).
\]

Consequently,

\[
P_0(t)\text{ reachable}\Longrightarrow A_0(t)\text{ reachable}.
\]

Both coordinates of \(A_0(t)\) are odd for odd \(t\), and its coordinate sum is

\[
H(t)=4782507555t+1282499995.
\]

If \(t\equiv1\pmod4\), then \(H(t)\equiv2\pmod4\), and the right coordinate is odd and at least five. The source-certified blank_no_odd_sum_two theorem excludes \(A_0(t)\). Hence

\[
t\equiv1\pmod4\Longrightarrow \neg CReach(P_0(t)).
\]

## 3. The P2 parent has no source parent when t = 3 mod 4

For odd \(t\), \(P_{2,x}\) is even, \(P_{2,y}\) is odd and at least five, and

\[
S_2=P_{2,x}+P_{2,y}
=3901703715t+1046299444
\]

is odd. If \(t\equiv3\pmod4\), then

\[
S_2+1\equiv 2\pmod4.
\]

There is no source predecessor at all:

- The \(a=0\) recursive branch requires \(S_2\) even; its small cases are incompatible with \(P_{2,y}\ge5\).
- The finite \(a=1,k\le3\) cases are too small. The high \(a=1\) branch requires \(16\mid S_2+1\), impossible.
- The low \(a\ge2\) branch requires even right coordinate.
- The high even-\(a\) branch requires even \(S_2\).
- The high odd-\(a\) branch requires \(4\mid S_2+1\), because \(2(a+3)\) is divisible by four for odd \(a\). This contradicts \(S_2+1\equiv2\pmod4\).

Therefore

\[
t\equiv3\pmod4\Longrightarrow \neg CReach(P_2(t)).
\]

This is a complete no-parent argument against the unbounded original-source grammar, not a bounded reverse-tree search.

## 4. Disjoint surviving family and a new infinite exclusion

Combining the two parent analyses with the exact two-parent theorem gives the sharper disjoint reduction

\[
\boxed{
\begin{aligned}
t\equiv1\pmod4,\ CReach(L(t))
&\Longrightarrow CReach(P_2(t)),\\
t\equiv3\pmod4,\ CReach(L(t))
&\Longrightarrow CReach(P_0(t)).
\end{aligned}}
\]

In particular, the \(P_0\) branch can be eliminated on one further infinite cylinder. If \(t\equiv3\pmod{16}\), write \(t=4v+3\), so \(v\equiv0\pmod4\). Then

\[
H(t)\equiv4\pmod{16}.
\]

The odd/odd low-valuation reachability equivalence applies to \(A_0(t)\) and forces its unique low-valuation parent

\[
Q(v)=
(9565015110v+7815011328,\;
9310353885v+7606942617).
\]

For \(v\equiv0\pmod4\), this target has even first coordinate, odd second coordinate at least five, and coordinate sum congruent to one modulo four. The source-certified blank_no_odd_sum_one theorem excludes it. Hence \(A_0(t)\), then \(P_0(t)\), is unreachable. Since \(P_2(t)\) has no source parent for \(t\equiv3\pmod4\), we obtain the new infinite subfamily exclusion

\[
\boxed{t\equiv3\pmod{16}\Longrightarrow\neg CReach(L(t)).}
\]

This removes one sixteenth of all natural t, equivalently one eighth of the odd parameter line of the P7 direct-parent residual.

## 5. Remaining branches and next exact targets

The reduction is not a closure of \(L(t)\). Its surviving cases are now separated:

1. **\(t\equiv1\pmod4\):** only \(P_2(t)\) can survive. Its sum-plus-one factors as
   \[
   P_{2,x}+P_{2,y}+1
   =5(780340743t+209259889).
   \]
   Thus the \(a=1\) high predecessor branch is impossible for every \(t\), since it would make this quantity a power of two times 16. If \(t\equiv5\pmod8\), the odd-\(a\) bounce depth is forced to \(n=0\). Writing \(t=8q+5\), the unique possible parent is
   \[
   (15606814860q+10277409007,\;
     20382315450q+13422174498).
   \]
   Its right coordinate is even and its coordinate sum is
   \(35989130310q+23699583505\equiv6q+1\pmod8\). Thus the standard even-right unique inverse applies unless \(q\equiv1\pmod4\). For \(t\equiv1\pmod8\), even bounce depths \(n\) with \(2^n\mid(P_{2,x}+P_{2,y}+1)/4\) remain possible; this is the unbounded-depth residual.

2. **\(t\equiv3\pmod4\):** only \(P_0(t)\) can survive. For \(t\equiv3\pmod{16}\) it is now excluded. For \(t\equiv11,15\pmod{16}\), the forced low-valuation parent \(Q(v)\) remains; the \(t\equiv15\pmod{16}\) subcase has even right coordinate and sum modulo eight in \(\{2,6\}\), so the even-right unique inverse applies. For \(t\equiv7\pmod{16}\), \(H(t)\) is divisible by 16 and the higher-valuation odd/odd parent fan remains open.

The useful next work is therefore the unbounded even-depth \(P_2\) branch for \(t\equiv1\pmod8\), and the high-valuation / forced-\(Q\) branches of \(P_0\) for \(t\equiv7,11,15\pmod{16}\). Do not treat the eliminated \(t\equiv3\pmod{16}\) cylinder as a full P7 or Machine C exclusion.

## Verification boundary

The calculations above are exact integer algebra, and the reachability transports use existing source-certified theorems. The new composed claims have not yet been compiled in one Lean module. Keep this dossier in im-results/; do not promote it to results/ until an exact Lean 4.36.0-rc2 import-closure compile and axiom audit succeed.
