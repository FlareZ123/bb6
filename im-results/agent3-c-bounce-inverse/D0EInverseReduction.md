# D0E inverse-chain arithmetic and residual E7 branch

**Status:** exact arithmetic is locally Lean-checked; the source-parent composition below is a paper-level reduction awaiting integration into the original-source proof. This is not a nonhalting proof.

## Setup

The q=0 root32 bridge gives the same parameter
\[
u=1802+6720t.
\]
The surviving direct-parent branch of \(D_0(u)\) is
\[
D0E(u)=(218624u+14700,\;414976u+27902).
\]

Define the direct inverse map
\[
\operatorname{dp}(x,y)=(x+y-2,(y-2)/2).
\]
The Lean file D0EInverseArithmetic.lean proves the exact chain
\[
D0E(u)\to d_1(u)\to d_2(u)\to\cdots\to d_7(u)\to d_8(u),
\]
where each arrow is the arithmetic map \(\operatorname{dp}\). For \(u=1802+6720t\), the seven intermediate states \(d_0,\ldots,d_6\) are even/even, have right coordinate at least six, and have coordinate sum \(2\pmod4\). Thus, using cReach_parent_of_left_gt5 and even_even_parent_fan, every genuine source parent at these seven stages is forced to be the direct parent: the zero-left branch has sum divisible by eight, and an even-a bounce has sum divisible by four.

## The first terminal fork

The state immediately before \(d_8\) is
\[
d_7(t)=(7002858240t+1877919828,\;21786240t+5842300).
\]
Its sum is
\[
d_{7,x}+d_{7,y}=8S,\qquad S=878080560t+235470266,
\]
with \(S\equiv2\pmod4\) and \(S>2\). Therefore even_even_sumzero_parent leaves exactly two source-parent alternatives:

- direct parent
  \[
  d_8(t)=(7024644480t+1883762126,\;10893120t+2921149);
  \]
- depth-one even-a bounce parent
  \[
  E7(t)=(1756161120t+470940530,\;2645134800t+709331944).
  \]

The direct branch \(d_8\) is source-unreachable. Its coordinates are even/odd, its sum is divisible by three, and
\[
d_{8,x}+d_{8,y}+1\equiv4\pmod8.
\]
even_odd_three_divisible_parent forces an odd-a, even-depth parent. Since the sum-plus-one has exact 2-adic valuation two, that depth is zero, and the unique parent is
\[
(3517768800t+943341635,\;1764330960t+473131391).
\]
Both counters are odd, the right counter is at least five, and their sum is \(2\pmod4\). blank_no_odd_sum_two excludes it. Hence
\[
D0E(u)\text{ reachable}\Longrightarrow E7(t)\text{ reachable}.
\]
This is a reduction, not an exclusion of D0E.

## Next inverse of E7

Since \(E7(t)\) is even/even with sum \(2\pmod4\), its only source parent is its direct parent
\[
P(t)=(4401295920t+1180272472,\;1322567400t+354665971).
\]
The target \(P(t)\) is even/odd and has
\[
P_x+P_y+1\equiv4\pmod8.
\]
The complete predecessor grammar therefore forces its odd-a, depth-zero parent
\[
R(t)=(2861931660t+767469219,\;2092249530t+561067594).
\]
Here \(R\) is odd/even and
\[
R_x+R_y\equiv6t+5\pmod8.
\]

For \(t\not\equiv3\pmod4\), this residue is respectively 5, 3, or 1 modulo eight, so blank_reach_iff_even_right applies and forces the direct parent
\[
R'(t)=(4954181190t+1328536811,\;1046124765t+280533796).
\]
The exceptional case is \(t\equiv3\pmod4\), where \(R_x+R_y\equiv7\pmod8\) and the generic even-right uniqueness theorem does not apply.

## Root-index localization of the exception

Write \(r=32+64j\), as required by the root32 class. The exact root equation
\[
18018+211u+22155r=20\cdot2^{E-13}
\]
and \(E\ge21\) imply, modulo 256,
\[
64(17300+22155(t+j))\equiv0\pmod{256}.
\]
Since \(17300\equiv0\) and \(22155\equiv3\pmod4\), this gives
\[
t+j\equiv0\pmod4.
\]
Consequently the exceptional subcase \(t\equiv3\pmod4\) is exactly
\[
j\equiv1\pmod4,
\qquad r\equiv96\pmod{256}.
\]

This is the next concrete target: analyze the complete source-parent fan for \(R(t)\) on the exceptional root-index cylinder \(r\equiv96\pmod{256}\), while continuing the even-right inverse chain for the other three classes. The Lean file certifies the affine arithmetic and modular identities only; it does not import or re-prove the original source grammar.
