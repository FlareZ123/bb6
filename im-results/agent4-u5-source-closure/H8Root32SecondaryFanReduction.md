# Root-32 reduction of the H8 secondary fan

**Status:** intermediate source-level reduction; not yet a Lean theorem and not a BB(6) classification.

## Setup

Use the H8 branch from \`U5Q0H8Residue.lean\` and the exact root-32 parameter bridge in \`U5B2Root32ParameterBridge.lean\). Write
$$
h=8+128u,\qquad u=1802+6720t,\qquad t\ge0.
$$
The secondary fan in \`U5Q0SecondaryFan.lean\` reduces reachability of \(P_0(h)\) to the direct parent \(E_h\) or one of four even/even bounce parents \(B_{1,h},\ldots,B_{4,h}\).

Substitution gives
$$
\begin{aligned}
E_h&=(14700+218624u,\;27902+414976u),\\
B_{1,h}&=(2942+43776u,\;33780+502400u),\\
B_{2,h}&=(734+10944u,\;34881+518816u),\\
B_{3,h}&=(182+2736u,\;35154+522920u),\\
B_{4,h}&=(44+684u,\;35220+523946u).
\end{aligned}
$$

## Cases that reduce

### \(E_h\)

Apply the unique even-right predecessor map
$$
F(x,y)=(x+y-2,(y-2)/2)
$$
eight times. The eighth predecessor is
$$
E_8=(70258+1045334u,\;107+1621u).
$$
Since \(u\equiv2\pmod8\), this has even/odd parity and \(x+y\equiv3\pmod8\). The exact \`section_evenodd_sum3_inverse\` parent is
$$
P=\left(\frac{70360+1046955u}{2},\;\frac{70570+1050197u}{4}\right).
$$
Using \(u=1802+6720t\), this is the integral affine family
$$
P=(943341635+3517768800t,\;473131391+1764330960t).
$$
Both coordinates are odd and their sum is \(1416473026+5282099760t\equiv2\pmod4\). The existing odd/odd sum-two exclusion therefore rules out \(P\), hence \(E_h\).

### \(B_{1,h}\)

Its sum is \(36722+546176u\equiv2\pmod8\). The forced even-right predecessor is
$$
(36720+546176u,\;16889+251200u).
$$
Its right coordinate is odd and its sum is \(1\pmod4\). The odd-right sum-one exclusion rules out \(B_{1,h}\).

### \(B_{2,h}\)

This is exactly the affine \(B_2(u)\) family treated in \`U5B2Root32.lean\`. The root-32 bridge supplies \(u=1802+6720t\), so the intended exclusion is \`blank_no_b2_root32_from_exact_root_index\`.

**Proof-status caveat:** the current repository note says the full \`U5B2Root32.lean\` import closure has not yet been compiled. Treat this case as conditional on that draft theorem until its source proof is compiled and checked.

### \(B_{3,h}\)

We have
$$
B_{3,h,1}+B_{3,h,2}=8S_3,\qquad S_3=4417+65707u.
$$
Since \(u\equiv2\pmod4\), \(S_3\equiv1+3\cdot2\equiv3\pmod4\). The existing even/even sum-zero exclusion \`blank_no_sumzero_target\` applies.

## The remaining \(B_{4,h}\) case

Write \(u=1802+6720t\). Then
$$
B_{4,h}=(1232612+4596480t,\;944185912+3520917120t)
$$
and
$$
S_4=\frac{B_{4,h,1}+B_{4,h,2}}8
=118175964+440684160t
=4(29543991+110171040t).
$$
The last factor is odd and greater than one, so \(v_2(S_4)=2\) and \(S_4\) is not a power of two.

Apply the complete even/even parent fan:

* **Direct parent:**
  $$
  (945418522+3525513600t,\;472092955+1760458560t).
  $$
  Its right coordinate is odd and its sum is \(1\pmod4\), so it is excluded.
* **Zero-left parent:** this would require \(S_4=2^m\), impossible because \(S_4/4\) is odd and greater than one.
* **Bounce parents:** the bounce depth \(n\) is odd and \(n+2\le v_2(B_{4,h,1}+B_{4,h,2})=5\), hence \(n=1\) or \(n=3\).

For \(n=3\), the parent is
$$
(59087980+220342080t,\;915258220+3413044320t),
$$
whose sum is
$$
8(121793275+454173300t),
$$
with quotient \(3\pmod4\). It is excluded by \`blank_no_sumzero_target\`.

For \(n=1\), the parent is the sole surviving family
$$
P_1(t)=(236351926+881368320t,\;826626250+3082531200t),
$$
with
$$
P_{1,1}+P_{1,2}=8S_1,\qquad
S_1=132872272+495487440t
=16O(t),
$$
where
$$
O(t)=8304517+30967965t.
$$

## Further reduction of \(P_1(t)\)

The direct parent of \(P_1(t)\) is
$$
D_1=(1062978174+3963899520t,\;413313124+1541265600t).
$$
Its sum is \(2\pmod8\), so its even-right predecessor is forced:
$$
D_2=(1476291296+5505165120t,\;206656561+770632800t).
$$
The right coordinate of \(D_2\) is odd and its sum is \(1\pmod4\). Thus the direct-parent branch of \(P_1(t)\) is excluded.

The zero-left branch would require \(S_1=2^m\), hence \(O(t)=2^{m-4}\). But
$$
O(t)\equiv1\pmod3,\qquad O(t)\equiv2\pmod5.
$$
A power \(2^e\equiv1\pmod3\) requires \(e\) even, while \(2^e\equiv2\pmod5\) requires \(e\equiv1\pmod4\), a contradiction. So the zero-left branch is also excluded.

The only remaining source parents of \(P_1(t)\) are even-\(a\) bounce parents at odd depths
$$
n\le 5+v_2(O(t)).
$$
There is no uniform finite depth cutoff. The coefficient \(30967965\) is odd, so \(O(t)\equiv0\pmod{2^d}\) has one solution class \(t\pmod{2^d}\) for every \(d\).

This unboundedness is not an artifact of allowing arbitrary \(t\). On the root-32 cylinder the exact saturation formula is
$$
r=32+64j,\quad
K=903171544+1761607680j,\quad
N=\frac{5\cdot2^K-17300}{22155},\quad
t=N-j.
$$
For any fixed \(d\le K\), \(2^K\equiv0\pmod{2^d}\), so
$$
N\equiv-17300\cdot22155^{-1}\pmod{2^d},
$$
independently of \(j\). As \(j\) ranges over the naturals, \(t=N-j\) therefore runs through every residue class modulo \(2^d\). In particular, actual root-32 instances realize arbitrarily large \(v_2(O(t))\).

## Research consequence

The H8 fan is reduced to one explicit affine target family \(P_1(t)\). Its direct and zero-left parents are excluded, but its even-\(a\) bounce fan has genuinely unbounded depth along the exact root-32 family. A finite list of bounce-depth checks cannot close H8. The next useful task is a uniform normal form or invariant for the \(P_1(t)\) bounce parents, not another fixed-depth case split.

This note is an algebraic reduction using existing source-parent lemmas. It does not claim that the remaining \(P_1(t)\) family is unreachable, and it does not establish the BB(6) upper bound.
