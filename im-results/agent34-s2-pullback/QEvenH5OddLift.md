# Q-even h5: candidate odd-lift cylinder and the remaining inverse branch

## Candidate parameter lift

The current h5 source-draft family is
\[
u=2+8192d,\qquad v=48+8192b.
\]
Its direct-parent proof relies on the second terminal parent having odd right
coordinate and coordinate sum \(2\bmod4\). This is exactly why the current
family takes an even value of the normalized \(4096\)-step lift parameter.

A natural next cylinder is
\[
u=2+4096n,\qquad v=48+8192b.
\]
Set
\[
t=(u+v-2)/4=12+1024n+2048b,\qquad
z=(12+11t-v)/32=3+352n+448b.
\]
The h5 congruence is automatic:
\[
53u+57v\equiv 53\cdot2+57\cdot48=794\pmod{1024}.
\]

This is also compatible with the high-stop parameterization. Let
\[
j=319+512u=1343+2^{21}n,\qquad
m=2779178+2^{21}n+2^{23}w.
\]
Then
\[
j+3m+5+49726=2^{23}(1+n+3w).
\]
Since \(2^{2m+2}(j+3)\) is divisible by \(2^{23}\), the high-stop value
\[
K=2^{2m+2}(j+3)-(j+3m+5)
\]
satisfies \(K\equiv49726\pmod{2^{23}}\). Writing
\(K=49726+2^{23}b\) gives precisely \(v=48+8192b\).
The existing family is the even subcase \(n=2d\); this candidate adds the
odd coset \(n=2r+1\).

## What the existing residual proof does and does not cover

For the generalized \(t,z\), the same first parent calculations give
\[
\begin{aligned}
A&=41704+1714176n+6852608b,\\
B&=30198+1240064n+4962304b,\\
W&=3775+155008n+620288b.
\end{aligned}
\]
In particular \(B+2=8W\) and \(W\equiv3\pmod4\). The second residual pair
and its scale are
\[
\begin{aligned}
x&=86996+3574272n+14296064b,\\
y&=7548+310016n+1240576b,\\
S&=(x+y)/8=11818+485536n+1942080b.
\end{aligned}
\]
The useful terminal congruences persist for every \(n,b\):
\[
x\equiv20\pmod{64},\quad
y\equiv60\pmod{64},\quad
S\equiv10\pmod{32}.
\]
The direct parent used in the existing q-even h5 residual theorem therefore
retains the same odd-right/sum-\(2\bmod4\) exclusion.

The other terminal parent has coordinates
\[
\begin{aligned}
E_x&=71649+2944276n+11777096b,\\
E_y&=15209+625014n+2500060b.
\end{aligned}
\]
For even \(n\), \(E_x+E_y\equiv2\pmod4\), which is the existing
odd-right/sum-\(2\bmod4\) endpoint. For odd \(n\),
\[
E_x+E_y\equiv0\pmod4,
\]
so the existing residual theorem cannot be reused unchanged. This is a real
parity obstruction, not a missing arithmetic tactic.

## A first odd-coset sample

Write \(n=2r+1\). If \(r+b\not\equiv3\pmod4\), then
\(E_x+E_y\) is divisible by \(4\) but not \(16\), and the low-value
odd/odd inverse theorem supplies the parent
\[
\begin{aligned}
P_x&=1828072+3569290r+7138578b,\\
P_y&=1234146+2409659r+4819319b.
\end{aligned}
\]
For the sample \(r=b=0\), this is
\((1828072,1234146)\), an even/even pair with sum \(2\bmod8\).
Its unique even-right parent is \((3062216,617072)\), whose sum is
\(8\cdot459911\) with \(459911\equiv3\bmod4\). The two parents from
the even/even sum-zero inverse theorem are
\[
(3679286,308535),\qquad(919820,1688265).
\]
Both have odd right coordinate and sum \(1\bmod4\), hence are excluded by
the existing odd-right/sum-\(1\bmod4\) theorem. This closes that sample,
but not the whole odd coset.

When \(r+b\equiv3\pmod4\), the odd/odd sum is divisible by \(16\).
The sum-16 inverse theorem handles only the \(16\bmod32\) slice; the deeper
\(0\bmod32\) slices still need a source inverse analysis. Even in the
\(16\bmod32\) slice, the second parent is an even/odd high-valuation state
and needs a further image classification.

## Research status

This note is an exact arithmetic reduction and a candidate expansion, not a
source-certified exclusion theorem. The current h5 draft remains the
even subcase \(n=2d\). To gain the factor-two cylinder, classify the
odd-coset \(E\) parent by residues of \(r,b\), using the low-value,
sum-16, and deeper 2-adic inverse branches. Do not promote the odd lift to
results/ until both parents are excluded by original-source theorems.
