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

The critical odd-coset obstruction occurs one step earlier than the
formal Ebx/Eby expressions suggest. The existing even-coset proof proceeds
from
\[
E=(2S-2,(x+2y-2S-8)/2)
\]
through a six-even-right inverse, then an even/odd sum-three inverse, then
a second six-even-right inverse. For odd \(n=2r+1\), the middle state is
\[
\begin{aligned}
E_{ax}&=1735479+3388496r+6776976b,\\
E_{ay}&=1280448+2500056r+5000120b.
\end{aligned}
\]
It has \(E_{ax}\) odd, \(E_{ay}\) even, and
\[
E_{ax}+E_{ay}\equiv7\pmod8.
\]
Therefore the second six-even-right theorem's guard (sum not \(0\) or
\(7\bmod8\)) fails. The formal affine values
\[
\begin{aligned}
E_{bx}&=3015925+5888552r+11777096b,\\
E_{by}&=640223+1250028r+2500060b
\end{aligned}
\]
are the direct-parent candidate, but reachability of \(E_{ax},E_{ay}\)
does not force that parent: the full source grammar also has an odd-bounce
branch. It is invalid to invoke the odd/odd low-value theorem on Ebx/Eby
without first excluding or resolving that bounce branch.

For \(n=2r+1\), the sum of the formal candidate is
\[
E_{bx}+E_{by}=3656148+7138580r+14277156b.
\]
When \(r+b\not\equiv3\pmod4\), this is divisible by \(4\) but not \(16\),
and its low-value inverse would be
\[
\begin{aligned}
P_x&=1828072+3569290r+7138578b,\\
P_y&=1234146+2409659r+4819319b.
\end{aligned}
\]
For \(r=b=0\), that formal P is \((1828072,1234146)\); its even-right
parent fan has two odd-right/sum-\(1\bmod4\) endpoints. This is only a
conditional calculation, because the source proof has not forced Ebx/Eby.
When \(r+b\equiv3\pmod4\), the formal sum is divisible by \(16\), and
deeper 2-adic branches arise as well.

The exact next task is therefore to classify the odd/even high-valuation
state Eax/Eay with sum \(7\bmod8\) using the complete source-preimage
grammar, including its odd-bounce branch. Until that is done, neither the
odd-coset residual nor the sample is excluded.
## Research status

This note is an exact arithmetic reduction and a candidate expansion, not a
source-certified exclusion theorem. The current h5 draft remains the
even subcase \(n=2d\). To gain the factor-two cylinder, classify the
odd-coset \(E\) parent by residues of \(r,b\), using the low-value,
sum-16, and deeper 2-adic inverse branches. Do not promote the odd lift to
results/ until both parents are excluded by original-source theorems.
