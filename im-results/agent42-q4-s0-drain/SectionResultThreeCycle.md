# Three-step form of the complete S1 dispatcher

This note extracts the exact two-variable recurrence hidden inside
`sectionResult` when the initial marker is zero and the number of
dispatcher increments is divisible by three. Its core cost and
popcount identities are now machine-checked in
[`SectionResultThreeCycleModel.lean`](SectionResultThreeCycleModel.lean),
a self-contained Lean 4.36.0-rc2 model copying the recurrence definitions
from [`CostRecurrence.lean`](../agent24-champion-time/CostRecurrence.lean).
It does not import or compile the original source dependency closure.

## Machine-checked model and scope

The isolated Lean model proves the following exact statements:

1. \(\sum_{r=1}^{N}v_2(r)=N-s_2(N)\), by a binary-increment
   identity for the copied \(v_2\) and popcount recurrences.
2. For \(N=3k\) and initial marker zero,
   \[
   C(N)=31N-12s_2(N)+
   \sum_{i=0}^{N-1}
   (6\cdot4^{b_i}+42\cdot2^{b_i}+12a_i-9b_i).
   \]
3. For \(A\ge2\),
   \[
   s_2(2^A(2^{L+2}-1)-3)=A+L.
   \]
4. If \(L\) is even, the same terminal index is divisible by three,
   so the cost identity specializes directly to this q4 family.
5. 'sectionResult_one_dimensional_cost': after adding the terminal
   \(12E\), \(12(s_2(N)+2)\), and fixed 66 correction, the cost becomes
   \[
   90k^2+111k+90+12(3k+1)U+\operatorname{oneDimSum}(3k,R),
   \]
   eliminating the intermediate exponent sequence and marker dependence.

The model copies the definitions of 'v2', 'proposedIncrementCost',
'nextMarker', 'nextExponent', 'nextRight', and 'sectionResult'
from 'CostRecurrence.lean' into a fresh namespace. It compiles with
warnings treated as errors; the principal theorem axiom profiles are
'[propext, Quot.sound]'.

The one-dimensional dispatcher-plus-terminal elimination above is
formalized in the isolated model, but this does **not** certify the
original 'CostRecurrence.lean' module or its transitive imports. The
three-step map \(F\), dominant-increment asymptotic, root-prefix cost,
and counted-drain composition remain outside this Lean proof. Most
importantly, it does not prove that the proposed dispatcher cost is the
authentic TM2 primitive run length. The authentic blank-root composition
remains uncompiled and no BB(6) halt/score claim follows.

## One-step state and cost

Write the dispatcher state before an increment as ((m,a,b)). The
definitions in `CostRecurrence.lean` update it by

[
m'=(m+2)mod 3,qquad
a'=a+b+egin{cases}1&m=0,\2&m
e0,end{cases}
qquad b'=2^b-1.
]

The one-step cost at remaining counter (r) is

[
c(m,r,a,b)=6cdot4^b+42cdot2^b+15+4m+
12(a+v_2(r))-9b.
]

The existing shift identity for `proposedIncrementCost` gives

[
c(m,r,a,b)=12v_2(r)+c(m,1,a,b).
]

Thus the complete dispatcher cost is the sum of the (N) one-step costs,
with (r) running through (N,N-1,ldots,1).

## Three-step state macro

Starting from marker zero, the marker sequence is (0,2,1,0). Composing
the three state updates gives the two-variable map

[
F(a,b)=
left(
a+b+2^b+2^{2^b-1}+3,;
2^{,2^{,2^b-1}-1}-1
ight).
]

Consequently, if (N=3k), then the endpoint of
`sectionResult N 0 a b` has marker zero and its exponent/right fields
are exactly the two components of (F^k(a,b)). This follows by grouping
the (N) one-step updates into (k) consecutive triples; no asymptotic
approximation is involved.

The map raises the right counter by three nested powers of two per
three-increment cycle. This is the structural reason the complete
dispatcher can absorb the very large q4Tail index without iterating the
separate P2 q4Tail-to-q4Tail recurrence.

## Exact cost simplification when (3mid N)

Let ((m_i,a_i,b_i)) be the state before increment (i), for
(0le i<N), starting from ((0,a_0,b_0)). The marker sequence repeats
(0,2,1), so

[
sum_{i=0}^{N-1}m_i = N
qquad	ext{when }3mid N.
]

Also, Legendre's binary valuation identity gives

[
sum_{r=1}^{N}v_2(r)=N-s_2(N),
]

where (s_2(N)) is the binary digit sum (popcount). Summing the
one-step costs and collecting the constant and marker terms yields

[
oxed{
(operatorname{sectionResult}(N,0,a_0,b_0)).operatorname{cost}
=
31N-12s_2(N)
+
sum_{i=0}^{N-1}
left(6cdot4^{b_i}+42cdot2^{b_i}+12a_i-9b_iight)
}
]

for (3mid N). The identity is exact; the remaining sum follows the
state recurrence above. The (-9b_i) term is in the original natural
number expression, whose nonnegativity is already discharged by the
existing `proposedIncrementCost` lemmas.

## Specialization to the authentic q4Tail terminal route

For the general q4Tail adapter in [`GeneralQ4TailTerminalComposition.lean`](../agent44-tm63-middle/GeneralQ4TailTerminalComposition.lean), set

[
W=A+L+2,quad
N=2^A(2^{L+2}-1)-3,quad
U=q4TerminalUnary(z),quad R=q4TerminalRight(z).
]

If (L) is even, (3mid N). With (k=N/3), the dispatcher endpoint is
therefore

[
E=pi_1(F^k(U,R)),qquad
B=pi_2(F^k(U,R)),
]

with marker zero. Here (E) is the terminal exponent used by
`terminalMoves W E`. The exact champion score expression from the root
composition can be written

[
S=C_{m root}+drainCost(R,0)+
C_{m dispatch}(N,U,R)+59+12(W+E)+7,
]

where (C_{m dispatch}) is the boxed sum above and
(C_{m root}=rootToSecondQ4Cost+rootSecondQ4TailPrefixCost).

This form exposes the complete dispatcher as a three-step recurrence
plus an explicit valuation correction. It does not by itself prove the
authentic root prefix, compile the Lean dependency closure, or establish
a universal BB(6) upper bound.


## Exact popcount of the authentic terminal index

The valuation correction in the dispatcher cost can be made explicit for
this entire q4Tail family. For \(A\ge2\), write
\[
N=2^A(2^{L+2}-1)-3
  =(2^{L+2}-2)2^A+(2^A-3).
\]
The lower block satisfies
\[
2^A-3=1+\sum_{j=2}^{A-1}2^j,
\]
so it has exactly \(A-1\) one-bits (the sum is empty when \(A=2\)).
The upper block satisfies
\[
2^{L+2}-2=\sum_{j=1}^{L+1}2^j,
\]
so its shift by \(A\) has exactly \(L+1\) one-bits, all above the lower
\(A\)-bit block. There is no carry or overlap. Therefore
\[
\boxed{s_2(N)=A+L.}
\]
For the authentic root \(L=76\), this is \(s_2(N)=A+76\), independently
of the enormous value of \(A=\texttt{rootMarker1A}\).

Consequently, with \(a_0=U\), \(b_0=R\), and
\[
m_{i+1}=(m_i+2)\bmod3,\qquad
a_{i+1}=a_i+b_i+\begin{cases}1&m_i=0,\\2&m_i\ne0,\end{cases}
\qquad b_{i+1}=2^{b_i}-1,
\]
the complete dispatcher cost is exactly
\[
C_{\rm dispatch}
=31N-12(A+L)
 +\sum_{i=0}^{N-1}
   (6\cdot4^{b_i}+42\cdot2^{b_i}+12a_i-9b_i).
\]
Here \(m_0=0\), \(U=K+n-1\), \(R=2^{n-1}-1\), and \(E=a_N\).

Using the closed all-ones drain cost and
\(\operatorname{terminalMoves}(W,E)=59+12(W+E)\), the conditional
Attainable score from the authentic root simplifies further to
\[
S=C_{\rm root}
 +6\cdot4^{n-1}+42\cdot2^{n-1}
 +31N
 +\sum_{i=0}^{N-1}
   (6\cdot4^{b_i}+42\cdot2^{b_i}+12a_i-9b_i)
 +12E-12n+54,
\]
where \(W=A+L+2\) and
\(C_{\rm root}=\texttt{rootToSecondQ4Cost}
 +\texttt{rootSecondQ4TailPrefixCost}\).
The constant \(54\) includes the \(+7\) champion-attainability
correction. This is an exact algebraic simplification of the source
score expression; it does not upgrade the uncompiled root/dispatcher
composition to an accepted theorem.


## One-dimensional exact score form

The exponent and marker can also be eliminated from the cost sum.  This
leaves only the independent right-counter recurrence, which is the
quantity responsible for the tower growth.

Put \(N=3k\), \(b_0=R\), and
\[
b_{j+1}=2^{b_j}-1.
\]
The marker sequence is \(m_j=0,2,1,0,2,1,\ldots\).  Let
\(\epsilon_j=1\) when \(j\equiv0\pmod3\), and
\(\epsilon_j=2\) otherwise.  Then
\[
a_i=U+\sum_{j=0}^{i-1}(b_j+\epsilon_j).
\]
In particular, the terminal exponent is
\[
E=a_N=U+\sum_{j=0}^{N-1}b_j+5k.
\]

Summing the intermediate exponents gives
\[
\sum_{i=0}^{N-1}a_i
=NU+\sum_{j=0}^{N-2}(N-1-j)b_j
 +\frac{15k^2-7k}{2}.
\]
For the last term, group the weighted marker increments in blocks of
three. In block \(r=0,\ldots,k-1\), writing \(t=k-r\), the contribution
is
\[
(3t-1)+2(3t-2)+2(3t-3)=15t-11.
\]
Summing \(t=1,\ldots,k\) gives \((15k^2-7k)/2\).

Substituting these two identities into the preceding exact score formula
and collecting the coefficients of each \(b_j\) yields the single-sum
expression
\[
\boxed{
\begin{aligned}
S={}&C_{\rm root}
 +6\cdot4^{n-1}+42\cdot2^{n-1}
 -12n+54\\
&+90k^2+111k+12(3k+1)U\\
&+\sum_{j=0}^{3k-1}
 \left(6\cdot4^{b_j}+42\cdot2^{b_j}
       +(12(3k-j)-9)b_j\right),
\end{aligned}}
\]
where
\[
b_0=R=2^{n-1}-1,\qquad b_{j+1}=2^{b_j}-1,\qquad
U=K+n-1,\qquad K=2^z+z+3.
\]
All coefficients are explicit; no marker or exponent recurrence remains
inside the sum. The formula is an algebraic consequence of the exact
dispatcher-cost recurrence and the root score expression. Its use as an
attained champion score remains conditional on acceptance of the
uncompiled authentic-root and source-dispatcher composition.


## Direct correspondence with the BusyCoq \(t_2,s t_2\) notation

The right-counter sequence is exactly the published recursion, not merely
an asymptotically similar one. With
\[
t_2(0,R)=R,\qquad t_2(j+1,R)=2^{t_2(j,R)}-1,
\]
we have \(b_j=t_2(j,R)\). If
\[
s t_2(q,R)=\sum_{j=0}^{q}t_2(j,R)
\]
(the inclusive convention used in the BusyCoq analysis), then the terminal
exponent simplifies to
\[
E=U+s t_2(N-1,R)+5k.
\]
Thus the single-sum expression is an exact primitive-step cost refinement
of the same \(t_2,s t_2\) recursion used in the published TM63 analysis.
It does not introduce a new machine recurrence, and it does not by itself
establish that the source-level root composition is accepted.


## Dominance of the final counted increment

For \(N=3k\), isolate the dispatcher-plus-terminal part of the score:
\[
D_N(U,R)=90k^2+111k+12(N+1)U+
\sum_{j=0}^{N-1}\left(
6\cdot4^{b_j}+42\cdot2^{b_j}
+(12(N-j)-9)b_j
\right).
\]
Assume \(R\ge5\), \(U\ge0\), and \(b_0=R,\ b_{j+1}=2^{b_j}-1\).

Since \(b_0=R\ge5\), every \(b_i\ge5\), and
\[
6\cdot4^{b_j}+42\cdot2^{b_j}
=6b_{j+1}^2+54b_{j+1}+48.
\]
For \(x\ge5\), \(2^x-1\ge x^2\), so \(b_i^2\le b_{i+1}\); the sequence
is increasing. For \(N\ge2\), this gives the sharper estimates
\[
\sum_{i=1}^{N}b_i^2
\le b_N^2+b_N+(N-2)b_{N-1},
\qquad
\sum_{i=1}^{N}b_i
\le b_N+(N-1)b_{N-1}.
\]
All coefficients \(12(N-j)-9\) are positive, and
\[
\sum_{j=0}^{N-1}(12(N-j)-9)=6N^2-3N.
\]
As \(b_j\le b_{N-1}\) for \(j<N\), the remaining weighted term obeys
\[
\sum_{j=0}^{N-1}(12(N-j)-9)b_j
\le(6N^2-3N)b_{N-1}.
\]
Combining these three bounds yields the sharpened two-sided estimate
\[
\boxed{
6(b_N+1)^2\le D_N(U,R)\le
6b_N^2+60b_N+(6N^2+57N-66)b_{N-1}
+48N+90k^2+111k+12(N+1)U.
}
\]
The lower bound is exactly the final increment's
\(6\cdot4^{b_{N-1}}=6(b_N+1)^2\) contribution; every other term in
\(D_N\) is nonnegative. The upper-bound coefficients follow by collecting
\(6(N-2)b_{N-1}\) from the square sum,
\(54(N-1)b_{N-1}\) from the linear sum, and
\((6N^2-3N)b_{N-1}\) from the weighted sum.

Because \(b_N=2^{b_{N-1}}-1\), we have
\(b_{N-1}=\log_2(b_N+1)\). Also \(b_N\ge2^N R\) for \(R\ge5\).
For fixed \(U,R\), the remainder above is therefore
\(O(Nb_N+N^2\log b_N+N^2+NU)=o(b_N^2)\), and
\[
D_N(U,R)\sim6b_N^2=6\,t_2(N,R)^2
\qquad(N\to\infty).
\]
This is a sharper paper derivation than the earlier \(O(N^2b_N)\)
remainder. It has not yet been added to the isolated Lean model, so it
must not be described as Lean-checked.

## Root-prefix domination and full-score asymptotic

The preceding estimate can be extended from the dispatcher-plus-terminal
part to the complete conditional score. The argument below is a paper
derivation from the source cost recurrences; it is not yet Lean-formalized.

First bound a general SectionResult segment. Let
\[
a_{i+1}=a_i+b_i+\epsilon_i,\qquad
b_{i+1}=2^{b_i}-1,\qquad \epsilon_i\in\{1,2\},
\]
with \(a_0\le b_0\) and \(b_0\ge5\), and let \(B=b_M\) after \(M\ge1\)
increments. Since \(2^b-1\ge2b\) and \(2b+2\le2^b-1\) for \(b\ge5\),
induction gives
\[
b_{i+1}\ge2b_i,\qquad a_i\le b_i.
\]
In particular \(M\le B\), \(\sum_{i=0}^{M-1}a_i\le MB\le B^2\), and
\[
\sum_{r=1}^{M}v_2(r)=M-s_2(M)\le M\le B.
\]
For \(i\le M-2\), \(b_i\le b_{M-1}/2\), while
\(B+1=2^{b_{M-1}}\). Thus
\[
\sum_{i=0}^{M-1}4^{b_i}
\le (B+1)^2+(M-1)(B+1)
\le2(B+1)^2,
\qquad
\sum_{i=0}^{M-1}2^{b_i}\le2(B+1)^2.
\]
Using \(m_i\le2\) in the exact one-step cost and dropping its nonpositive
\(-9b_i\) term gives
\[
\begin{aligned}
\sum_{i=0}^{M-1}c_i
&\le6\sum_i4^{b_i}+42\sum_i2^{b_i}
 +12\sum_i a_i+12\sum_{r=1}^{M}v_2(r)+23M\\
&\le143(B+1)^2.
\end{aligned}
\]
The terminal offset \(12a_M+8+63+3B\) is at most
\(15B+71\le86(B+1)^2\).

Apply this to the long middle-34 SectionResult segment, whose initial
state satisfies \(a_0\le b_0\), \(b_0\ge5\), and whose final right counter
is \(B=\texttt{middle34Result.right}\). The preceding root-to-middle-34
prefix has a fixed finite number of source increments and drains, so its
cost is \(O((B_0+1)^2)\), where
\(B_0=\texttt{tm63MiddleAfter34B}\le B\). The preceding bound and the
outer-LC postlude estimate therefore give
\[
\texttt{rootToMarker1S0Cost}=O((B+1)^2).
\]
The authentic parameters then satisfy
\[
z=2^B-1,\qquad m=2^z-1,\qquad n=2^m,\qquad
A=\texttt{middle34Result.exponent}+B+2\le2B+2,
\]
so \(B\le z\le m\). The exact formula for
\(\texttt{rootSecondQ4Cost}\) consists of closed drain terms of orders
\(4^B,4^z,4^m\), together with terms linear in
\(A,z,m,2^B,2^z\); hence it is \(O(4^m)\). Let \(p=3\cdot2^z+3z+7\) be the q4Tail prefix parameter (distinct from \(m=2^z-1\)). The exact final q4-tail prefix cost is
\[
3n+p+65=3n+3\cdot2^z+3z+72=O(n)=O(4^m),
\]
because \(2^z=m+1\), \(z\le m\), and \(n=2^m\). Since
\(\texttt{rootToMarker1S0Cost}=O(B^2)=O(4^m)\), the complete root prefix
obeys
\[
C_{\rm root}
=\texttt{rootToSecondQ4Cost}
 +\texttt{rootSecondQ4TailPrefixCost}
=O(4^m)=O(n^2).
\]

The initial dispatcher parameters are
\[
U=K+n-1=n+m+z+3,\qquad
R=2^{n-1}-1,\qquad K=2^z+z+3.
\]
For \(z\ge3\), \(m\ge7\), \(n=2^m\), so \(U\le R\). Also
\(R^2\asymp4^{n-1}\), and \(4^m=o(R^2)\) because \(n=2^m\).
Consequently \(C_{\rm root}=o(R^2)\).

For the dispatcher term, the earlier upper bound and
\(b_N\ge2^N R\), \(b_{N-1}\le b_N\), show uniformly when \(U\le R\) that
\[
D_N(U,R)=6b_N^2(1+o(1))
\qquad(N\to\infty).
\]
Indeed, after division by \(b_N^2\), the remaining terms are bounded by
\(O(N^2/b_N+N^2/b_N^2+N R/b_N^2)\), which tends to zero. The separate
root-drain term in the exact score is
\[
D_{\rm rootDrain}
=6\cdot4^{n-1}+42\cdot2^{n-1}-12n+54
=O(R^2),
\]
and hence is also \(o(b_N^2)\), since \(b_N\ge2^N R\).
Combining the three contributions gives the full conditional-score
asymptotic
\[
\boxed{S_{\rm full}
=C_{\rm root}+D_{\rm rootDrain}+D_N
\sim6b_N^2=6\,t_2(N,R)^2.}
\]

This closes the root-prefix asymptotic gap for the q4 parameter family at
the level of a paper derivation. It does **not** compile or certify the
authentic root/dispatcher composition, and it is not an accepted BB(6)
halt or score theorem.


## Relation to existing Lean popcount/valuation lemmas

A short formal proof of the new \(M-3\) popcount identity can reuse
\`im-results/agent48-counted-inc0/Marker1TerminalArithmetic.lean\`.
Put \(q=2^{A-2}(2^{L+2}-1)\), so \(M=4q\). Then
\[
M-1=4(q-1)+3,\qquad M-3=4(q-1)+1.
\]
The existing \`popCount_odd\` and \`popCount_even\` lemmas give
\[
\operatorname{popCount}(4r+3)=\operatorname{popCount}(r)+2,\qquad
\operatorname{popCount}(4r+1)=\operatorname{popCount}(r)+1.
\]
Combining these with \`popCount_M_sub_one\` yields
\(\operatorname{popCount}(M-3)=A+L\). The same module's
\`sumV2_add_popCount\` then gives
\(\sum_{r=1}^{N}v_2(r)=N-A-L\), after identifying its recursive \(v_2\)
with the dispatcher \`CostRecurrence.v2\) (the explicit zero case in the
latter is redundant). This is a reuse route for a future compiled lemma;
no new Lean theorem is claimed here.


## Stronger tetration-height corollary (conditional)

A strong root-countdown estimate follows directly from the seven-step
first section \(\texttt{sectionResult}\ 7\ 2\ 6\ 63\). Let
\(T_1=2\), \(T_{j+1}=2^{T_j}\). Its right counters start at \(b_0=63\),
so \(b_0\ge T_3+1\); since \(b_{j+1}=2^{b_j}-1\), induction gives
\(b_j\ge T_{j+3}+1\) for \(0\le j\le6\). The exponent update is
\(a_{j+1}=a_j+b_j+\epsilon_j\) with \(\epsilon_j\ge1\), whence
\[
A_0=a_7
=6+\sum_{j=0}^{6}(b_j+\epsilon_j)
\ge20+\sum_{j=3}^{9}T_j.
\]
Set \(S_9=\sum_{j=3}^{9}T_j\). The root residue arithmetic gives
\[
r=31\cdot2^{A_0-4}-1,\qquad M=16r-20,
\]
and therefore
\[
M\ge M_0:=496\cdot2^{S_9+16}-36.
\]
The middle-34 SectionResult segment starts with right counter at least \(2\)
and performs \(M\) updates \(b_{j+1}=2^{b_j}-1\), so its final right
counter \(B\) satisfies
\[
B\ge T_M+1\ge T_{M_0}+1.
\]
The terminal exponent is
\(A=\texttt{middle34Result.exponent}+B+2\), so
\(A\ge T_{M_0}+3\).

For the authentic \(L=76\) terminal index,
\[
N=2^A(2^{78}-1)-3
\ge N_0:=(2^{78}-1)2^{T_{M_0}+3}-3
=8(2^{78}-1)T_{M_0+1}-3.
\]
The final dispatcher right counter starts at \(R\ge5\) and follows the
same recurrence, so \(b_N\ge T_N+1\ge T_{N_0}+1\). The exact dispatcher
score contains \(6b_N^2\), and all remaining dispatcher, root-drain, and
root-prefix terms are nonnegative. Thus the complete conditional score
obeys
\[
\boxed{S_{\rm full}\ge6\bigl(T_{N_0}+1\bigr)^2.}
\]
This supersedes the weaker \(M_0=62T_{10}-36\) bound and the earlier
\(2\uparrow\uparrow\uparrow5\) comparison.

This remains an arithmetic lower bound conditional on the authentic root
and complete dispatcher source composition. It is not a compiled Lean
result, and it does not establish an unconditional BB(6) lower bound
until that source composition is accepted.