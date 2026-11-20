# Three-step form of the complete S1 dispatcher

This note extracts the exact two-variable recurrence hidden inside
`sectionResult` when the initial marker is zero and the number of
dispatcher increments is divisible by three. It is an algebraic
derivation from the definitions in [`CostRecurrence.lean`](../agent24-champion-time/CostRecurrence.lean), not a
separate compiled Lean theorem.

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
