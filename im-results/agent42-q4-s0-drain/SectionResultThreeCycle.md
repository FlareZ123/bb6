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
