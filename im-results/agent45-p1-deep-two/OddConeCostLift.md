# Odd-cone cumulative-cost lift

Agent 45, 2026-11-24. This is an algebraic reparameterization of the existing `OddShift` recurrence, not a new reachability theorem.

## One-edge identity

Write the root mass as (S=b_0+d_0), the odd-cone cumulative cost at a hub as (m), and its shifted coordinate as
[
s=d+b/2+3.
]
For an odd inverse edge of depth (t), the next hub has (m'=m+t+1). The existing exact `OddShift` equation is
[
2^{t+1}(s'+m')=2^t(S+7)+s.
]
Set
[
A=(S+7)/2,qquad P=2^m s.
]
Multiplying the edge equation by (2^m), then rearranging, gives
[
oxed{P'=2^{m'}s'=P+2^{m'}(A-m').}
]
This removes the edge depth (t) from the update: it appears only through the strictly increasing new cumulative cost (m').

## Whole-path identity

For any odd-cone path with cumulative costs
[
0=m_0<m_1<\cdots<m_n
]
and shifted coordinates (s_i), repeated application gives
[
oxed{
2^{m_n}s_n
=s_0+\sum_{i=1}^{n}2^{m_i}(A-m_i).
}
]
The next odd edge is possible only if (2^{m_{n+1}}mid 2^{m_n}s_n), i.e.
[
m_{n+1}\le v_2\!\left(
s_0+\sum_{i=1}^{n}2^{m_i}(A-m_i)
\right).
]
Thus the odd-cone is equivalently constrained by a strictly increasing sequence of exponents whose next exponent cannot exceed the 2-adic valuation of the current partial sum. This is a 2-adic lifting / carry formulation of the existing inverse cone.

For a terminal even-right edge, its depth is (t=v_2(s_n)), so its total cost (M=m_n+t+1) satisfies
[
M=v_2(2^{m_n}s_n)+1.
]
If (r=s_n/2^t) is the resulting odd quotient, then
[
r=\frac{2^{m_n}s_n}{2^{M-1}}.
]
The terminal feeder's even-left power-shape equation can therefore be rewritten using the same partial sum (P_n), rather than carrying the terminal quotient as an independent variable.

## Initial constants for the two P1 roots

Let (N=16q) and (U=7\cdot2^N-4q-3).

| Root family | (S) | (A=(S+7)/2) | (s_0) |
|---|---:|---:|---:|
| L0 | (8U+5) | (4U+6=28\cdot2^N-16q-6) | (6U+10=42\cdot2^N-24q-8) |
| L1 | (8U+3) | (4U+5=28\cdot2^N-16q-7) | (5U+7=35\cdot2^N-20q-8) |

## Why this may help

The current unresolved task is to bound total inverse cost or prove the global terminal small-left barrier. In this representation, a path is a sequence (m_i) with
[
P_i=P_{i-1}+2^{m_i}(A-m_i),qquad m_{i+1}\le v_2(P_i).
]
The coefficients (A-m_i) are explicit. A proof that the partial sums cannot acquire sufficiently large 2-adic valuation would give a uniform cost bound; alternatively, the terminal power-shape condition can be combined directly with this partial-sum identity.

This note does **not** establish such a valuation bound, does not exclude any additional (q)-classes, and does not decide P1 or BB(6). It is intended as a reusable exact normalization for further work.
