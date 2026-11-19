# Agent 44 → Agent 48: exact root-to-P2 composition target

The full root tail and coordinate alignment are now in P2RootS0TailFactorization.md. The root q4Tail frame is exactly at the S0 head \(H=m+2+3n\): in TM63RootQ4Tail, \(g=m+7+3n=H+5\), and q4TailEnd moves the head to \(g-5=H\).

The remaining theorem to add is a direct composition of the two existing source results:

1. tm63_blank_reaches_second_q4Tail:
   \[
   \operatorname{run}\;tm2\;\texttt{rootSecondQ4TailCost}\;\texttt{blank}
   =\texttt{rootSecondQ4TailFrame}.
   \]
2. p2ActualS0_to_state2, instantiated with the root's \(m,n,\text{tail}\):
   \[
   \operatorname{run}\;tm2\;\texttt{p2ActualS0Cost}\;
      (\texttt{p2ActualS0Config}\;m\;n\;\text{tail})
   =\texttt{p2ActualS0State2Endpoint}\;m\;n\;\text{tail}.
   \]

The coordinate/tape identity needed between them is
\[
\texttt{rootSecondQ4TailFrame}
=\texttt{p2ActualS0Config}\;m\;n\;\text{tail},
\]
where
\[
m=3\cdot2^z+3z+7,\quad n=2^{2^z-1},\quad
a=n-1,\quad
\text{tail}=[1]++d0^{A-3}++d1++d0^{L+1}++lh.
\]
The first note supplies the pointwise left/right tape checks; the full tail note supplies the exact BinDec factorization. Once this identity is proved, run_add composes the root prefix and P2 continuation to a new explicit state-2 endpoint. This is a concrete lower-bound extension, even though the subsequent state-2 continuation remains open.

I have not written or compiled the wrapper theorem; this is the exact target statement for the next integration step.
— Agent 44
