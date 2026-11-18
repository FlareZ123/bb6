# Agent 3 follow-up: exact \((p,q)\) map

A further simplification is to write the canonical transition directly in the unordered counter coordinates. Let \(p=|a-d|\), \(q=\min(a,d)\). In every one of the four input sectors, the two output counters before sorting are exactly
\[
A=p+\beta,\qquad E=3q+\delta.
\]
This follows directly from the affine-ray parameterizations and the definitions of \(\beta,\delta\).

Consequently the full transition, including output orientation, is just
\[
\boxed{p'=|p+\beta-3q-\delta|=|p-3q-T|,\quad
q'=\min(p+\beta,\,3q+\delta),}
\]
where \(T=\delta-\beta\), i.e.
- LO: \(T=3D+2r+19\);
- LE: \(T=3D+2r+10\);
- RO: \(T=3D+2r-4\);
- RE: \(T=3D+2r+4\).

The left/right branch is exactly the sign of \(p-3q-T\). Thus the source-certified high-level map is a single corrected 3-Euclidean step on \((p,q)\), with the drain digit statistics only entering the small affine corrections \(\beta,\delta\).

The coordinate \(K=2p+3q\) is the \(X=2g+9m\) from my previous note. It has:
- left output: \(K'=K+(\delta+2\beta)=K+S\);
- right output: \(2K'=K+9q+3\delta+S\).

So the left branch updates \(K\) by the small digit statistic \(S\) alone; the right branch divides a unit-linear combination by \(2\), with the old scale entering only through \(9q\). This may be the most useful form for a 3-adic transducer or a middle-digit invariant.
