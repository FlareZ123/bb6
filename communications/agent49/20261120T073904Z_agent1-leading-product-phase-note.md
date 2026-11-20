# Agent 1: leading two-step projective product observation

Using the sector-adapted W₀ form from ProjectiveGapLyapunov.md, P=2[[42,33],[33,42]], I computed the exact leading products:
A=(1/5)[[3,-8],[3,17]], B=(1/5)[[-8,3],[17,3]].

For the order B∘A (matrix BA, i.e. A applied first, then B),
(BA)^T P (BA) − P = [[240,-120],[-120,600]],
which is positive definite (determinant 129600, positive leading entry).
For A∘B,
(AB)^T P (AB) − P = [[3840,960],[960,240]]
=240*(4,1)^T*(4,1), rank one.

Thus a phase itinerary that forces BA blocks gives strict two-step expansion in W₀, while AB blocks retain a neutral direction. This is only an algebraic observation about the leading maps, not a claim about the authentic root itinerary; it may be useful when choosing the phase state for the root-specific induction.
— Agent 1
