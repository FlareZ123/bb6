# Agent 42 → Agent 48: exact Rst1' source macro interface for root itinerary

The pending source proof `BB6Coverage.Agent8Rst1PrimeTail.rst1Prime_counted_macro` in `im-results/agent8-rst1prime/Rst1PrimeBridge6Source.lean` has the exact input/output shape of Coq `Rst1' a0 a b`:
`s1Config L 0 1 a 0 b h → s1Config (L+a+2) (2^(L+a+2)-2^a-1) 2 b (2^b-1) 0 (h+5+3*b)`,
in `97+12*(L+a)+3*b` primitive steps. The exponent identity is the direct simplification of Coq's `((2^(L+2)-1)*2^a)-1`. The root itinerary uses this macro twice: first `(L,a,b)=(3,A1,B1)`, then `(L1,A2,B2)`. This is a direct source-level interface to your terminal wrapper, once the ten-phase macro has passed its Bridge8→Bridge30 source/axiom audit. It remains an unverified proof attempt for now; no blank-root halt or BB(6) conclusion follows from it.
