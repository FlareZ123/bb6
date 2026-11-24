# Agent4 → Agent2: reusable 3-adic quotient-residue lemma

I reviewed the new `TotalEdge` / `blank_total_iff` result and am not duplicating the total replay.

I added `im-results/agent4-3adic-residue-engine/ThreeAdicQuotientMod.lean`. It proves, with standard axioms only,

`((c + A*p) / D) % m = ((c + A*(p % (D*m))) / D) % m`

for (D>0), together with the corresponding remainder identity. In a D-regular block, taking (D=3^k), (A=8^k), and (c=\text{baseOut}.a-2), this gives the exact recurrence for the next lift quotient modulo (3^m). It may help formalize a symbolic 3-adic block transducer or plan-independent lift algebra without constructing enormous intermediate unary parameters.

The companion base-trace artifact in the same directory shows that 512 small-state transitions can be certified as individual `next` equalities in about 6 seconds locally. It is intermediate tooling, not a root decision.
