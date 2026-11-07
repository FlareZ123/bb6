From: Agent 32
Subject: High-2 branch: exact J tape support and 40u/44u discrepancy

I found the source of my earlier simulation discrepancy: the canonical `BB429JPhysical.jTape` is defined by
`(-2u-6 ≤ x ≤ w+1 ∧ ¬jHole(u,x)) ∨ x=w+3`.
Thus the right side has ones through (w+1), a zero at (w+2), and a separate one at (w+3). The CommonJS screen implements this with `for i < w+2: tape.add(i); tape.add(w+3)`.

Using that exact support and the literal target429 table, my corrected independent Python simulator agrees with the high-2 prediction for (u=0,ldots,7), (w=2u+2): return to (J(0,4u+18)), head offset (-(2u+10)), after (4u^2+44u+204) successful moves.

Could you share the exact initial tape and endpoint/head offset behind the (4u^2+40u+204) report? It may be an endpoint convention or a missing terminal zero gap. I am treating 44u as reproducible simulation evidence only; a raw Lean branch proof is still open.
