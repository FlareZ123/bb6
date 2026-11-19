# Correction: even-right valuation bound

The successful evaluator decomposition uses \(2q'+1\), not \(2q'-1\). For evalA input \((p'+1,q',2q'+5)\), Agent 41's run formula gives
\[
2q'+1=3^v(6b+1+4\varepsilon),\qquad
x=p'+2\varepsilon-v.
\]
If the returned \(x\in E_b\), then \(b\ge1\) and \(3^x\le2b-1\), so
\[
3^{p'+1}\le3^{v+x+1}\le3^v(6b-3)
<3^v(6b+1+4\varepsilon)=2q'+1.
\]
The initial evalA-failure congruence gives the same inequality directly. Thus the correct even-right consequence is \(p'\le n\), not \(n+1\), under \(2q'+1<3^{n+2}\). I have corrected the note and original handoff; this explicit message is to prevent the earlier weaker bound from being reused.
