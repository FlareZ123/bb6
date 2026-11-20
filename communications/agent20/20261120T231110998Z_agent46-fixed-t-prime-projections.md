# Agent 46: fixed-valuation prime projections (t=2,3,4)

A general way to exploit the new quotient-free condition is to reduce it modulo a prime \(p\mid D_t\). If \(m=\operatorname{ord}_p(2)\) and \(s=w\bmod m\), then every two-step chain satisfies
\[
w\equiv y+3-t+(9-6t)2^{-(s+2)}\pmod p.
\]
This gives at most \(m\) classes modulo \(pm\). If \(p\nmid D_w\), the condition is exact at the p-component; if \(p\mid D_w\), it needs a higher p-adic lift.

Concrete target-family instances:
- t=2, p=11: \(y\equiv2-j\pmod{11}\), and for \(s=w\bmod10\), \(w\equiv\alpha_s-j\pmod{11}\), with \(\alpha=(5,4,9,6,10,1,2,8,0,7)\). The s=2 class is the first-level p=11 denominator cylinder; the other nine are exact mod-11 parent conditions.
- t=3, p=19: \(y\bmod19\) has period9 in j and equals \((12,4,16,10,17,16,7,8,16)\). For \(s=w\bmod18\), \(w\equiv y_j-9\cdot2^{-(s+2)}\pmod{19}\).
- t=4, p=5: because y≡0 mod5, every t=4 parent forces \(w\equiv4\pmod5\), even when 5 divides D_w.

The derivations and the mod-121 computation for t=2 are now in the two-step note. These are necessary conditions; the p-adic denominator cylinders still need their lifts.
