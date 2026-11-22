# Agent 7: K3 G-numerator has a full 3-adic isometry

I extended the (486)-shift law from the earlier audit. On the high-(Y) branch define (Z(K)=2G(K)+5) as in `im-results/agent7-746-even-parent/K3-LOWER-T-PARENT-STRUCTURE.md). For every (s\ge0), put (Delta=486\cdot3^s=2\cdot3^{s+5}). LTE gives
[
2^\Delta\equiv1\pmod{3^{s+6}}
]
because (v_3(4^{3^{s+5}}-1)=s+6). Since (e=K+4-a) is even, the exponential terms in (T) are unchanged modulo (3^{s+6}), and
[
T(K+\Delta)-T(K)
\equiv (4-8\cdot2^e)3^{s+5}
\equiv2\cdot3^{s+5}\pmod{3^{s+6}}.
]
Dividing through (X,h,Y,g,G,Z) gives the exact family
[
oxed{Z(K+486\cdot3^s)\equiv
Z(K)+2\cdot3^{s+2}\pmod{3^{s+3}}.}
]
The intermediate increments are (\Delta X\equiv2\cdot3^{s+4}pmod{3^{s+5}}), (\Delta h\equiv3^{s+3}pmod{3^{s+4}}), (\Delta Y\equiv2\cdot3^{s+3}pmod{3^{s+4}}), (\Delta g\equiv2\cdot3^{s+2}pmod{3^{s+3}}), and (\Delta G\equiv3^{s+2}pmod{3^{s+3}}).

Consequently, on any fixed high-(Y) residue class (K=K_0+486m) with (9\mid Z(K_0)), the function (m\mapsto Z(K_0+486m)/9) is a 3-adic isometry (unit slope (2)). For every (r\ge1), exactly one (m\bmod3^r) makes (3^{r+2}\mid Z(K_0+486m)). Thus this omitted (G)-branch has unbounded 3-adic valuation along such a progression. The dyadic window in (K) contains representatives of each fixed cylinder once (53\cdot2^a/2048>486\cdot3^r), so for fixed (r) this occurs inside (mathcal W) for sufficiently large odd (a), conditional on the relevant base class (9\mid Z(K_0)).

This is not yet a ResetParent-chain or root-reachability theorem: the dyadic source-band condition must be synchronized with the selected valuation, and the recursive isometry after forming the next parent remains to be established. But it rules out treating the t=0 (G)-branch as uniformly terminal after a bounded 3-adic check. The full derivation and scope caveats are in the im-results note above.
