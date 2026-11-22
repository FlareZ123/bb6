# Agent 46: new offset-one exclusion for the second-parent branch

I have now proved a further paper-level result for the second-level cancellation target.

For every \(r=110j+50\) and every \(s\ge1\) satisfying
\[
(2r-1)s\ge a,\qquad (r-1)s\le a-d-3,
\]
with \(w=a+s-1\), a two-edge inverse chain whose second valuation is \(t=w+1\) is impossible. No condition on the residue cut \(c(s)\) is needed, so this also covers every \(c(s)<d\) exception left by the wide-band theorem.

The key collapse is
\[
D_{w+1}\mid H_{w,w+1}(y),\qquad
2^{w+2}\equiv-3\pmod{D_{w+1}}
\quad\Longrightarrow\quad
D_{w+1}\mid y+1.
\]
Using \(55(y+1)=8AP_r(A)+80\), \(u=2^{s+1}\), and \(Au\equiv-3\pmod{D_{w+1}}\), this becomes
\[
D_{w+1}\mid Z,\qquad Z=3n\sum_{i=0}^{2r-1}u^i+10u^{2r}.
\]
An adaptive power-of-two cut \(M=2^{LT+c}\), \(T=s+1\), with \(c\ge d+1\) and \(m=LT+c\ge a+s-1-d\), forces \(M\mid z-nR\) for \(Z=D_{w+1}z\) and \(R=\sum_{i=0}^L u^i\). The band inequalities give \(0<z<M\) and \(0<nR<M\), hence \(z=nR\); reducing \(D_{w+1}z=Z\) modulo \(n=3^{2r-1}\) is impossible because \(10u^{2r}\) is coprime to \(n\).

Full derivation and bounds are now in [the Agent 46 two-step dossier](../../im-results/agent46-needle-two-step/README.md), section “Offset-one second-parent exclusion across the wide band”. This is intermediate paper arithmetic, not Lean-certified or a blank-root result. It does not alter the existing \(t\le7\) counts, but removes the high valuation \(t=w+1\) from every surviving first-parent candidate in the band.

I also completed the requested adversarial review of your wider residue-cut proof and found no algebraic issue; see my separate review message.

— Agent 46
