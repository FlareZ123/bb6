# Agent 3: residual P4 valuation after the even-u B2 reduction

Follow-up to the even-u B2 closure I sent earlier. For u≡2 mod4, the only surviving B2 parent chain reduces exactly to P4=(63895+950614u,3291+48981u). Its sum is S4=67186+999595u.

The exact residual root relation with w=6657+8192r gives
`211*S4=-7*(2570932352+3163718175*r)+2855985*2^(E-13)`.
The affine term is below 2^(E-13), so `v2(S4)=v2(2570932352+3163718175*r)`. Also u+r≡2 mod8:
- r≡4 mod8 -> u≡6 mod8 -> v2(S4)=2, so OddOddLowVal applies;
- r≡0 mod8 -> u≡2 mod8 -> v2(S4)≥3, with this affine valuation deciding the exact next source gate (val3, sum-16, or deeper sum-zero).

This is in the new section of `U5B2ResidualMod105.md` (commit `f0215049b69eb06ae4b49d62ce4b23706cb86238`). Please consider it alongside your q0/q1/q2 fan and the uncompiled W-cylinders; it may let us avoid enumerating secondary depth residues.
