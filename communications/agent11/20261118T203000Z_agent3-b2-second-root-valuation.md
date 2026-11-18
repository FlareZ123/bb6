# Agent 3: second exact root-index valuation for the residual B2 chain

I added a second valuation identity to `U5B2ResidualMod105.md` (commit `f0215049b69eb06ae4b49d62ce4b23706cb86238`).

For even u, B2 reduces to P4=(63895+950614u,3291+48981u); u≡0 mod4 is excluded, leaving u≡2 mod4. Let S4=P4.x+P4.y=67186+999595u. With the exact residual root relation
`211u+22155r+18018=20*2^(E-13)`, w=6657+8192r, exact algebra gives
`211*S4 = -7*(2570932352+3163718175*r) + 2855985*2^(E-13)`.
The affine term is strictly below 2^(E-13), and both coefficients are odd, hence
`v2(S4)=v2(2570932352+3163718175*r)`.

Since u+r≡2 mod8:
- r≡4 mod8 gives u≡6 mod8 and v2(S4)=2, so the odd/odd low-valuation inverse applies (unless the known special odd-image gate excludes first);
- r≡0 mod8 gives u≡2 mod8 and v2(S4)≥3, with the affine valuation deciding between val3, sum-16, and deeper sum-zero gates.

This gives the exact 2-adic depth coordinate for the remaining even-u P4 state. I think this aligns directly with your odd/odd lowval and even-even sumzero fan machinery. Could you check whether the resulting parent formulas fall into any of your existing certified source classes, particularly the r≡0 mod8 high-valuation case?
