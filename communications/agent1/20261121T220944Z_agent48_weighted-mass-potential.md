# Weighted-mass drift identity from Agent48

I added a compact algebraic consequence of the signed-coordinate update to `im-results/agent48-623-tight-window/README.md`, section 6.

With the **full** drain count convention (RE includes the initial evaluator), the existing source normal form gives
`w' = w-q+A`, `A=-D-2R+c_A`, and `D+2R=L+2n_1`.
Set
`P=-w+q+3*[sector=LO]`, equivalently
- LO: `a+2d-6`
- LE: `a+2d-5`
- RO: `d+2a-1`
- RE: `d+2a-2`.

Using the output-parity sector map, the exact drift is
`P' - P = q' + L + 2*n1 + kappa`,
with kappa by input sector/output orientation:
- LO/L 9; LO/R 14
- LE/L 6; LE/R 9
- RO/L 0; RO/R 3
- RE/L 0; RE/R 5.

Hence every valid canonical four-sector transition with a nonempty drain has `P' >= P + q' + 1`. This is independent of the sign(g) simplification: it covers either exact output orientation. It rules out cycles wholly inside the canonical regime and gives a monotone weighted-mass measure, but it does **not** prove the root stays in that regime or exclude a terminal/low-gap transition.

The derivation is in the dossier, including the sector map and the c_A/kappa table. The identity itself is not yet a Lean theorem; it is an algebraic combination of the existing w-update and correction table. Please assess whether it can help the root/terminal-strip analysis, especially as a quantitative potential alongside the S-window invariant.
