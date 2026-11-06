# BB429 synthetic-family 3-adic congruence: Lean proof

**Status (6 November 2026).** The generic lifting theorem, power periods, and the specific 3-adic residue coverage of **two** BB429 synthetic-input parameter functions have been checked in local Lean 4.36.0-rc2, without `sorry`. This formally establishes their arithmetic surjectivity, conditional on the separate machine-trajectory mathematics. It does **not** prove that these synthetic starts halt in the unchanged BB429 source, that authentic blank reaches them, or any decision of BB429 or BB(6).

## Verified arithmetic results

[ThreeAdicLifting.lean](ThreeAdicLifting.lean) proves:

- `all_residues`: if `(F(n+2*3^e)+2*3^e) % 3^(e+1)=F(n) % 3^(e+1)` for every `e,n`, every residue modulo `3^E` is hit between parameter `n0` and `n0+2*(3^E-1)`. The proof is an explicit three-lift argument with all time bounds.
- `power_period`: `2^(2*3^e) % 3^(e+1)=1` for all `e`, by induction and the cube lift.
- `shift_two_power`: multiplying by the period preserves any `2^t` residue modulo `3^(e+1)`.

[ThreeAdicG2.lean](ThreeAdicG2.lean), importing the generic file, proves exact shift congruences and all-power residue coverage for both

`G2(t)=4*2^t-t`, `t≥1`, and `G1(q)=16^q-q`, `q≥1`.

In particular every residue modulo `3^E` is realized by each function with a parameter at most `1+2*(3^E-1)`. This is directly relevant to Agent 6's synthetic start families `W2=3*G2-13` and `W1=24*G1-29`. The third synthetically halting family, involving nested exponential `H0(c)`, still requires an all-parameter Lean shift theorem.

## Verification and remaining source obligations

Both modules were checked with Lean 4.36.0-rc2 locally. Compile `ThreeAdicLifting.lean` to an `.olean` then import it when compiling `ThreeAdicG2.lean`. All named theorem axiom audits contain only standard `propext`, `Quot.sound`, and in power-dependent theorems `Classical.choice`. No custom axiom or `sorryAx`.

The existing [Agent 6 three-family paper derivation](../agent6-429-coprime-moduli/AllThreeAdicCylinders.md) establishes the proposed BB429 complete-map synthetic trajectory formulas and the third parameter congruence on paper, with a separate BigInt simulator. Those assertions are **not yet transported into these Lean modules**. Closing those machine-source obligations and separately investigating authentic blank-root reachability would be needed for machine decisions.

The generic lifting mechanism is elementary and previously derived by Agent 6; this independently kernel-checks two relevant infinite parameter surjectivity cases. It is a complementary verification result in `im-results/`, without any claim of independent mathematical novelty or an improved BB(6) bound.
