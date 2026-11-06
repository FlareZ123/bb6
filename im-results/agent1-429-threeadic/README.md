# BB429 synthetic-family 3-adic congruences: three Lean proofs

**Mathematical status (6 November 2026).** All three parameter functions occurring in Agent 6's [synthetic BB429 halting families](../agent6-429-coprime-moduli/AllThreeAdicCylinders.md) are now separately proved to cover every congruence class modulo every power of three. The entire modular-lifting chain was compiled locally in **Lean 4.36.0-rc2** without `sorry` or custom axioms. This closes the *arithmetic surjectivity* obligation in the existing paper argument. Source-specific machine halting trajectories, genuine blank-root reachability and exact BB(6) remain separate open proof obligations.

## Formal theorems and exact parameter bounds

[ThreeAdicLifting.lean](ThreeAdicLifting.lean): The generic `all_residues` theorem proves the uniform lift principle. For every `F : Nat → Nat`, if
`(F (n+2*3^e)+2*3^e) % 3^(e+1) = F n % 3^(e+1)`
for all `e,n`, then every target residue modulo `3^E` occurs for some
`n0 ≤ n ≤ n0+2*(3^E-1)`. Its auxiliary `power_period` proves `2^(2*3^e) % 3^(e+1) = 1`.

[ThreeAdicG2.lean](ThreeAdicG2.lean) proves the precise shift condition and `G2_all_residues` for
`G2(t)=4*2^t-t`, `t≥1`, together with `G1_all_residues` for
`G1(q)=16^q-q`, `q≥1`. Each covers all residues modulo `3^E`, with a witness at most `1+2*(3^E-1)`.

[ThreeAdicH0.lean](ThreeAdicH0.lean) proves `H0_all_residues` for the nested-exponential function
`N(c)=4*2^c+c-10`,
`H0(c)=4*2^N(c)-8*2^c+13-c`, with `c≥2`.
It proves the core all-parameter congruence
`(H0(c+2*3^e)+2*3^e) % 3^(e+1) = H0(c) % 3^(e+1)`,
and an explicit witness `2 ≤ c ≤ 2+2*(3^E-1)` for every residue modulo `3^E`. The Lean `H0_eq_paper` theorem certifies agreement of the guarded natural subtraction definition with Agent 6's paper formula for every c≥2. The proof of exponent shift constructs an exact multiple of `2*3^e` between `N(c+2*3^e)` and `N(c)`.

## Verification, provenance, and limitations

The modules import in the order `ThreeAdicLifting`, `ThreeAdicG2`, `ThreeAdicH0`. Compile each to an `.olean` with Lean 4.36.0-rc2 before importing the next. The local axiom audits list only `propext`, `Quot.sound`, and `Classical.choice` for power-dependent theorems, with no `sorryAx`; the H0 formula-equivalence theorem uses only `propext` and `Quot.sound`. The code imports core Lean tactics, including `omega` and `grind +ring`; there is no Mathlib dependence.

These three functions underlie the proposed synthetic full-map halting starts `W2=3*G2-13`, `W1=24*G1-29`, and `W0=3*H0`. Agent 6 independently derived the affine transport from each function to its respective `w mod 3` residue class and described the associated BB429 macro-machine trajectories. **The three-source-map trajectory theorems, plus an integrated formal all-`3^E) synthetic BB429 halting theorem, have not been proved in this dossier.** These are source-independent arithmetic proofs, not a certification of the complete machine or the authentic blank input.

The lifting mechanism and all-three-family arithmetic claim were already argued on paper by Agent 6. This independently checks the entire elementary modulo-three parameter argument in the Lean kernel. It is preserved in `im-results/` as an intermediate verification result, without a claim of external priority, publishable novelty or any new Busy Beaver bound.
