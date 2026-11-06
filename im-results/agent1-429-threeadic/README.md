# BB429 3-adic lifting: kernel-checked elementary infrastructure

**Mathematical status (6 November 2026):** The generic lifting theorem and the power-of-two period below compile locally in Lean 4.36.0-rc2, without `sorry` and with only standard axioms. This is an independent formalization of the arithmetic mechanism in Agent 6's [all-3-adic synthetic-halt argument](../agent6-429-coprime-moduli/AllThreeAdicCylinders.md), **not** a proof of Agent 6's complete source-map synthetic families, and not a genuine blank-root halt/nonhalt result.

## Precise statements

The reusable file [ThreeAdicLifting.lean](ThreeAdicLifting.lean) proves:

1. `all_residues`: For any `F : Nat → Nat` and lower parameter bound `n0`, assume every `e,n` satisfies
   `(F (n + 2*3^e) + 2*3^e) % 3^(e+1) = F n % 3^(e+1)`.
   Then for every exponent `E` and target `r`, there is `n` with `n0 ≤ n ≤ n0 + 2*(3^E-1)` and `F n % 3^E = r % 3^E`.
2. `power_period`: For every `e`, `2^(2*3^e) % 3^(e+1) = 1`.
3. `shift_two_power`: For every `e,t`, `2^(t+2*3^e) % 3^(e+1) = 2^t % 3^(e+1)`.

The residue-lifting proof splits into three bounded representatives in a fiber mod `3*m`, proves the exact two-step parameter shift, and inducts on the power of three. The power-period proof explicitly cubes the prior congruence and uses the factor of three in the modulus. There is no imported BB429 simulator or hidden source assumption in this Lean file.

## Reproduce and proof boundary

Local command: `lean im-results/agent1-429-threeadic/ThreeAdicLifting.lean` with Lean 4.36.0-rc2, importing only `Lean.Elab.Tactic.Omega`. The local compilation passed on 6 November 2026. The `#print axioms` output was `[propext, Quot.sound]` for `all_residues` and `[propext, Classical.choice, Quot.sound]` for both power statements; no `sorryAx`.

**Unproved in this file:** the three concrete sequence shift hypotheses for Agent 6's `G2,G1,H0`, exact all-parameter full-map halting trajectories, and any connection from a synthetic `(0,W)` to the authentic blank start `(0,0)`. Agent 6 supplies the machine-specific hand proof and sample computation separately. A direct source-checked Lean theorem for all three families is the appropriate next integration step.

**Originality:** Formalizes a general, elementary lifting lemma already argued on paper by Agent 6; no claim of external mathematical priority, independent BB(6) progress, or publication-ready result. All material belongs in `im-results/`.
