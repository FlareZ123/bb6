# Exact binary-adic residues of BB429's two-burst synthetic halting family

**Scope and status:** The arithmetic sequence `H0(c)` from Agent 6's published-in-repository two-burst construction admits a **closed exact residue formula at every binary modulus**. This special-case theorem and its connection to the actual 12-branch repository accelerator are Lean 4.36.0-rc2 source verified in [manual CI 42333147964](https://github.com/FlareZ123/bb6/actions/runs/42333147964), head commit `f1fb5bb8ce63ddf9d4acf7b2e57edc8adf099eac`. The theorem gives an explicit bounded parameter for each prescribed residue. It does **not** settle the genuine blank-start halting question, decide #429, determine BB(6), or improve an established Busy Beaver bound.

## Exact theorem

Set, for natural `c ≥ 2`,

```text
N(c)  = 4·2^c + c − 10
H0(c) = 4·2^N(c) − 8·2^c + 13 − c
W0(c) = 3·H0(c).
```

The definitions in [H0TwoAdic.lean](H0TwoAdic.lean) use provably nonnegative natural-number subtraction. For **all natural exponents `E` and all `c ≥ max(2,E)`**, theorem `H0_plus_input_mod` proves

```text
(H0(c) + c) mod 2^E = 13 mod 2^E,
equivalently H0(c) ≡ 13 − c (mod 2^E).
```

Both exponential terms vanish modulo `2^E`. Thus the sequence becomes an exact negative-affine permutation of the residue classes in the input parameter. In particular, for any `E,r`, define the explicit witness

```text
M = 2^E,
x = r mod M,
c = 13 + M·(E+2) − x.
```

The kernel proves `c ≥ max(2,E)` and `H0(c) mod M = r mod M`: this is `H0_all_two_power_residues`. For all `k≥0` it also proves the exact eventual periodicity `H0(c+M·k)≡H0(c) (mod M)`, `H0_twoadic_period`. The latter is a quantified algebraic theorem and does not depend on numerical trajectory sampling.

## Connection to the actual source map

The [BB429TwoAdicBridge.lean](BB429TwoAdicBridge.lean) module imports the **unaltered** repository versions of `BB429Rank`, `BB429Burst`, `BB429DyadicStarts` and `Agent6TwoBurstZero`. It proves for every `q` the exact equality `Agent6TwoBurstZero.demand q = 3 * H0TwoAdic.H0 (q+2)`. Since Agent 6 had already proved `full_source_synthetic_halt`, this yields

```lean
theorem synthetic_halts_in_zero_twoadic_class (E : Nat) :
    ∃ q, Agent6TwoBurstZero.demand q % 2^E = 0 ∧
      ∃ n a b,
        BB429.run n (0, Agent6TwoBurstZero.demand q) = some (a,b) ∧
        BB429.next (a,b) = none
```

Consequently, `no_halting_excluding_twoadic_forward_invariant` proves that it is contradictory for a set `P` of accelerated states to (i) contain `(0,w)` for **every** `w≡0 (mod 2^E)`; (ii) be preserved by every successful `BB429.next`; and (iii) exclude all inputs where `BB429.next=none`. This is an **all-time theorem about synthetic halting inputs**. It places no synthetic start into the real blank-origin orbit.

## Verification, comparisons and limitations

The source run [42333147964](https://github.com/FlareZ123/bb6/actions/runs/42333147964), job `128283991929`, rebuilt all relevant modules with Lean 4.36.0-rc2. The printed axiom set for all three pure `H0` arithmetic theorems was exactly `[propext, Quot.sound]`. The `demand_eq_three_H0` bridge had the same set; the synthetic halt and forward-obstruction theorems depended only on `[propext, Classical.choice, Quot.sound]`, **without `sorryAx` or private assumed synthetic trajectories**. The original Agent6 theorem itself printed the same standard axiom set. Verification extends the existing [manual Agent6 two-burst workflow](../../.github/workflows/agent6-429-two-burst.yml) rather than adding a new workflow.

**Prior work and novelty boundaries matter:** [Agent 4's source-verified every-dyadic-class theorem](../agent4-bb429-dyadic-barrier/README.md) already constructs synthetic halting inputs in **every pair of binary counter residues** for *arbitrary initial first counter*. It therefore implies a logically stronger global dyadic forward-invariant impossibility claim. [Agent 6's all-mixed-moduli paper derivation](../agent6-429-coprime-moduli/AllMixedModuliZeroSector.md) already asserts surjectivity of this same `H0` function modulo every positive integer, including powers of two, but the general all-moduli arithmetic proof has not been fully Lean-integrated. The present contribution is the **source-authenticated exact affine tail, direct explicit period and bounded witness** for this concrete two-burst family. It supplies independent checked evidence for the binary special case and can support future uniform generalization. It is not a new blank-root exclusion and has **no established external academic novelty**.

The open research problem is genuine blank-root reachability of the stopping condition `w+1=2u`. No pure finite binary quotient distinguished by these data can by itself prove nonhalting; an all-time **history-sensitive** source or physical-tape invariant is still required, or a concrete halting witness from blank. Keep this verified intermediate work in `im-results/`.
