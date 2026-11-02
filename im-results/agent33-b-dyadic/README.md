# Exact dyadic parity coding for Machine B (Agent 33)

**Status:** Intermediate all-natural, kernel-checked structural result about the published Machine B scalar acceleration, without any new BB(6) bound or machine-halting decision. No claim of external mathematical novelty: the dyadic coding resembles standard generalized Collatz-map constructions.

The six-state machine is `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`, with certified blank entry `(3,0,0)` in the reduction. Agent18's preexisting `raw_halts_iff_two_branch` gives an exact source-certified equivalence of the original machine with the sampled-parity question; see `im-results/agent18-b-cycle/ONE-DIMENSIONAL.md`.

## Exact theorem statements

For the exact Agent18 map

```
G z = 3*(z/2)+4+5*(z%2)
iterG 0 z = z
iterG (n+1) z = iterG n (G z)
```

the new source-verified Lean modules prove:

1. **Uniform dyadic affine covariance** (`BDyadicCore.lean`, `iterG_dyadic_shift`): for all naturals `j,k,q,z`, `iterG j (z+q*2^(k+j)) = iterG j z + q*3^j*2^k`.
2. **Finite parity-word realization** (`BDyadic.lean`, `arbitrary_finite_parity_word`): every binary word of length `n` is the first `n` output-parity symbols of some input `z<2^n`. Adding `2^n` preserves all earlier symbols but flips symbol `n`.
3. **Constant-run characterization** (`BConstantCore.lean`, `BConstantRuns.lean`, `scalar_constant_run`): for `bit≤1`, all of the first `n` symbols equal `bit` iff `2^n ∣ z+(if bit=0 then 8 else 15)`. Exact balance identities: `2(Gz+8)=3(z+8)` on even `z` and `2(Gz+15)=3(z+15)` on odd `z`.
4. **Uniqueness modulo `2^n`** (`BCodingBalance.lean`, `BCodingCore.lean`, `BCodingUnique.lean`): identical first `n` parity symbols force initial inputs to be congruent modulo `2^n`; in particular each finite binary word has **exactly one** representative `z<2^n` realizing that word.

The fourth theorem strengthens finite-prefix existence into an explicit full binary coding bijection of the `2^n` initial residues.

## Verification

The exact, **unmodified full repository source** of `Agent18BReduction.lean` and `Agent18BOneDim.lean` was compiled before all Agent33 proof sources by the manual-only workflow `.github/workflows/agent33-b-dyadic-verify.yml`. Successful [CI run 41412360813](https://github.com/FlareZ123/bb6/actions/runs/41412360813) on 2026-11-02 compiled all modules and prints:

- `iterG_dyadic_shift`: `[propext, Quot.sound]`.
- `arbitrary_finite_parity_word`: `[propext, Quot.sound]`.
- `scalar_constant_run`: `[propext, Quot.sound]`.
- `parity_prefix_unique_residue`: `[propext, Quot.sound]`.

No `sorryAx`, `native_decide`, mock definition, imported unproved axiom, or failed source import in the successful run. Earlier CI [41411405353](https://github.com/FlareZ123/bb6/actions/runs/41411405353) and [41411831840](https://github.com/FlareZ123/bb6/actions/runs/41411831840) established intermediate parts before the full source certification.

## Mathematical limits

The exact Machine B halting criterion tests parities of the one special orbit starting `z=0` at an extremely sparse, recursively constructed sequence of times `A_n`. Full dyadic coding on arbitrary starts `z` does not constrain those sampled parities, establish termination, or show nontermination. In fact, the coding theorem warns that finite parity obstructions valid only for *generic start residues* cannot alone rule out all finite patterns. Further work requires a structural property of the actual pair `(z=0,A_n)`, not generic initial-value coding.

All evidence is intentionally in `im-results/`. No publishable BB(6) result asserted.
