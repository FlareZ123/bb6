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


## New Machine B blank-orbit modular decision gate

The absolute blank-orbit invariant `(iterG n 0)%7 ≠ 6` holds for every `n` (`BMod7Core.lean`, `BMod7NoSix.lean`). Its mechanism is exact: `(G z+1)%7=(5*(z+1))%7`, and therefore `(iterG n 0+1)%7=5^n%7`. All of these statements are proved for unbounded `n`.

More decisively, `BMod7Period.lean`, `BMod7Cycle.lean`, `BResetArithmetic.lean`, `BResetMod7Constraints.lean`, `BResetMod7Criterion.lean`, and `BResetMod7Machine.lean` establish the globally quantified equivalence

```lean
BB6.OneDim.local_halts_iff_index_mod7 :
  BB6.BReduction.Halts (3,0,0) ↔
    ∃ n : Nat,
      (scalarA (n+1))%7=0 ∨ (scalarA (n+1))%7=6
```

**Proof outline.** Every hypothetical reset index `scalarA n` is odd and avoids residue 2 modulo 3. Thus it equals 1 or 3 modulo 6. The exact six-period of `5^n mod7` implies every sampled scalar output `iterG (scalarA n) 0` is 4 or 5 modulo 7. The reset arithmetic adds 9 after an even sample and adds 6 after an odd sample. The next hypothetical reset index is therefore 0 or 6 modulo 7 **exactly for an even sample**. Agent18's already established all-time local halting iff sampled-even criterion composes to the displayed equivalence.

All modules successfully compiled against **unmodified Agent18 full source** in the manual [CI 41414167867](https://github.com/FlareZ123/bb6/actions/runs/41414167867), with only standard axioms and no sorryAx. A separate pinned Cryptids original-six-state-machine composition module `Agent33RawBMod7Bridge.lean` and manual workflow `agent33-b-mod7-raw.yml` were added for the distinct raw semantic step; cite a successful exact CI run before calling the new direct raw-machine theorem fully source certified.

This is an exact alternative formulation of the still-open Machine B halting question, not a resolution. The synthetic reset sequence is defined beyond any possible halt specifically to make the quantified equivalence precise. Avoid inferring that physical machine runs progress to the post-halt index.



## Priority and novelty correction after cross-agent audit (2026-11-02 08:42 UTC)

**Important preexisting work:** Agent 24's `im-results/agent24-b-parity/README.md`, `BParityCoding.lean`, `BResetResidues.lean`, and `Agent24BResidueBridge.lean` already prove the finite parity-coding bijection, exact mod-7 behavior, all-time sampled parity iff next-index residue dichotomy, and the complete original-machine modular criterion, with successful [source CI 41403230037](https://github.com/FlareZ123/bb6/actions/runs/41403230037) at 07:03 UTC. Agent 24 goes further with mod-42 classification, counterexamples to naive modular induction, and quantitative aperiodicity. Our independently derived modules reproduce those earlier findings via a different proof organization and compile them directly against Agent18's original source. They **must not be described as new within this repository or as an advance over Agent24's strongest result**.

The particularly clean **constant-parity run iff `2^n∣z+8` or `2^n∣z+15`** theorem in `BConstantRuns.lean` is an additional exact source-certified lemma not explicitly stated in Agent24's summary, although it is a standard generalized Collatz affine-branch observation. The main practical contribution here is reproducible cross-validation and this run-length lemma. Agent24's existing original-machine source bridge should be cited as primary provenance for the modular halting equivalence. Avoid redundant further modulo-7 or parity-coding investigations. Pursue genuinely stronger blank-orbit information or different unresolved holdouts.

