# Exact Machine B dyadic curvature and affine-modulus classification

Agent 30, 2026-11-03. R007 exploration. **Source-connected Lean kernel checked**. This is a structural restriction on an undecided Busy Beaver machine's scalar accelerator, not a proof of halting or nonhalting.

## Theorems

For `G(z)=3*(z/2)+4+5*(z%2)` and `F_n(z)=G^[n](z)`, the centered second difference at dyadic spacing satisfies, for every `n,z:Nat`,

`F_(n+1)(z)+F_(n+1)(z+2*2^n)-2*F_(n+1)(z+2^n) ∈ {-7,+7}`.

The sign depends on the parity of `F_n(z)`. This identity holds for all starting counters and all positive iteration counts. Consequently, for every `n>0` and `m>0`,

`(∃ a b:Nat, ∀ z:Nat, F_n(z)%m=(a*z+b)%m) ↔ (m=1 ∨ m=7)`.

Thus **seven is the only nontrivial modulus with an all-input affine formula for any positive iterate**. The `n=0` identity-map case is excluded. At `m=7`, the coefficients `a=5^n`, `b=8*5^n+6` provide the affirmative construction, derived from Agent10's existing modulo-seven theorem.

## Proof mechanism

Agent10's exact 2-adic shift theorem states `F_k(z+2^k*d)=F_k(z)+3^k*d`. Put `x=F_k(z)` and the odd number `s=3^k`. The points `z,z+2^k,z+2^(k+1)` therefore map after `k` iterations to `x,x+s,x+2s`. Direct algebra for the next step gives `G(x)+G(x+2s)+7=2G(x+s)` when `x` is even, and `G(x)+G(x+2s)=2G(x+s)+7` when `x` is odd.

An affine modular function has zero centered second difference, so a universal affine congruence of the positive iterate forces `m | 7`. Positivity leaves only 1 and 7. Agent10 already proves `(F_n(z)+8)%7=(5^n*(z+8))%7`, yielding the explicit modulo-seven affine coefficients. Every prohibited modulus and positive iterate has a three-input obstruction witness `0,2^(n-1),2^n`. No finite forward-cutoff assumption is used.

## Formal evidence

- [BModularCurvature.lean](./BModularCurvature.lean) proves the exact curvature and necessity of `m | 7`.
- [BModularSource.lean](./BModularSource.lean) transfers them to the original Agent18 scalar return map.
- [BModularClassification.lean](./BModularClassification.lean) proves the complete iff theorem with Agent10's pre-existing modulo-seven identity.
- [Manual workflow](../../.github/workflows/agent30-b-curvature.yml) compiles original Agent18, Agent10, and the new source-connected modules under pinned Lean 4.36.0-rc2.

[CI run 41557566942](https://github.com/FlareZ123/bb6/actions/runs/41557566942), 2026-11-03 01:07 UTC (head `10042275bac5b689112f5d9a2f33add7c31b9dce`), succeeded. Its logs report `BB6.Agent30B.source_affine_quotients_iff` and the source curvature theorem with only `[propext, Quot.sound]` axioms. There are no `sorryAx` dependencies.
