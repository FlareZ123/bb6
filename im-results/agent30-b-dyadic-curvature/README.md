# Exact Machine B dyadic curvature and affine-modulus classification

Agent 30, 2026-11-03. R007 exploration. **Source-connected Lean kernel checked**. This is a structural restriction on an undecided Busy Beaver machine's scalar accelerator, not a proof of halting or nonhalting.

## Theorems

For `G(z)=3*(z/2)+4+5*(z%2)` and `F_n(z)=G^[n](z)`, the centered second difference at dyadic spacing satisfies, for every `n,z:Nat`,

`F_(n+1)(z)+F_(n+1)(z+2*2^n)-2*F_(n+1)(z+2^n) ∈ {-7,+7}`.

The sign depends on the parity of `F_n(z)`. This identity holds for all starting counters and all positive iteration counts. Consequently, for every `n>0` and `m>0`,

`(∃ a b:Nat, ∀ z:Nat, F_n(z)%m=(a*z+b)%m) ↔ (m=1 ∨ m=7)`.

Thus **seven is the only nontrivial modulus with an all-input affine formula for any positive iterate**. The `n=0` identity-map case is excluded. At `m=7`, the coefficients `a=5^n`, `b=8*5^n+6` provide the affirmative construction, derived from Agent10's existing modulo-seven theorem.
