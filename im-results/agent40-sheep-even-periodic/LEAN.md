# Lean-certified arithmetic components of the E-inverse family certificate

Agent 40, 2026-11-02. Built and compiled against the locally reconstructed official Lean **4.36.0-rc2** binary, importing `Std` and no other user modules. Both source files are retained plainly in this directory.

## Verified theorems

[`EvenOffsetPeriod.lean`](./EvenOffsetPeriod.lean) proves `SheepEvenNew.signed_affine_period`: for any natural `d,M,n,k`, arbitrary **signed** `B:Int`, and hypotheses `1<d`, `0<n`, `2^M%d=1`,
```
((2^(n+M*k):Nat):Int)+B  ≡  ((2^n:Nat):Int)+B  (mod (2*d:Nat))
```
It also proves `odd_quotient_residue` and `exclude_signed_pair`, giving the exact parity-sensitive exclusion used for the odd quotient in a generic E inverse. All three `#print axioms` results were `[propext, Quot.sound]`.

[`EvenInverseIdentity.lean`](./EvenInverseIdentity.lean) gives three unbounded **all-parameter** algebraic proofs. Define `X=2^h, Y=3^h, A=2^a, P=2^(j+s)` with `d>0`, signed `b`, and assume the exact E-parent equations
```
d*(1+Y*U) = P+b,
2*(1+X*U) = (2*A+1)*V+2*a-1.
```
Then `generic_inverse_identity` derives the exact scaled inverse equation
```
2*X*P + 2*(X*(b-d)+d*Y) - d*Y*(2*a-1) = d*Y*(2*A+1)*V.
```
The theorem `high_h_divisibility` proves the necessary exact modular condition `(P+b-d) % (d*Y)=0`. The theorem `generic_inverse_parity` proves that, whenever `V` is odd, the scaled left side above is congruent to `d*Y*(2*A+1)` modulo `2*d*Y*(2*A+1)`. These algebraic results are completely independent of fixed exponent periods, horizons, and the three specific candidate families. All `#print axioms` results were `[propext, Quot.sound]`.

Reproduction (assuming Lean 4.36.0-rc2 already available): compile each `.lean` file with that Lean executable. No Mathlib, no `sorry`, no `admit`, no `native_decide`, and no mock signatures were used.

## What remains outside these theorems

The source-certified machine-level correspondence `raw_halts_iff_even_power` is already provided by Agent 16, [successful original-source CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547). The new lemmas are all-parameter algebraic *sublemmas* for deriving the E-predecessor table. The full three-family no-reach theorem is **not** yet a Lean theorem: formal reflection of the finite low-valuation certificate, high-valuation residue-gap proof, all-exponent exceptional-branch bound, and composition with the Agent16 graph remains to be implemented. The independent proof dossier and exact arithmetic certificate are [README.md](./README.md) and [certify.py](./certify.py).

The appropriate next mathematical investment is a generic reflective E-inverse certificate (a small Lean proof kernel accepting period witnesses and bounds) rather than manually writing one Lean proof per residue class. This would certify arbitrary future all-index E inverse trees and permit reuse on other original-machine rooted holdouts.
