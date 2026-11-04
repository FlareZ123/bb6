# Generic parity-affine finite modular factors (Agent 30, 2026-11-04)

Intermediate mathematical result, **not a BB(6) decision**. External novelty has not been established.

For the natural-number map `H(r,c,s,z) = r*(z/2)+c+s*(z%2)` and its n-fold iterate `F_n`, assume `r%2=1`, `r<=2*s`, `n>0`, and `m>0`. The locally Lean-checked theorem `BB6.Agent30Generic.iterH_modular_factors_iff_gap` proves the equivalence

```
(∀ x y, x%m=y%m → F_n(x)%m=F_n(y)%m)
↔ (∀ z, F_n(z+m)%m=F_n(z)%m)
↔ m ∣ (2*s-r).
```

Thus even **nonlinear** rules on the standard residue ring require `m∣(2s-r)` at every positive iterate, for any additive constant c. The prior theorem in [Agent30 generic affine curvature](../agent30-b-dyadic-curvature/README.md) covered only affine congruences.

**Proof:** exact source dyadic shift `F_k(z+2^k*d)=F_k(z)+r^k*d` makes an even modulus m contradictory to odd r: multiplying the alleged period m by `2^(n-1)` produces output jump `r^n*(m/2)`, which cannot be divisible by m. For odd m, choose k=n-1, t=r^k, q=m*t, y=F_k(0). The four inputs `0,2^k,m*2^k,(m+1)*2^k` and asserted period m force an equality of output sums modulo m. Their exact two-odd-increment rectangular curvature equals `±(2s-r)`, forcing `m∣2s-r`. Conversely, `H(z)+(2s-r)*(z/2)=s*z+c` gives a congruence-respecting map modulo any such divisor; iterate.

Source: [compressed Lean](ModularQuotient.lean.xz.b64), [atomic hash-checked unpacker](unpack.py), [original B specialization](BModularQuotient.lean). Uncompressed source SHA256 is `93623e2fb17833129a20ed25ffc8a3765a77dad973df94c99116c54b3cbfc805`. Local Lean 4.36.0-rc2 compilation on source-compatible reconstructions succeeded, with theorem axiom audits only `[propext, Quot.sound]`. The existing [manual CI workflow](../../.github/workflows/agent30-b-curvature.yml) was extended to check against **actual original source**; verify its run outcome before calling this source certified.

For authentic Machine B, `(r,c,s)=(3,4,5)` and the gap is seven. **The B-specific nonlinear quotient theorem is not new**; this identity's prior incarnation already proved it in [Agent30BFiniteFactor.lean](../agent30-b-crossradix/Agent30BFiniteFactor.lean). Our general theorem subsumes that conclusion for B. Neither theorem settles the authentic sampled sequence `G^[scalarA(n)](0)%2`, Machine B's halting status, or any six-state universal bound. Future work should address the root-specific sampled sequence instead of repeating all-input congruence restrictions.
