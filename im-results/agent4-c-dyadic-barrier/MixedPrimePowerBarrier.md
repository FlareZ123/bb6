# Machine C: arbitrary mixed 2-adic/3-adic blank-cylinder contamination

**Agent 4, 2026-11-05. Status: complete elementary paper derivation, not yet Lean-kernel certified as a quantified all-`e,j` theorem.** Earlier Lean source certifies the underlying exact Machine C stopping equation, and the separate `e`-uniform, factor-three `CDyadicMod6.lean` formalizes a special case. The actual blank orbit remains undecided, as does BB(6). Nothing here establishes a real blank-origin halting state.

## General quantified claim (paper mathematics)

For every natural pair `e,j`, put `M=2^e*3^j`. There exists a natural right counter `K` with

```text
K ≡ 1 (mod M)
BB6.Agent46.secNext (5,K) = none.
```

Therefore the *authentic blank-section input* `(5,1)` has an **immediately halting synthetic representative in its residue-pair cylinder modulo each `M=2^e*3^j`**. Every finite residue-saturated source-state invariant containing `(5,1)` and excluding immediate halts fails already at that initial abstract cylinder. This conclusion concerns one restricted family of moduli; it says nothing about arbitrary moduli with primes at least 5, nonperiodic invariants, or root-specific true reachability.

## Proof, with all parameters unrestricted

The existing source-verified exact two-family stopping theorem (`Agent1Unified.source_section_halts_iff_one_equation`, itself based on Agent15's original `secNext` classification) reduces the `a=5` immediate stopping condition to the parameter family

```text
K+3m+6 = 4^(m+2),  m≥0.
```

Set `n=m+2`. Its candidate is `K=4^n-3n`; hence `K-1=4^n-3n-1`. We need to find `n≥max(2,e)` so that this difference is divisible by `2^e` and `3^j`.

1. Because `3` is invertible modulo `2^e`, the linear congruence `3n+1≡0 (mod 2^e)` has a solution `n≡r_e (mod2^e)`. For `e=0` the modulus is one and this condition is vacuous.
2. Impose independently `n≡1 (mod3^j)`. The moduli `2^e` and `3^j` are coprime; the ordinary Chinese Remainder Theorem gives a simultaneous solution and a full infinite arithmetic progression of solutions. Select `n≥max(2,e)`.
3. The elementary exponential congruence `4^(3^j)≡1 (mod3^j)` holds for every `j≥0`. For a direct proof, use the stronger induction `4^(3^j)≡1 (mod3^(j+1))`: base `4≡1 (mod3)`; if `A=4^(3^j)=1+3^(j+1)*t`, then `A^3-1=3(A-1)+3(A-1)^2+(A-1)^3`, whose summands are all multiples of `3^(j+2)`. This establishes the induction.
4. Since `n≡1 (mod3^j)` and `n≥2`, write `n-1=3^j*t`; step 3 gives `4^(n-1)≡1 (mod3^j)`, whence `4^n≡4 (mod3^j)`. Likewise `3n+1≡4 (mod3^j)`, so `4^n-3n-1≡0 (mod3^j)`.
5. Because `n≥e`, `2^e∣4^n`; because of step 1, `2^e∣(3n+1)`. Thus `2^e∣4^n-3n-1`. Coprimality of the moduli gives `M∣K-1`.
6. For all `n≥2`, `4^n≥3n+1` by induction, so `K=4^n-3n` is a positive natural right counter. Set `m=n-2`. Then `K+3m+6=4^(m+2)`, precisely the proven source stopping criterion. Therefore `secNext (5,K)=none` and `K≡1 (modM)`.

The use of the Chinese Remainder Theorem and the exponential congruence is exact; there is no finite-computation extrapolation. The theorem should be formalized in original-source Lean prior to describing it as *kernel checked*. The source's existing parametric stopping iff and the smaller `j=1` theorem `CDyadicMod6.lean` provide a ready integration path.

## Relation to the #429 dyadic theorem and research priorities

The separate `BB429EveryDyadicClass.lean` is fully Lean source certified, but its machine is a different 12-branch map and its synthetic inputs halt after a finite first-burst. For Machine C, synthetic representatives here halt at the very first section call. In both cases the method obstruction applies only to **all-input residue-saturated abstract forward invariants**, and supplies no actual blank-halt witness or upper bound on BB(6). A genuinely useful next research direction is history-sensitive, nonperiodic, or exact-inverse provenance that distinguishes synthetic halting inputs from the actual blank orbit.
