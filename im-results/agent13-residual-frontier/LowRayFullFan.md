# Machine C low-stop ray: complete original-source parent form and exact dyadic depth bound

**Mathematical status (23 November 2026).** The exact original Machine C section predecessor grammar has now been specialized, **without any depth cutoff**, to the entire necessary low-stop progression (m=512z+67). For every (z\ge0) every original section parent of its four-step inverse target is an ordinary *odd-source, even-depth high bounce*, and its bounce depth satisfies

[
  2^n\mid 519z+73,\qquad
  n\equiv0\pmod2,\qquad
  n\le\lfloor\log_2(519z+73)\rfloor.
]

The exact dyadic criterion is stronger: **for every natural n,**

[
2^{n+2}\mid(346u+54) \quad\Longleftrightarrow\quad
2^n\mid(519z+73),
\qquad u+6z+1=2^{1024z+129}.
]

This is a full *immediate-predecessor classification and exponent reduction*, **not** a proof that any parent is blank-reachable, that the stopping target is impossible, that Machine C never halts, or that BB(6) is solved. The remaining parent families (and the unrestricted high stopping branch) must be eliminated or reached.

## Exact coordinates and source dependence

The original low-stop criterion has (k+3m+4=2^{2m+3}). Substituting (m=512z+67) gives (k=256u+51) where

[
T=1024z+129,\qquad u=2^T-6z-1.
]

The accepted source-exact four-step inverse of ((1,256u+51)) has output target

[
R_u=(180u+28,\ 166u+25).
]

Its odd-bounce mass is (Q=x+y+1=346u+54). Put (C=519z+73>0). The elementary identity

[
Q+4C=346\cdot2^T
]

holds exactly. Also (4C<2^T), since (2^{1024z+127}\ge1024z+128>519z+73); consequently

[
2^{T+8}<Q<2^{T+9}.
]

In particular, **Q is never a pure power of two**, even at arbitrarily high 2-adic valuation. This removes the special (a=1) predecessor that would otherwise survive the general even-left/odd-right inverse grammar. Source-complete theorem `BB6.Agent13AllFan.even_odd_nonpower_parent` proves every actual parent ((a,k)) of (R_u) has (a\ge3), odd (a), high-bounce input (a<2k), even bounce depth (n), and

[
Q=2^n\bigl(2(a-1)+8\bigr),\qquad
2k+a+7+3n=512u+78.
]

These are necessary and reflect the literal original section transition relation; they have no synthetic-tape or quotient substitutions.

## Exact dyadic equivalence

For any integer exponent (n\ge0), the factor (2^{n+2}\mid Q) is equivalent to (2^n\mid C). The proof is elementary and covers *all* n, not only those below a numerical cutoff:

1. If (2^{n+2}\mid Q) and (n+2\ge T), then (2^T\mid Q) and thus (2^T\mid4C); this is impossible because (0<4C<2^T). Hence (n+2<T) and subtraction from (346\cdot2^T) shows (2^{n+2}\mid4C), whence (2^n\mid C).
2. Conversely, if (2^n\mid C), then (2^{n+2}\le4C<2^T), forcing (n+2<T). Both (346\cdot2^T) and (4C) are divisible by (2^{n+2}), and so is their difference Q.

Because (a\ge3) is odd, its source factor (2(a-1)+8) is a multiple of four. Combining the source equation with the exact dyadic equivalence yields (2^n\mid C); since C is positive, (2^n\le C), and thus the logarithmic depth bound.

An immediate arithmetic consequence is \(\nu_2(Q)=2+\nu_2(C)\). Combining this with the *already established* complete section-indegree formula in [Agent 34's exact local inverse-degree law](../../results/2026-11-08-machine-c-exact-indegree-distribution-agent34.md), which counts the predecessors of an even-left/odd-right target with nonpure Q, gives the **paper-level exact indegree specialization**

[
 \#\operatorname{secNext}^{-1}(R_u)
  =1+\Bigl\lfloor\frac{\nu_2(519z+73)}2\Bigr\rfloor.
]

The enumerated possible source depths are precisely the even integers (n=0,2,\ldots,2\lfloor\nu_2(C)/2\rfloor). The displayed *cardinality and sufficiency for every allowed depth* follow from the existing source-complete inverse degree theorem and are **not a separately exported Lean counting theorem** in this module. The axiom-audited new Lean theorems cover the precursor source classification, power gap, exact dyadic iff, and universal necessity of the depth bound.

For example, (z=0) has (C=73) and exactly one immediate parent; (z=1) has (C=592=16\cdot37) and exactly three. The degree is unbounded along 2-adic index progressions because 519 is odd and admits an inverse modulo every (2^d), so (519z+73) can have arbitrarily high valuation. Crucially, these are *all section parents*, not reachable ancestors of the authentic blank orbit.

## Certified modules and limitations

- [EvenOddAllValuationParent.lean](EvenOddAllValuationParent.lean): `even_odd_nonpower_parent`, complete unchanged-source proof for every large nonpower even-left/odd-right output, accepted [CI 45269554412](https://github.com/FlareZ123/bb6/actions/runs/45269554412).
- [EvenOddLowStopPowerGap.lean](EvenOddLowStopPowerGap.lean): `low_mass_strict_gap`, `low_mass_not_power_two`, `all_low_ray_parents_are_even_bounce`, accepted [CI 45270017711](https://github.com/FlareZ123/bb6/actions/runs/45270017711).
- [EvenOddLowStopDivisor.lean](EvenOddLowStopDivisor.lean): exact dyadic iff `low_mass_divisor_iff`, generic cancellation theorem `subtract_small_power_divisor_iff`, and source parent theorem `all_low_ray_parent_depth_logbound`, accepted [CI 45271285852](https://github.com/FlareZ123/bb6/actions/runs/45271285852). Full 20-module original project closure, Lean 4.36.0-rc2; exported axiom profiles `[propext, Quot.sound]` for arithmetic and `[propext, Classical.choice, Quot.sound]` for source-connected parent statements; no `sorryAx`, no `native_decide`.

All three jobs reuse the existing *manual* `.github/workflows/agent13-m16-high-family-interface.yml`. There is no new workflow file or per-commit run.

The independent [all-depth source-word sieve](AllDepthSourceParentPruning.md) may exclude particular individual candidates after the classification. Its formal phase fraction is **not** a count of solved candidate machine orbits. To close even this low-stop ray, one must eliminate *every* surviving permitted depth for *every* z using a genuine blank-root inverse invariant or exhibit a genuine root hit. The high-stop family in the exact Machine C halting criterion remains unrestricted by these statements.


## Full original-source edge iff: the completeness statement is now formal

The prior parent classification and dyadic bound have been strengthened to a source-exact **necessary AND sufficient** edge criterion for *every* stopping index z, with no bound on the bounce depth:

```
secNext(a,k) = some (180*u+28,166*u+25)
    ↔ ∃ n, n%2=0 ∧ 3≤a ∧ a<2*k ∧
         346*u+54=2^(n+1)*(a+3) ∧
         2*k+a+7+3*n=512*u+78.
```

The reverse direction is significant: it reconstructs an actual `secNext` machine edge from the source arithmetic via the complete original-section inverse theorem; it does *not* treat an arithmetic candidate as automatically genuine. Accepted in [Lean CI 45275606485](https://github.com/FlareZ123/bb6/actions/runs/45275606485), source [EvenOddLowStopFullInverseIff.lean](EvenOddLowStopFullInverseIff.lean).

For **every even z**, `519*z+73` is odd, so the only allowed depth is n=0. In fact [EvenOddLowStopEvenEdgeIff.lean](EvenOddLowStopEvenEdgeIff.lean) proves the stronger exact source singleton-fiber equivalence

```
secNext(a,k)=some (180*u+28,166*u+25)
  ↔ a=173*u+24 ∧ k=(339*u+47)/2,
   provided z%2=0 and u+6*z+1=2^(1024*z+129).
```

This establishes *actual original section indegree exactly one* for the entire unbounded even-z half-ray, [CI 45276324981](https://github.com/FlareZ123/bb6/actions/runs/45276324981). [EvenOddLowStopEvenReachIff.lean](EvenOddLowStopEvenReachIff.lean) further proves the genuine **blank-root reachability iff** between `R_u` and its unique parent, [CI 45276448739](https://github.com/FlareZ123/bb6/actions/runs/45276448739). Thus the even-index low ray is no longer an *inverse-enumeration problem*: it is a single explicit recursive root obligation. Neither theorem excludes that last parent in general.

## New all-time rooted exclusions and the integrated gateway

Two source-exact independent inverse words exclude complete previously open low-stop index progressions:

- `z≡44 mod64`, `u≡119 mod128`: forced inverse word F-A-B-O ends at an odd-right source-image contradiction. Accepted [CI 45272616908](https://github.com/FlareZ123/bb6/actions/runs/45272616908), [LowM67Z44Source.lean](LowM67Z44Source.lean).
- `z≡16 mod128`, `u≡159 mod256`: forced F-A-A-A-A-B ends in a different odd-right forbidden-image class. Accepted [CI 45274516141](https://github.com/FlareZ123/bb6/actions/runs/45274516141), [LowM67Z16Source.lean](LowM67Z16Source.lean).

Both have no time, u or z cutoff. Combined with previous exact source 559/4096 and Agent 8 z=2 mod8, z=7 mod16 and z=24 mod32, the [lossless original blank-halting equivalence](LowM67All1551Criterion.lean), accepted [CI 45275168303](https://github.com/FlareZ123/bb6/actions/runs/45275168303), excludes **1551/4096 distinct formal z-residue classes** from this particular low stopping ray. The high-stop family and all surviving low cases remain unbounded and untouched. This is **NOT** a fraction of halting six-state machines resolved; it is an exact infinite parameter-index exclusion.

A separate **second-generation 2-adic mass relation** follows the unique even-z predecessor one source layer further. It uses `s=z/2` and `u+12s+1=2^(2048s+129)` and the exact identity
`2*((173u+24)+(339u+47)/2+1)+12*(685s+49)=685*2^(2048s+129)`.
The all-exponent equivalence
`2^(n+2) | 2*(173u+25+(339u+47)/2) ↔ 2^n | 3*(685s+49)`
is now kernel-accepted in [CI 45277270250](https://github.com/FlareZ123/bb6/actions/runs/45277270250). The second-generation strict non-power gap, which excludes the exceptional pure-power source branch uniformly, is kernel-accepted in [CI 45277766006](https://github.com/FlareZ123/bb6/actions/runs/45277766006).

For `z` divisible by four, [EvenOddLowStopQuarterTwoForced.lean](EvenOddLowStopQuarterTwoForced.lean) composes two exact source-forced ancestors; its selective CI passed in [45287391182](https://github.com/FlareZ123/bb6/actions/runs/45287391182). This is still a reduction, not a root exclusion.

A further second-generation theorem is being developed in [EvenOddLowStopSecondFanSource.lean](EvenOddLowStopSecondFanSource.lean) and [EvenOddLowStopSecondFanReach.lean](EvenOddLowStopSecondFanReach.lean). Its intended exact source-parent iff says that the odd/even target `P=(173u+24,(339u+47)/2)` has its direct affine parent plus only odd-depth high-bounce parents, with every such depth satisfying `2^n | 3*(685s+49)`. For `s=4r+3` with odd `r`, the divisor bound forces every high-bounce parent to depth `n=1`, giving an exact two-candidate root-reachability decomposition. **This further fan is not yet kernel-accepted.** Its first combined CI run was interrupted by a GitHub runner shutdown while compiling the new module (not a Lean diagnostic); source and reachability files have since been split for targeted verification. Do not present these new theorems as certified until the split CI jobs pass.
