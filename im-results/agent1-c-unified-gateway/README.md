# Machine C unified affine stopping rays (Agent 1, 2026-11-04)

**Status:** Source-checked Lean intermediate result, no claim of Machine C nonhalting or exact BB(6). The normalization reexpresses Agent15's already complete two-family stopping classification. The simple new joint residue filter is a corollary of Agent38's pre-existing genuine blank-orbit image obstruction; its independent novelty and relation to other filters have **not** been established.

## Scope and exact equation

Use the unmodified `BB6.Agent46.secNext` two-counter first-return map (original accelerator input `(5,1)`). Agent15's exact source stopping classification gives the exceptional `(0,0)` case, an `a=1` dyadic family, and an `a=2*j+3` dyadic family.

Both nonzero families are **exactly one unified family**, with natural parameters `u,m`:

```
a = 2*u+1
k+u+3*m+4 = 4^(m+1)*(u+2)
```

Equivalently, positive odd `a` and
```
a+2*k+6*m+7 = 4^(m+1)*(a+3).
```
For fixed `m`, this is a single affine ray `k=(4^(m+1)-1)*u+2*4^(m+1)-3*m-4`, so the two prior stopping families are the `u=0` and `u>=1` sectors. The source theorem `source_section_halts_iff_one_equation` preserves the exceptional `(0,0)` input. The true blank section never reaches `(0,0)`, by the earlier source-certified Agent38 right-counter positivity theorem.

## Shared all-time filter

At a candidate gate, if `(u+m)%4=1`, arithmetic forces both `k%2=1` and `(2*u+1+k)%4=2`. Agent38's original `blank_section_mod4` theorem says that a genuine blank-origin section state with these two properties must be the initial `(5,1)`, which is not a stopping input. Thus **every** such gate is absent from the true blank orbit, for all natural `u,m`, with no finite step cutoff.

As prior-family arithmetic this simultaneously excludes the first-family `m%4=1` and the high-family `(j+m)%4=0` when `u=j+1`. Other source-proved filters could subsume portions or all of these restrictions; no exclusive novelty is claimed.

Lean source theorem `source_blank_halts_iff_affine_rays` establishes the exact remaining blank stopping criterion:

```
RunHalts iff there exist time,u,k,m such that
  run secNext time (some (5,1)) = some (2*u+1,k)
  and k+u+3*m+4 = 4^(m+1)*(u+2)
  and (u+m)%4 != 1.
```

Every positive-first-counter immediate stopping input also has **`k%3=1`**, a direct corollary of the same source classification, proved as `source_positive_stopping_right_mod3`. This fact does not show that a genuine blank orbit cannot reach a stopping input. Simple finite samples show that odd-first-counter states with `k%3=1` are common, so a standalone mod-3 exclusion cannot decide the machine.

## Verification and files

- [UnifiedArithmetic.lean](UnifiedArithmetic.lean) contains complete arithmetic iff, base-four identity, affine reparameterization, odd-right residue theorem and mod-three necessity.
- [UnifiedGateway.lean](UnifiedGateway.lean) imports the unchanged Agent15 `BlankParam` and Agent38 source bridge, proves the fully source-connected exact stopping iff, all-time residue restriction and filtered affine-ray iff.
- [Manual-only GitHub Actions workflow](../../.github/workflows/agent1-c-unified-gateway.yml) reconstructs the original checked-in repository `CLine`, source bridge, Agent46 section map, Agent38 mod-four proof and Agent15 stopping classification prior to compiling both new sources. No per-commit trigger.
- Original-source [CI 41778082311](https://github.com/FlareZ123/bb6/actions/runs/41778082311) **succeeded** for the initial unification, [CI 41778447511](https://github.com/FlareZ123/bb6/actions/runs/41778447511) **succeeded** for the common residue filter, and [CI 41778935482](https://github.com/FlareZ123/bb6/actions/runs/41778935482) **succeeded** including affine ray parameterization and mod-three theorem. Pure arithmetic local Lean 4.36.0-rc2 checks reported only standard `propext`, `Quot.sound`, and occasional `Classical.choice`; source output includes explicit `#print axioms`.

## Mathematical boundary and next useful question

These results reorganize existing halting obligations and source-certified reachability restrictions into one parameter space. They do not eliminate all gates, improve a global BB(6) bound, or prove that Machine C never halts. Surviving `(u+m)%4` classes are `0,2,3`; each still contains infinitely many affine gates.

Before extending, compare exact overlap with Agent15's affine normalization, Agent11's low/high all-depth families, Agent3's odd-section inverse grammar, and Agent29/46's latest residue certificates. A potentially useful next step is a backward-closed invariant or lossless inverse grammar in the unified `u,m` coordinates that rules out a **surviving complete infinite subfamily** of both former halting branches, rather than adding isolated modulus instances.
