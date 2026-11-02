# Agent 1: P1 quarter-class proof and all-depth dyadic inverse grammar

**Status 2026-11-02:** Genuine blank-entry P1 critical indices n≡2(mod64) for n≥66 and n≡50(mod64) have been universally excluded by Lean 4.36.0-rc2. The entire P1 machine and BB(6) remain undecided. See [the academic result and proof provenance](../../results/2026-11-02-p1-entire-2-and-50-mod64-exclusions.md).

## Source-checked all-natural theorem and reproduction

`QuarterFinal.lean`: `no_critical_q_mod_four` excludes `Reach 2 (14*2^(16q+2)-2*(16q+2)-10)` for every q≥1 with q%4=0 or3, using the original P1 map and Agent45's two-feeder iff. Eight complete finite inverse-cone proofs are stored in `QuarterCone.lean.xz.b64`, regenerated independently from `generate_quarter_cones.py`. Their exact source SHA256 is verified twice in the manual-only workflow `.github/workflows/agent1-p1-quarter.yml`. `QuarterGap.lean` proves the universal arithmetic power gap for every even-positive terminal leaf. The verified original-source CI is [41456577976](https://github.com/FlareZ123/bb6/actions/runs/41456577976); [41461096964](https://github.com/FlareZ123/bb6/actions/runs/41461096964) additionally includes the new structural inverse lemmas. Their final axiom reports include standard `propext`, `Classical.choice`, and `Quot.sound` only.

## New exact inverse relation as two equations

For `4≤b`, `b%4=0`, `d%2=1`, `InverseIff.lean` proves over **all** natural k,c:

```
GAncestor b d k c ↔
  ∃ t : Nat,
    d + b/2 + 3 = 2^t*(c+3) ∧
    2*k + c + 2*t + 1 + c%2 = b+d
```

Here `GAncestor` is the **unmodified** source inverse, not a heuristic guessed recurrence. `MassInverse.lean` establishes the mass equation directly by induction on Agent47's exhaustive `inverseAt`; `InverseIff.lean` composes it with the source-verified dyadic power equation, uniqueness of positive powers of two, and `inverseAt_complete`. It is a complete Diophantine representation for every predecessor under the stated parity hypotheses.

`OddConeMass.lean` defines `OddCone b0 d0 b d m` for arbitrarily long odd-right-target inverse chains with full source `inverseAt b d t=some(k,c)`, `c` odd, `k≥2`; the cumulative cost m increases by `t+1` per edge. It proves

```
b+d+2*m=b0+d0.
```

For Agent45's genuine necessary feeder roots L0=(4u-4,4u+9), L1=(6u-2,2u+5), starting sums are `8u+5` and `8u+3`. Define `s=d+b/2+3`. `OddConeCoordinates.lean` proves that `(s,m)` determine both original counters:

```
b + 2*s + 4*m = 2*(b0+d0)+6
d + (b0+d0)+6 = 2*s+2*m.
```

`OddShift.lean` proves the exact dyadic edge law, for inverse recursion depth t:

```
m' = m+t+1
2^(t+1)*(s'+m') = 2^t*((b0+d0)+7)+s.
```

All this is **kernel-checked original-source arithmetic** in [manual CI 41461096964](https://github.com/FlareZ123/bb6/actions/runs/41461096964), with standard axioms and no sorry. These are intermediate generalizations, not a P1 nonhalting proof; no arbitrary pair satisfying these equations is asserted blank-reachable.

## Remaining unbounded closure task

Known original-source reductions leave the infinite P1 critical sectors n≡2,14(mod16). Our new proof excludes q%4=0,3 within n=16q+2; **q%4=1,2** survive, alongside n≡14(mod16). Agent45's exact feeder equivalence requires both special families `u(q)=7*2^(16q)-4q-3` to be excluded from the actual blank orbit. Source-verified arbitrarily deep *synthetic* inverse paths defeat a global fixed-depth strategy.

The exact `(s,m)` grammar suggests investigating a parameter-aware forward barrier on `s+2*m`, equivalent to lower bounds on `b`; no such sufficient universal barrier is yet proved. It is crucial to test proposed restrictions against Agent4's real reachable (32,45) member of the unrestricted L0 line and Agent45's deep synthetic histories. No generic whole-line exclusion, new BB(6) bound, or decision is claimed.
