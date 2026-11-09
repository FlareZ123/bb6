# New odd-right strict I₂ \ I₃ cone and high-stopping exclusion

**Agent 34, 9 November 2026.** Exact arithmetic of the **unchanged**
`BB6.Agent46.secNext` first-return section for Machine C. The underlying
source iff is `BB6.Agent46.section_preimage_all_iff` from
`SectionAllInverse.lean`. The result concerns one specific unresolved six-state
machine and **does not determine BB(6)**.

## Main theorems

For natural coordinates `x ≥ 8`, `y ≥ 256`, write `S=x+y`. Define

```
C(x,y) := S % 32 = 20 ∧ (S+34) % 128 = (2*y) % 128.
```

**Original-source image separation.** Every state of `C` has two consecutive
successful first-return ancestors from arbitrary sources, and **none has three**:
`C ⊆ I₂ \ I₃`. Every such target is absent at **all** finite section times
from the true blank-derived seed `(5,1)`. The cone is entirely odd-right and
has natural density **1/2048** in expanding square grids.

**New high stopping family.** Every high-family stopping candidate specified by

```
m % 8 = 7
(j+m+14) % 128 = 0
k+j+3*m+5 = 2^(2*m+2)*(j+3)
target = (2*j+3,k)
```

is absent from the blank-derived original section orbit for all section times.
This removes an infinite, **1/1024-density** lattice of high stopping
parameters from the halting condition. The theorem is universal in `j,m,k`;
no bounded-time simulation or finite exponent cutoff is used.

The congruence-lattice density counts parameters, not density among machines.

## Exact inverse proof

For `C(x,y)` the exhaustive original-source predecessor grammar forces the
**sole immediate ancestor** `(a,k)` to obey

```
2*a+4 = S,
2*k+a+7 = S+y,
a % 16 = 8,
k % 16 = 0,
(a+k) % 32 = 24.
```

The original section actually returns the target from this source: take
`a=(S-4)/2`, `k=(S+y-a-7)/2`, and select depth-zero even-source bounce.
For `x≥8,y≥256`, these counters are ≥128, satisfy the high-input guard,
and the source equality follows from the complete `secNext` grammar.

Every immediate ancestor `(b,l)` of that forced first ancestor satisfies
`l≥5`, `l%2=1`, and `(b+l)%4=1`. The source grammar permits the direct
ancestor `(a+k-2,(k-2)/2)` and the single depth-one even-source high ancestor.
The source-exact proof excludes every other branch, including exceptional
sources `b=0,1` and all high depths ≥2; no inverse-depth bound is assumed.
Both possible second ancestors have the stated bad odd-right residue.
The already kernel-certified `BB6.Agent3.section_odd_image` theorem says that
an actual output with odd right counter ≥5 has sum residue 0 or 3 modulo 4.
Consequently neither second ancestor can itself have an incoming edge.

Existence of a two-edge chain follows by taking the actual direct ancestor
of the high-bounce first ancestor, whose right coordinate is even ≥128.
Initial real blank-section states are `(5,1)`, `(3,4)`, `(4,7)`; the
cone has `y≥256`. All later times have three source edges and are forbidden.

## Pullback to the stopping equation

Since `m%8=7`, we have `m≥7`, and `2^(2*m+2)` is divisible by 128.
The stopping equation yields
`k+j+3*m+5 ≡ 0 (mod 128)`. Thus

```
S = 2*j+3+k ≡ j-3*m-2  (mod 128),
S+34-2*k ≡ 3*(j+m+14) (mod 128).
```

The parameter conditions make `S≡20(mod32)` and
`S+34≡2*k(mod128)`. Simple exponential domination gives
`2*j+3≥8`, `k≥256`, so the cone's hypotheses hold.

## Independence from the earlier integrated parameter restrictions

The established earlier exact-root parameter predicate is
`BB6.Agent3ValSix.highAllowedValSixFull` in
`im-results/agent3-c-bounce-inverse/ValSixJointFull.lean`. On the entire
new lattice, the parameter conditions give

```
m%8=7, j%8=3, (j+m)%128=114, (2*j+3)%8=1.
```

All fixed modular exclusions in that predicate are false: in particular the
dyadic-depth prior exception requires first coordinate residue 3 or 7 mod8,
the Agent11 sum filter requires `j+m≡0(mod4)`, and the other listed branches
require incompatible `j,m` residues. The actual stopping counter is odd
because `j+m` is even, hence `affineNormalize` immediately stops and its
right coordinate is `k≥256`, never 4. Therefore **the entire lattice
satisfies the earlier named `highAllowedValSixFull` parameter predicate**
by direct arithmetic of its definition. The comparison is a mathematical
analysis of the earlier *parameter filter*; it does not claim the lattice
contains a genuinely reachable halting target.

A concrete previously-admissible pair is `j=107,m=7`, with

```
target (217, 7208827)
```

The exact published predicate was independently evaluated with a direct
integer implementation covering its full defining conjunctions and
the dynamic `affineNormalize` call. All 16 residue branches
`m%128∈{7,15,...,127}` and `j%128=(-m-14)%128` passed the prior predicate.
The new entire-family admission fact has **not separately been Lean checked**
against that historical predicate graph.

## Formal and computational evidence

- [`OddThreeArithmetic.lean`](OddThreeArithmetic.lean) is fully locally
  kernel-checked with Lean 4.36.0-rc2, without `sorry`, for the universal
  branch classification and two-edge construction. The grammar `P` has
  literally the same definition as original `sectionPreimageAll`.
- [`OddThreeSource.lean`](OddThreeSource.lean) transfers both directions
  of `P` through the authentic `section_preimage_all_iff`, establishes
  the all-source three-link impossibility, the full-time authentic blank
  exclusion, and the high stopping pullback. The earlier **narrower**
  `S%128=84,y%64=59`, `m%32=7,(j+42)%128=(3m)%128` form passed
  [original-source GitHub Actions CI 42570604194](https://github.com/FlareZ123/bb6/actions/runs/42570604194),
  with the same source modules. The generalized fourfold stronger version's
  arithmetic and high stopping lemmas also compiled locally. Its CI
  source integration has been temporarily obstructed by **GitHub's HTTP 504
  when fetching elan**, in runs 42571167740 and 42571283706, before any
  research code was executed. Until a successful generalized source run,
  **do not describe the stronger version as CI-verified**.
- [`check_odd_high_novelty.py`](check_odd_high_novelty.py) is an independent
  exact-integer implementation of earlier named parameter predicates.
  It is diagnostic evidence, not a machine source proof.

## Research significance and limits

This cone has **odd** right counter and begins two sections before its missing
third predecessor. It is disjoint from Agent 34's earlier **even-right**
four-cell source-certified strict `I₂\I₃` cone, and from Agent 11's
even-right all-depth tower for `n≥1`. The exact global `I₃` density was
independently derived by Agent 45; this result supplies an explicit original
source-checked high-halting gate pullback that the global density alone does
not isolate.

The remaining authentic halting parameters are still unbounded and BB(6)
remains open. The next mathematical step is to force all **surviving** stopping
rays into a missing ancestral image, or to construct a globally valid
blank-origin invariant strong enough to close the existential parameter gap.
