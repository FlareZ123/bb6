# Sign-free modular inverse cones for Machine C

Status: **abstract Lean kernel accepted locally**, Lean 4.36.0-rc2; source adapter written against exact current repository interfaces, not yet compiled against the full original-source dependency closure. This is an intermediate mathematical tool, not a proof of Machine C nonhalting or BB(6).

## Core idea

Agent13's negative-shadow approach requires both representatives to be positive magnitudes of small negative coordinates. Instead carry a single invariant on the actual right counter: y+2 >= 3*2^b at precision b. Residues may be arbitrary signed integers, including zero, and are reduced to canonical residues at each inverse step.

Direct inverse: a+2=x+y and 2*k+2=y, so 2*(k+2)=y+2. This propagates the invariant at precision b-1.

High inverse at depth n: Q=x+y+o=2^(n+1)*(a+2+o), o=(x+y)%2, and 2*k+a+7+3*n=x+2*y. Since x+y-a >= 2^(n+2) >= 3*n+4, we have 2*(k+2) >= y+1. Thus 2^(n+2)*(k+2) >= y+2, preserving the invariant at precision b-(n+2).

At b>=2 the invariant implies y>=8. If the modular valuation v is known (v+1<=b), the invariant also implies Q>2^v, excluding the exceptional pure-power branches in Agent13's source parent theorem. The all-depth fan is finite, with n+2<=v. Each recursive child consumes precision, preserving both modular correspondence and the size invariant. Every accepting leaf excludes an original-source odd-image forbidden residue. An empty parent fan is also validly rejecting. Failure to accept is inconclusive.

## Unified stopping families

Use j=0 for the low branch and j>=1 for high index j-1. The exact stopping equation is
```
y+j+3*m+4 = 2^(2*m+2)*(j+2),  x=2*j+1.
```
It implies y+2 >= 3*2^(2*m+1), or y+2 >= 3*2^(2*m+2) when j>=2. At any such precision b, the target is congruent to (2*j+1,-j-3*m-4). Thus one accepted residue certifies all congruent (j,m) with sufficient precision budget, **without j<=3*m+1** or any relative growth restriction.

Concrete kernel-checked example: b=5, j=10 (mod 32), m=2 (mod 32). For all u,v>=0, j=10+32*u and m=2+32*v, the stopping target is excluded under the complete source laws. Its canonical root (21,12) needs a direct inverse, then a high inverse of depth 0; this is not just an immediate odd-image check.

## Files and verification

- ModularCone.lean: fully compiled standalone locally, no sorry; the axiom audits of excluded_sound, stop_excluded, stop_cylinder_excluded, example_family are [propext, Quot.sound]. It is parameterized by ParentLaw and ForbiddenLaw.
- ModularConeSource.lean: thin original-source specialization using Agent13UnifiedShadow.source_parent_of_right_ge8, Agent13AffineCone.parent_equations, and Agent13TwoParent.odd_forbidden_image. Requires a source-closure build before marking the original-source theorem accepted.
- probe.py: memoized exploration of exactly the modular checker; Python counts are discovery evidence, not formal universal coverage.

At precision cap 32 (actual b=min(cap,2*m+1)): 883/1024 low parameter cases m=0..1023; 13451/16129 high cases j,m=1..127; 1916/2583 high cases outside j<=3*m+1. At cap 24: 846,12932,1876 respectively. Low unresolved m<100 at full precision: 0,2,6,8,10,15,16,27,47,82,91. No inference to unbounded coverage from these counts.

Next: use the reusable modular checker inside the existing source criterion with existing exact finite-root/mass methods, and investigate the remaining symbolic residues rather than expanding isolated affine certificates. Avoid a new redundant CI workflow; append the two files to an existing compatible source-closure workflow once practical.
