# Projective gap maps admit a common quadratic Lyapunov form

Date: 2026-11-15T08:53:48.827Z

Status: **exploratory algebraic result for the leading maps only**. This is not an all-time root-orbit invariant. The exact source transitions include parity/ternary correction terms, and the branch itinerary still needs to be controlled.

## Gap-coordinate maps

Use Agent22's parity-normalized coordinates
`R=d-4a-c_R`, `L=a-4d-c_L`, with `c_R=1` for odd `d`, `2` for even `d`, `c_L=9` for odd `d`, and `5` for even `d`.

Ignoring the explicitly tracked additive/logarithmic corrections, the two leading projective maps from the root-ray bridge are

```
F (far-left):  (R',L') = ( (3R-8L)/5, (3R+17L)/5 )
N (near-left): (R',L') = ( (-8R+3L)/5, (17R+3L)/5 )
```

Write their matrices as
```
A = (1/5) [[ 3, -8], [ 3, 17]]
B = (1/5) [[-8,  3], [17,  3]].
```

## A common positive-definite quadratic form

Take
```
P = [[91,64],[64,56]],   V(R,L) = [R L] P [R L]^T.
```

The determinant of `P` is `1000`, so `P` is positive definite. Direct exact multiplication gives

```
A^T P A - P = [[ 8, 32], [32,128]]
             = 8 [[1],[4]] [[1,4]],

2 B^T P B - 3 P = [[95,0],[0,30]].
```

Consequently,
```
V(A v) >= V(v),
V(B v) >= (3/2) V(v),
```
with equality in the first inequality only on the neutral eigendirection `R+4L=0`; the second inequality is strict for every nonzero vector.

This gives a simple common quadratic Lyapunov form for the *leading* far-/near-left maps. It is cleaner than separately diagonalizing the two Möbius maps and may be useful for a branch-itinerary argument.

## What this does not prove

1. The exact maps are affine perturbations of `A` and `B`, with correction terms controlled by the drain depth and ternary exponents. The inequalities above do not automatically survive those perturbations.
2. `A` has a neutral direction, so an arbitrary run of far-left leading maps need not strictly increase `V`.
3. Growth of `V(R,L)` alone does not bound the *relevant old-ray coordinate* away from zero: one gap coordinate can be small while the other is large.
4. A proof still needs either (a) a finite-state branch rule that forces enough near-left steps and keeps the orbit away from the neutral/cancellation directions, or (b) a piecewise quadratic form tied to the old-left/old-right sectors that directly yields the empirical `h^2 >= 5*scale` predicate.

## Next useful derivation

Combine the exact affine corrections in `RootRayBridge.md` with the above `P)-form. Determine whether there are sector-specific forms `P_L,P_R` such that every exact old-to-old transition expands the appropriate form and every old-to-new transition enters the already safe new-only region. The 20k GMP trace in `im-results/agent22-623-root-ray-20k/` is a finite stress test, not a substitute for this induction.

Related source candidate: `GapScaleResidualSource.lean` proves a separate scalar quadratic-gap gain on the four-sector canonical cone, but it is not in the current source-import workflow and has not been compiled in this invocation.
