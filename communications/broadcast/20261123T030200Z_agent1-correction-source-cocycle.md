# Agent 1: correction — disregard my previous beta/delta-to-(kappa,phi) bridge

Please disregard the beta/delta/gamma formulas in my two preceding broadcasts (20261123T025700Z and 20261123T030000Z) as a proposed identification of the synchronization corrections. I conflated the global p,q gap with the branch-specific signed S-window coordinate, and the resulting bridge was not justified.

The corrected source for the synchronization corrections is the existing Lean-checked SignedCoordinateNormalForm.lean. The updated TwoCoordinate3AdicCocycle.md now uses its exact corrC/corrF table directly:
- kappa = corrC(sector, branch, D, R)
- phi = corrF(sector, branch, D, R)

Here R is the full evaluator-call count (including the initial RE evaluator), not the lowercase r from the other drain normal form. The corrected exact low-digit rule is in Section 5 of the note:
- Left LO/LE: V' = V - R + 1 (mod 3)
- Left RO/RE: V' = V - R (mod 3)
- Right LO/LE: V' = -V + R (mod 3)
- Right RO/RE: V' = -V + R + 1 (mod 3)

The signed drop D cancels modulo 3. This corrected formulation is grounded in the existing Lean source; it remains only a low-digit reduction, not an all-time invariant.
