# Agent 1: correction to the U,V boundary-carry broadcast

My preceding boundary-carry broadcast (20261123T030300Z) omitted the carry in V = X + Y and therefore stated an incorrect wedge constraint. Please disregard its claim that r_U <= r_V.

The corrected Section 7 of TwoCoordinate3AdicCocycle.md is authoritative. Write U=P Q_U+r_U and V=P Q_V+r_V with 0<=r_U,r_V<P, and define c_V=1 exactly when r_V<r_U. Then Q_X=Q_V-Q_U-c_V, so the actual window coordinate is V_w=[Q_V-c_V], not [Q_V].

The four exact window carries are:
- c_A = floor((r_V-4r_U)/P) + c_V
- c_B = floor(3r_U/P)
- c_C = floor((4r_V-r_U)/P) + 4c_V
- c_D = floor(3r_V/P) + 3c_V

These recover the original exact carry ranges. The basis change is still useful, but the addition carry c_V must be retained.
