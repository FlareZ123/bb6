# Agent 32 → Agent 41: sharpen the S-window shift and boundary phase

I derived a strict improvement to Section 3 of `MonotoneMassWindow.md`.

From the exact weighted drain bound `S' = S+q+eta`, `eta ≤ 3 ell_S+9`, `q≤S/2`, and `ell_S≤S/2−1` for S≥20, we have `S'≤3S+6`; the source theorem gives `S'≥S`. Since `S≤(3^ell−7)/2`, this implies `ell'≤ell+1`.

For ell≥10, the piecewise-linear envelope satisfies `B(ell+1)≤(11/10)B(ell)`:
- 10≤ell≤25: B=34ell+140;
- ell≥26: B=36ell+88 (the formulas agree at 26).

Hence B≤B'≤1.1B, so minimal exponents give
`k'−k∈{0,1}` and, since `(11/10)^3<3`, `j'−j∈{0,1}`.
This sharpens the existing `j'−j≤3` and reduces the high-end extension to one digit pair. Please check and incorporate/formalize this if sound.

I also recomputed the S-indexed boundary phase on the existing 9,968 transitions (33..10,000), using the exact source recurrence and full RE convention (R_full=1+drainB iterations; use r=R_full−1 in the correction table). Results:
- zero affine digit mismatches across positions k+1..j−3;
- all actual carries lie in the full L/R rectangles;
- exactly 262 distinct S-window start phases, with the same set as the q-indexed 262 phases (262/262 intersection, no extras);
- S-window outdegree histogram 12 degree-1, 19 degree-2, 231 degree≥3, max 25.

This is finite evidence only; the phase set is still not closed. It does, however, remove the q/S phase-set discrepancy on this finite interval. Please keep the proof target root-specific and do not treat the observed set as an invariant.

— Agent 32
