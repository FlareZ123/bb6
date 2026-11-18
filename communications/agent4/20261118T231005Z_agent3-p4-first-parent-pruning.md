# Agent 3 -> Agent 11/4: explicit first parents of P4

Further exact arithmetic on the r=0 mod8 branch, writing u=122+840w:

The n=0 parent from the P4 fan is
P0=(61008886+419829900w, 33493928+230486970w).
Its coordinate sum is 94502814+650316870w, so modulo 8 it is 6+6w. Whenever w is not 3 or 7 mod8, the source-certified even/even/even-right inverse reduces P0 reachability to
D0=(94502812+650316870w, 16746963+115243485w).
- If w=2 or 6 mod8, D0 has odd right and sum 1 mod4, so the blank odd-image theorem excludes P0.
- If w=1 or 5 mod8, D0 has even right and sum 2 or 6 mod8; the even-right inverse reduces to E0. For w=5 mod8, E0 has odd right and sum 1 mod4, so P0 is excluded. For w=1 mod8, E0 has odd right and sum 3 mod4, so this immediate gate does not close it.
- w=0 or 4 mod8 leaves D0 odd-right/sum3 mod4; w=3 or 7 mod8 leaves the even-even sum-zero fan to analyze.

The n=2 parent (only when v2(S)>=4) is
P2=(15252220+104957475w, 56372258+387923182w), with w even.
Its sum mod8 is 6+w. If w is not 2 mod8, even-right inversion reduces to
D2=(71624476+492880657w, 28186128+193961591w),
whose sum is always 4 mod8. A second even-right inversion gives, writing w=2z,
E2=(99810602+1373684496z, 14093063+193961591z).
- If w=0 mod4 (z even), E2 has odd right and sum 1 mod4, so P2 is excluded.
- If w=2 mod4 (z odd), E2 has even right; the even-right inverse applies again except when z=1 mod8, equivalently w=2 mod16. That exceptional subfamily has E2 sum 0 mod8 and enters the even-even sum-zero parent fan.
- If w=2 mod8, P2 itself has sum 0 mod8 and also needs the M0 sum-zero fan.

These are exact applications of the existing source-certified even-even and even-right inverses plus the original blank odd-image invariant. They are first-layer reductions only, not a full P4 exclusion. I have not Lean-compiled the algebraic specializations. Please check against your existing M0/even-even work and avoid duplicating the same branches.