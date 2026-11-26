# E0=1RF normalized Raw139 — resolved difficult descendants

Parent codes `[7,24,11,24,14,24,24,16,23,11,24,24]`. The preliminary exhaustive candidate partition has 35,274 splits and 811,303 ordinary leaves: 592,619 cycles, 139,691 last-hole queries, 73,278 FAR, and 5,715 open leaves. Extended search classifies 5,602 as block-FAR, 95 as late queries, 17 as cycles and one as a hard nonhalting leaf. Seven multi-hole late queries (122, 1271, 2528, 2682, 2714, 4563, 5109) expand to 168 children, including 123 block-FAR, 40 last-hole and three cycle certificates; two require special proofs. The largest finite query is 6,018, giving candidate bound 6,024. This remains a candidate partition until the complete source-connected weighted Cover is accepted.

## Residual 4563/5: two-parameter recurrence (new exact proof)

Table `[7,17,11,5,14,8,24,16,23,11,3,17]`, D0 free. Write E-section left words nearest-first excluding the scanned cell, right words nearest-first including it. Concatenation denotes adjacent words. Define

- P by signed run lengths (-1,2,-1,2,-1,2,-2,3,-1,7,-1,2,-5,3);
- M0 by (-1,1,-1,4,-1,6,-2,3);
- M1 by (-1,7,-1,4,-1,6,-2,3), where negative run lengths denote zeros;
- U = M1 M0^5, Q = 01111101111, K = 0111111;
- C(x,y) = E(P M0 U^x M1 M0^6 Q K^y, blank).

For every x,y >= 0, the exact primitive recurrence is

    C(x,y) --> C(x+1,y+553)
    steps = 24481769 + 1294020*x + 79632*y.

The authentic blank-start seed reaches C(0,619) at primitive step 28,792,194. Iterating the recurrence yields C(k,619+553*k) for all k >= 0; each finite run avoids D0, so every compatible completion is nonhalting.

[verify4563.py](verify4563.py) executes the seed using independent primitive steps and verifies the recurrence using exact symbolic prefix rewrites with arbitrary nonnegative repetition markers. A guarded block transfer consumes a known word W on one side, adds V on the other and restores the fixed prefixes, without reading beyond either finite prefix. Induction permits simultaneous transfer of W^n into V^n. Word rotations move fixed matching words across a repetition marker by the exact identity (ab)^n a = a(ba)^n. The final word identity, affine cost and all 19 distinct guarded loops are checked. The recurrence is a finite reproducible symbolic proof, not a finite orbit extrapolation. The original proof passed execution.

[E4563Macros.lean](E4563Macros.lean) establishes the eight exact E-section rewrites, 29-step and 19-step basic sweep rules and the four-step blank seed directly in the existing semantics. Local Lean 4.36.0-rc2 compiled these lemmas using only standard axioms. The full symbolic checker is not yet kernel-formalized.

## Other exceptional leaves

- 4868: `[7,19,11,9,14,5,12,16,23,11,3,24]`. [OneRF4868.lean](OneRF4868.lean) proves the exact 827-step pump with 37-cell growth, seed 953.
- 1271/5: `[7,12,11,23,14,5,2,16,23,11,1,24]`. Width-21, 13,603-state sparse n-gram invariant. [emit1271.py](emit1271.py) generates twelve independent row checks. All rows and `BB6.Agent6E0OneRF1271_5.never` passed local Lean 4.36.0-rc2 with only [propext, Classical.choice, Quot.sound], using exact previously accepted dependency objects (oneRE core 15130259578 and Raw111 sparse 15001870656). Largest row 2360 abstract states; largest observed peak memory about 3.59 GB. The complete source-connected audit remains separate.

The hardest previously unclassified descendant 4563/5 is mathematically resolved. The remaining obligations are coherent source-closure acceptance for 1271/5, full symbolic proof checking for 4563/5, and assembly of all branch certificates. The existing manual E0 workflow now has `oneRFProof` mode for the two exceptional leaves only. It generates the exact symbolic trace with `generate4563.py` and `generate4563_conclusion.py`, uses `split4563.py` to share one rule base across independent trace cuts, and uses `merge4563.py` to check exact module identities before the final blank-root theorem. It does not start a duplicate ordinary-leaf census. No universal upper bound or global residual-count reduction is claimed.
