# Residual 10338: linear growth and universal nonhalting

**Status:** paper-level proof; source-connected Lean certificate drafted separately, not yet accepted.

Table: `[7,21,11,1,14,24,3,16,20,11,15,20]`, sole unassigned slot C1. The transition alphabet is the usual 4q+2w+r. All statements concern the exact partial table and therefore every completion that agrees with it.

Define section S(n,h) to have state F, head h, ones at exactly h+3 through h+n+2 inclusive and zero everywhere else. For every positive odd n, the following exact run holds:

    S(n,h) -> S(n+8,h-5) in 5n+68 ordinary moves.

It suffices to prove at h=0, by translation. Below every cell outside the listed intervals is zero. All endpoints are inclusive.

1. The four transitions F0 D0 A0 B1 produce A at cell 4, with ones at 0..2 and 4..n+2. The latter run has even length n-1. On each successive pair of ones the four transitions A1 F1 F0 D0 restore both cells and advance A two positions. After (n-1)/2 such repetitions, A is at n+3, reading 0. This costs 4+2(n-1) moves.
2. A0 B0 C0 D1 gives E at n+3, with ones 0..2, 4..n+3 and n+5. Cell n+4 is zero. Whenever E is at p on 1 with cell p+1 zero, the three transitions E1 C0 D1 write 1 at p+1, erase p, and place E at p-1. Repeating exactly n times reaches E at cell 3, reading 0, with ones 0..2 and 5..n+5.
3. E0 F1 F1 F1 gives F at cell -1 with ones 5..n+5. Thus the first three phases cost 5n+10 moves.
4. The following fixed word of 16 ordinary transitions (head range -2..3) gives F at -3 with ones 0..3 and 5..n+5:

       F0 D0 A0 B0 C0 D1 E1 C0 D1 E1 C0 D1 E1 C0 D1 E0

5. The following fixed word of 42 ordinary transitions (head range -4..5) gives F at -5 with ones -2..n+5:

       F0 D0 A0 B1 A1 F1 F0 D0 A1 F0 D1 E1 C0 D1 E0 F1 F1
       F0 D0 A0 B0 C0 D1 E1 C0 D1 E1 C0 D1 E1 C0 D1 E1 C0 D1
       E1 C0 D1 E1 C0 D1 E0

   The 16- and 42-move words are independent of n: they consult no cell above 5, and cell 5 is a 1 for every admissible n. Their transition words can be checked directly from the displayed table.

The final interval -2..n+5 contains n+8 ones, hence S(n+8,-5). The total is 5n+10+16+42 = 5n+68. No phase queries C1.

The authentic blank execution reaches S(123,-98) at step 6120: F at -98, ones exactly -95..27. A direct finite replay checks the initial prefix and section endpoints. Since 123 is positive and odd, applying the recurrence k times gives S(123+8k,-98-5k), with the accumulated step count 6120 + 683k + 20k(k-1). These times are unbounded, proving that no completion can halt. 
