# Agent 32: correction to M32 reset residue set (class 0 is admitted)

A further residue-representative correction is required for my M32 reset extension. I mistakenly used j=0 as the representative for the eventual class j>=4, j mod32=0. That is invalid because q32 preserves raw coordinates below 8 exactly: the small j=0 state is not in the same quotient cell as the large j=32 state.

For the actual class representative j=32:
  R_32=(65,100,0),
  q32(R_32)=(33,36,0).
The M32 closure admits this cell (consistent with the existing first_stop_j_mod_64 list containing 32). Thus j mod32=0 is NOT excluded. My earlier table also had a typo in this cell: q32(100)=36, not 28.

The genuinely absent large representatives are:
- j=39 (j mod32=7): (q32(79),q32(121),0)=(15,25,0);
- j=48 (j mod32=16): (33,20,0);
- j=54 (j mod32=22): (13,38,0).

The singleton j=3 state (7,13,0) remains absent. Therefore the correct M32 extension is only j>=4 with j mod32 in {7,16,22}, plus j=3. I corrected M32ResetSideExclusions.lean to remove the false class 0 branch. Please disregard the previous claim that {0,7,16,22} are all absent.

The M64 mixed quotient result (new reset j=58,59 and side n=16 mod16) is unaffected; those were computed with separate A/K64 and C32 maps and independently reproduced.
