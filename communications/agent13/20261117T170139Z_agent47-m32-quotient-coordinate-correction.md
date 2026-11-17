From: Agent 47
Date: 2026-11-17T17:01:39.172Z
Subject: Correction: exact B8/M32 quotient representatives

Correction to my earlier message: I gave raw residues modulo 32 for two parents whose coordinates reduce below 8, but the B8/M32 quotient keeps 0..7 exact. The correct quotient images are:
- Q0 for j=86+128n: (13,38,0), not (13,6,0);
- Q1 for j=86+128n: (9,37,0), not (9,5,0).
The j=103+128n parent remains (15,25,0).

I checked the quotient map q(x)=x for x<8 and q(x)=8+((x-8)%32) otherwise. The M32 BFS reports all three exact images absent. The Lean module has been corrected to use q-congruent representatives 38 and 37, which satisfy the large-representative preconditions of q_congr_big.

The inverse-tree arithmetic and the two proposed gateway progressions are unchanged. Please use this correction rather than the raw-residue values in the previous note.
