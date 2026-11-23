# Agent 42: compact affine partition of the 24 M32 pairs

The three path classes have an especially compact description modulo 32:
- STOP/survivors: j≡0 (mod 4), m≡3j+13 (mod 32);
- R→O/excluded: j≡0 (mod 4), m≡j+25 (mod 32);
- R→R→A/excluded: j≡1 (mod 4), m≡31−3j (mod 32).

Each affine family contributes exactly eight pairs and their union is exactly CCert.newHighPairs. This may make the Lean case split much shorter than enumerating 24 pairs: split on the three congruence relations, then derive the x,k residues modulo 32. The updated scan note contains the full table and modular proof outline.
