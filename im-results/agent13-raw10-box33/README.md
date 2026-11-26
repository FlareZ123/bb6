# Raw10 rectangle 33, D0=2, B1=13: symbolic hard leaves

The two most resistant machines in this branch admit explicit nonhalting return maps.

- [8,20,11,13,1,13,2,23,4,0,2,21] (E1 halt): at a root A scanning 0 with blank left, the right stream is one free bit followed by base-four digits in {0,1,2}, least significant first. Root bit 0 becomes 1 in four moves. Root bit 1 initiates a scan over trailing digit-1 pairs; each is replaced by two ones. The first 0 or 2 leads to a clearing F sweep and returns to an allowed digit word. A finite word always has an implicit zero digit, so this is productive for every root. Box33BinaryCounter.lean proves this by list induction and strong induction on hypothetical halt time.
- [8,24,11,13,1,13,2,23,0,10,4,20] (E0 halt): after 33 moves, E scans a one with five ones to the left and zero to the right. Define R(m,r) as E with m ones on the left, scanned 1, r ones on the right; L(m,r) as R except for a single 0 between the scanned 1 and the right ones. The exact rules are R(m,r+5) → R(m+5,r) in 11 moves, R(m,0)=L(m,0), R(m,2) → L(m+2,1) in 14, L(m+2,r) → L(m+1,r+1) in 7, and L(1,r+2) → R(5,r) in 11. Consequently R(5,5k) → R(5,5k+2) → R(5,5(k+1)) forever. Box33UnarySweeper.lean proves all rules and the resulting nonhalting theorem.

Both files compiled in local Lean 4.36.0-rc2 using the exact C9Pair relative stream definitions (extracted from the existing conjugacy module); axioms propext and Quot.sound only. The canonical source projection and full branch coverage are separate next steps. No global bound is asserted.
