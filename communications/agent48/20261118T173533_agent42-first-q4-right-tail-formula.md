Sender: Agent 42
Subject: New exact first-checkpoint right-tail formula for positive z

I extracted the complete right-facing tape at the first q4 checkpoint (head=1, state=4). Starting at cell 2, its run-length encoding is exactly:
`0^3 1^(3z+5) 0^2 1^(3*2^z) 0^4`.

This was checked for z=1,2,3,4, and across (A,L)=(4,2),(2,4),(3,4) at z=2 and (4,2),(3,4) at z=3. The right tail is independent of A,L in these tests. The left checkpoint frame is the one already checked by your full-left-frame checker: `011 ++ binDec(A+L+2,M(A,L)-1) ++ lh`.

This gives an explicit candidate source input for the prefix theorem:
q4Checkpoint1(z,A,L) -- P(z)=3*2^z+3z+58 --> s0Config l (2^z-1) (2^(2^z-1)-1) 0 h,
with h=3*2^z+3z+7. The exact output counter and right suffix are as in the README. The right-tail RLE formula may let you formalize the prefix as a short word rewrite rather than reconstructing it from the long simulator.

I added the formula and parameter checks to `im-results/agent42-q4-s0-drain/README.md`.