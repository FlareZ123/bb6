# Direct digit inversion of the #623 positive-budget drain image

Theorem file: [DrainImageDecoder.lean](DrainImageDecoder.lean). Status: independently kernel-checked with Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a); printed axioms only propext, Classical.choice, Quot.sound. The module assumes the four exact excess laws used by Agent49. Original-source adapter is the next step.

## Result

For E(0)=0, E(3q)=E(q-1) (q>0), E(3q+1)=4+E(q), E(3q+2)=2+E(q+1), define F(b)=3b+E(b). The executable inverse satisfies, for all y,b in Nat,

    inverse y = some b  iff  F(b)=y.
    inverse y = none    iff  forall b, F(b)!=y.

This gives a direct most-significant-digit inverse with no candidate scanning or binary search on the block counter. The exact residual path is encoded by a ternary word of length k, with digits 2-r for residue r of each visited block. Writing U for that word, T=(3^k-1)/2, and c for the digit charge (#1 minus #2), the identities are b=2U-T, E=2k+2c, F=2(3U+c)-3T+2k. Nonzero words have nonzero leading digit. The three leading-digit intervals of 3U+c are disjoint; the decoder removes a digit and divides the place value by three. The output itself fixes k by parity and the strictly separated length bands. The band search uses a linear number of repunit updates in the bit length of y.

Two global image restrictions follow:
* F(b+2)>=F(b)+2, with equality **iff** b mod 3=1. Therefore among any y,y+2,y+4 at least one is absent from the image.
* For every k>=0 and 1<=j<=k+5, F never equals 9*T(k)+2*j. This follows from the bound F<=9*T(k) for length k, and F>=9*T(k-2)+2*k+8 for length k>=2, with k and F of equal parity.

These are quantified statements, not extrapolations of finite scans. The proof builds on Agent49's correction growth and strengthens the parity-specific image monotonicity to exact minimum-gap classification. The existing near-power inverse is a special case of this general decoder.

## Relevance and limits

Agent49's inverse window proves y=z+F(b) for a successful original drain returning (x,y) with x>=2*(y.log2+1). In the large-first-coordinate sector, the two candidate shifts are z=2,3 if y is even and z=5,0 if odd. Missing both shifted images is a sufficient no-parent criterion, potentially excluding infinitely many entire vertical rays from the blank-root orbit. The source-specific gate and its consequences must be connected and checked against the pinned original machine before claiming that result. No halting-family exhaustion or BB6 upper bound follows yet.
