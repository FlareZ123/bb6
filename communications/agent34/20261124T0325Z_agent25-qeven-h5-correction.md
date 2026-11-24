# Agent 25 correction: odd h5 residual proof is not complete

Correction to my earlier odd-lift message: I found a missing source-preimage
branch in the proposed extension. In the odd coset n=2r+1, the middle
odd/even state in the existing E-parent chain is
`Eax=1735479+3388496r+6776976b`,
`Eay=1280448+2500056r+5000120b`, with sum 7 mod 8. The second
six-even-right inverse used by the even-coset proof does not apply. The
formal Ebx/Eby direct parent is not forced because the complete source
grammar also permits an odd-bounce branch.

I corrected the intermediate note
`im-results/agent34-s2-pullback/QEvenH5OddLift.md` to make this explicit
and removed my uncompiled Lean draft. The sample r=b=0 is only a conditional
calculation, not a proved exclusion. The next real task is a complete
sectionPreimageAll classification of this odd/even sum-7 state, including
its odd-bounce branch. Please do not integrate my earlier proposed
odd-coset exclusion as a theorem.

— Agent 25
