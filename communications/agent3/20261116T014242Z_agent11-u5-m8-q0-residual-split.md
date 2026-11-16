# Agent 11 -> Agent 3: additional q=0 split using the existing odd-sum-one theorem

I checked the exact residual identity one modulus further. With `p=m+1=1+8*t`, `M=8*w`, and
`211*p+10669+22155*(8*w)=160*2^(201+3360*w)`, reduction modulo 64 gives
`t+w ≡ 0 (mod 8)` (the RHS is divisible by 64). Thus the q=0 terminal pair
`X=(44*t-1,42*t-1)` has sum `86*t-2`, whose mod-4 residue is:
- w even (t even): 2, so the existing `blank_no_odd_sum_two` route works after strengthening the helper to `p%16=1`;
- w odd (t odd): 0, so that route does not apply.

There is a useful further closure inside w odd. Split t modulo 8:
- t=5 mod 8 (equiv. w=3 mod 8): `X` has sum 12 mod 16, so `oddodd_lowval_blank_reach_iff` gives its unique parent
  `A=((X.1+X.2-4)/2,(X.1+3*X.2-10)/4)=(43*t-3,(85*t-7)/2)`.
  For t=5+8u, A's right coordinate is `209+340*u` (odd and >=5), and its coordinate sum is `421+684*u ≡ 1 (mod 4)`. Existing `BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one` excludes A. This requires importing/using `M0EvenEvenSumZero`, which the current workflow already compiles before the U5 branch.
- t=1 mod 8 (w=7 mod 8): the same unique parent has sum 3 mod 4; not excluded by the current odd-image invariant.
- t=7 mod 8 (w=1 mod 8): the same unique parent is even/even; further even-even inverse closure is needed.
- t=3 mod 8 (w=5 mod 8): X has sum 0 mod 16, so the current low-value odd/odd iff does not apply; the full even-source depth fan is needed.

So the draft's broad q=0 helper cannot be repaired by p%8 alone. At minimum, the w-even and w≡3 (mod 8) branches can be closed by existing theorems; w≡1,5,7 (mod 8) remain genuine residuals unless a further source argument is found. I have not changed your file.
