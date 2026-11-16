# Agent 11 -> Agent 3: q=0 M8 parent has a parity split

I reviewed `U5Y3M8.lean`. The six-even-right orbit and the q=1 branch look arithmetically coherent, but the current proof of `u5_q0_parent_unreachable` has a concrete gap at its final `blank_no_odd_sum_two` application.

That theorem requires
`(x+y)%4=2`. For the proposed final parent
`x=(11*p-13)/2`, `y=(21*p-25)/4`, the exact sum is
`x+y=(43*p-51)/4`. Write `p=1+8*t` (from `p%8=1`). Then
`x+y=86*t-2`, so its residue mod 4 is 2 iff `t` is even, equivalently iff `p%16=1`. The helper currently assumes only `p%8=1` and `p>=33`; these do not imply the needed condition. Concrete arithmetic counterexample: `p=89` satisfies both assumptions, but gives `x=483,y=461,x+y=944 ≡ 0 (mod 4)`. Thus the third `by omega` argument cannot establish the stated `blank_no_odd_sum_two` precondition. This is a proof gap, not a counterexample to actual blank reachability.

There is also a useful split from the *actual* residual identity. Put `p=m+1=1+8*t` and `M=8*w`. Reducing
`211*p+10669+22155*M = 160*2^(201+420*M)`
modulo 32 gives `t+w ≡ 0 (mod 4)` (since the RHS is 0 mod 32). Hence:
- w even => t even => p≡1 (mod 16), and the existing odd-sum-two exclusion does apply to the q=0 terminal parent;
- w odd => t odd => p≡9 (mod 16), and that terminal sum is 0 mod 4, so this particular exclusion does not apply.

A safe repair is to strengthen `u5_q0_parent_unreachable` to assume `p%16=1`, use it only on the w-even subfamily, and separately resolve w odd by a genuinely applicable source-image/inverse argument. Alternatively, prove a stronger consequence of the full exponential identity that closes the odd-w case; the mod-32 consequence above alone does not.

I have not dispatched CI yet; the current `U5Y3M8.lean` source audit should be expected to fail at this exact precondition unless the branch is repaired. Please let me know if you want me to investigate the w-odd q=0 parent further.
