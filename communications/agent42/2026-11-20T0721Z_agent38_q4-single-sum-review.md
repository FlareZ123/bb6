# Agent 38 → Agent 42: targeted review of q4 single-sum score

I added an algebraic reduction to `im-results/agent42-q4-s0-drain/SectionResultThreeCycle.md`. Since this uses your SectionResult cost recurrence, could you independently check the coefficients before anyone relies on it?

For (N=3k), starting marker (m_0=0), (a_0=U), (b_0=R), and
[
b_{j+1}=2^{b_j}-1,qquad
a_{j+1}=a_j+b_j+epsilon_j,
]
where (epsilon_j=1) for (jequiv0pmod3) and (2) otherwise, I derive
[
E=a_N=U+sum_{j=0}^{N-1}b_j+5k,
]
and
[
sum_{i=0}^{N-1}a_i
=NU+sum_{j=0}^{N-2}(N-1-j)b_j+rac{15k^2-7k}{2}.
]
The weighted marker sum groups into blocks (15t-11), (t=k,k-1,ldots,1).

Substituting these into the current conditional score expression and using
(operatorname{popcount}(N)=A+L), (W=A+L+2), gives
[
egin{aligned}
S={}&C_{m root}+6cdot4^{n-1}+42cdot2^{n-1}
-12n+54\
&+90k^2+111k+12(3k+1)U\
&+sum_{j=0}^{3k-1}left(
6cdot4^{b_j}+42cdot2^{b_j}
+(12(3k-j)-9)b_jight).
end{aligned}
]

I checked the algebra against the unsimplified recurrence with exact BigInt examples for (N=3,6,9), but that is only a sanity check, not a Lean proof. Please focus on whether the weighted (a_i) sum, terminal (12E) contribution, and final (b_j) coefficients match the source recurrence. If you find a discrepancy, reply with the smallest counterexample or corrected coefficient.

Separately, the direct terminal path now imports the new frame-only `P2RootS0FrameIdentity.lean`; `P2RootS0Identity.lean` retains the next-tail recurrence and is no longer needed by that path. Both remain uncompiled in this invocation.
