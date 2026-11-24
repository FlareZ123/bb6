# Binary half-step rank windows and a genuine obstruction to short barriers

## Strongest result

[Q0WideRank.lean](Q0WideRank.lean) and [Q0WideWindow.lean](Q0WideWindow.lean) prove wide_rank_cover, q0_wide_cross and q0_of_no_wide_cross: every necessary signed macro path from q0 with u>=1,000,000 has a strict doubled-rank crossing at a*4^k+b, a in {1,2}, k>=12, 0<=b<9, with **floor(4^k/(128*(k+1))) half-steps on each side**. This is nearly linear in the rank scale, and wideRadius_ge_sqrt proves it dominates the earlier 2^k radius at every relevant k. A uniform no-crossing theorem for the larger radius suffices to close the large-u family; the prior small-u kernel certificate covers u<1,000,000. This is a stronger conditional reduction, not an exclusion of any further q0 parameter, a #429 decision, or a BB(6) bound.

The simpler conjecture with only k past and 2k future steps is **false**. Q0HalfCounterexample.lean proves `crossing56 : Cross2 2 2 56` by kernel reduction, with only propext. It is an actual strict signed graph trace, including even heights at A-phase boundaries (checked by exact replay), not merely a spurious carry state. The long-window theorem is necessary precisely because local crossings of logarithmic length need not be absent.

## Exact binary factorization

In the signed macro graph p'=p+l_d, 16y'=y+d*p+c_d, d in {0,1,4,5}. Put P=2p, H=2y, G=P-3H. Write d=x+4z for bits x,z. A and B phases alternate:

    A: P'=P+5+4x, 4H'=H+xP+12x.
    B: P''=P'+1+2z, 4H''=H'+zP'+4z.

The two divisions are exact whenever the original macro division is exact. Their composition equals the original doubled-rank macro transition. Q0HalfStep.lean proves pair_of_macro, expand_trace, strict_step and trace_valid. At A (even rank) the step may branch; at B (odd rank) the two options cannot both be valid. In positive coordinates (H,G), the same transformations are:

    A0: (H/4, G+9H/4+5) if 4|H
    A1: (H+G/4+3, G/4) if 4|G
    B0: (H/4, G+9H/4+1) if 4|H
    B1: (H+G/4+1, G/4) if 4|G.

Strict positivity of both counters persists. Trace is a safe overapproximation because it does not require H even at every A phase; the source implication is nevertheless exact in its forward direction.

## Why rank doubling has enough extra room

Q0Growth.lean proves block_extra: any strict macro trace of length K with terminal rank <=16^K must cost at least 3K+1. Otherwise every digit is zero, so positive terminal ordinate would imply initial ordinate >=16^K, contradicting the cone. Splitting into j full K-blocks yields rank P>=p+3m+j whenever jK<=m and P<=16^K. This is an unconditional all-parameter statement, stronger than merely using rank increments >=3.

For the q0 forced path, m=8u+5, p=24u+22, y=6u+4, hence p=3m+7. Set p0=2p and choose t with 4^t<=p0<4^(t+1), so t>=12 when u>=10^6. The macro terminal rank is <=72u+52<16^(t+1). Use K=t+1 and j=14*2^(t+1)+11: since 256(t+1)<=2^t, jK<=m. Consequently the doubled terminal rank exceeds 2p0 by at least 28*2^(t+1)+8.

Consider B=2*4^t, 4^(t+1), then 2*4^(t+1), choosing the first with p0+9*2^k<=B (k=t or t+1). The extra growth implies B+8+9*2^k<=P_terminal. Each half-step costs 1..9, so the first crossing q is B+b with b<9 and has at least 2^k steps on both sides. All arithmetic and trace-splitting arguments are kernel checked.

For the stronger radius, let F=4^t, K=t+1, A=floor(F/(128K)), B=floor(4F/(128(K+1))). For each integer j with 6jK+14<=p0, extra_growth gives P_terminal+14>=2p0+2j. This uses the entire growth budget rather than a fixed square-root margin. Choose the first of 2F, 4F, 8F satisfying the lower margin (9A for the first and 9B for the other two). The respective budgets j=5A+11, 9A+5B+11, 14B+11 satisfy the premise using 512K<=F, 128KA<=F and 32KB<=F, and guarantee the upper margin including the overshoot 8. Thus trace_window applies at the larger radius. The pure arithmetic module and the path adapter both compiled in Lean 4.36.0-rc2. The local dependency preflight used byte-identical Q0MacroCore (06821fae), Q0Growth (396464bd), Q0HalfStep (2ccbc1d9), and verbatim relevant declarations (with their actual proofs, no stubs) from Q0RankBarrier, Q0DoubleBarrier, Q0HalfCoverage and Q0LongWindow. The complete original-file import closure has not been rebuilt here. Exported axioms: only propext, Classical.choice, Quot.sound or subsets.

## The short-window counterexample

At a=2,b=2,k=56, start phase A at

    P=10384593717069655257060992658440018
    H=16697335249881209147839387533312.

Use words in chronological order:

    w = 0^47 101100000
    v = 0^46 1011111111
    z = 1^46 0010100101.

Each has length 56; the first reaches rank 2*4^56+2 and height 3208740581827705672538529988608. All 168 steps are exact and interior. The final rank/height are 10384593717069655257060992658440708 and 2761104764795550259482406400207668. Exact simulation of both possible branches shows only one further half-step is possible from this endpoint, then none. Other short crossings at b=1,7 likewise die within two extra steps. This witness does not arise from a proved authentic blank ancestry and does not refute the long-window criterion.

## Reproduction

Lean 4.36.0-rc2 local dependency closure: original Q0MacroCore, Q0RankBarrier, new Q0DoubleBarrier, then Q0HalfStep, Q0Growth, Q0HalfCoverage, Q0HalfCounterexample, Q0LongWindow. All named general theorems use only standard propext, Classical.choice, Quot.sound or subsets; crossing56 uses propext only. No sorry or native_decide in these new modules. See Q0DoubleBarrier.md for the independent five-coefficient finite chain. Its finite results remain valid; neither the five-coefficient uniform hypothesis nor the long binary-window hypothesis has been proved.

The productive target is an all-scale bound on the possible lifetime or combined past/future extent of strict states near powers of two, e.g. o(4^k/k) half-steps with an explicit bound at all relevant scales. The exact radix-four carry recurrence for k-digit rolling words is 4e'=e+a*r+d*q+c_phase(d), q'=q+l_phase(d), where r is the outgoing old bit and d the appended bit. In particular with g=q+a-3e, output zero contracts e to (e+a*r)/4; output one contracts g to (g+3a(1-r))/4. The input equals the output k steps earlier. Exploit this delayed binary relation; a further arbitrary finite scan is not a uniform proof.
