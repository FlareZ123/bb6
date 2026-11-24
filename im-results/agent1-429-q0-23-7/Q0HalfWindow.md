# Binary half-step rank windows and a genuine obstruction to short barriers

## Strongest result

The gate-aware exact delayed-carry criterion below refines the wide-window proof obligation by restricting the first crossing to six central pairs for each coefficient. The wide-window result supplies its quantitative radius. The gate is not a proof of nonexistence. The complementary [radix-four convolution](Q0DigitConvolution.md) bounds the residual at arbitrary ranks by their digit sum, and gives an equivalent multi-delay update. It is an alternative all-scale proof mechanism; the logarithmic residual does not eliminate the binary history.

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

## Exact signed delayed-carry formulation

The strongest current reduction is [Q0StripCross.lean](Q0StripCross.lean), `q0_of_no_wide_strip`: excluding `StripCross a b k (wideRadius k)` for a=1,2, k>=12, 0<=b<9 excludes every remaining large-u q0 target under the existing source interface. Unlike independent carry inputs, this is an exact criterion for the full phase-lattice crossing, not a relaxed digit model.

[Q0ExactHalf.lean](Q0ExactHalf.lean) proves both directions of the aligned two-step macro factorization, unique strict predecessor, exact trace splitting, and q0_wide_exact_cross. The A-phase height parity is retained at every vertex; Q0StripCross.exact_of_trace shows ordinary exact-division traces already force it at all nonterminal A states. Only terminal parity must be added. The earlier wide radius is unchanged.

[Q0SignedCarry.lean](Q0SignedCarry.lean) gives the exact chronological word identities. For a binary word w of length k, M=4^k, D=sum(w_i*4^i), L=total phase-dependent rank cost, and E the signed offset,
    
    P=p+L, M*Y=y+D*P+E.
    
E/M is in (-1/5,7/15) when the terminal phase is A and (-7/15,13/15) when B. At P=a*M+q with 5q<=2M, put e=Y-aD. Every strict k-history satisfies
    
    min(q,0)-2 <= 3e <= max(q,0)+a+2.
    
In particular negative q is legitimate. Keeping only Nat carries on the past side would discard actual histories. For oldest bit r and output d, rolling the history gives exactly
    
    q'=q+len(s,d),  4e'=e+a*r+d*q+off(s,d).
    
[Q0DelayStrip.lean](Q0DelayStrip.lean) implements the exact rolling history and lattice, and proves delay_of_exact and exact_of_delay. The latter reconstructs all intermediate full-rank coordinates. There is no free choice of r: it is removed from the history and d appended. Q0StripCross adds the closed-form seed test, using p=a*M+q-L and y=M*e-q*D-E, and proves history_of_seed, seed_of_history and strip_cross_iff. This is equivalence with ExactCrossWindow whenever 0<k<=N and 5(b+9N)<=2*4^k, conditions proved for wideRadius at every relevant scale. Thus the initial large height and all intermediate large-rank arithmetic can be eliminated in favour of signed carries and one k-bit history. The remaining all-scale proof is to exclude the exact long delayed-carry window, not to establish another translation.

Local Lean 4.36.0-rc2 compiled these four complete new source files using the same original/selected-verbatim dependency closure as the wide rank proof. The exported theorem axioms are propext, Classical.choice, Quot.sound or subsets; no sorry or native_decide. Full untouched original dependency closure remains to be checked. The exact reduction does not itself exclude another q0 parameter, decide #429, or prove a BB(6) upper bound.

## First-crossing gate

[Q0CrossGateCore.lean](Q0CrossGateCore.lean) proves a scale-independent necessary gate with two incoming and two outgoing projected edges. At the first nonnegative offset q=b, the permitted pairs (b,e) are:

- a=1: (0,0),(1,0),(2,1),(3,0),(3,1),(5,2).
- a=2: (0,0),(1,0),(1,1),(3,0),(3,1),(7,3).

[Q0CrossGate.lean](Q0CrossGate.lean) proves gate_of_strip: every StripCross with k+10<=N yields GateStrip with the complete original seed and delayed history, centered at the first crossing. At most eight half-steps move from the past to the future, and the gate is imposed on that center. Since wideRadius k>=2^k>=k+10 for k>=12, the existing q0 wide-crossing implication composes with this theorem. Gate membership is necessary, not sufficient. Local Lean 4.36.0-rc2 compiled the complete gate core, and the adapter against a verbatim slice of the actual strip definitions and split/initial lemmas; full original import closure remains unchecked. The two finite gate equalities have no axioms; the general theorems use only standard axioms.

The first-crossing restriction does not make the short-window conjecture true. Recenter the existing k=56 witness one step earlier, prepending a valid zero step to its history. Starting in phase B at (10384593717069655257060992658440017,66789340999524836591357550133248), the words 0^48 10110000, 0^47 101111111, and 1^47 001010010 give 56 past and 112 future half-steps. The center is at (a,b,e)=(2,1,0), with preceding offset -4. Exact integer replay checks integrality, phase lattice and strict interior. This recentered witness is computationally verified, not a new kernel theorem or authentic-root ancestry.

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
