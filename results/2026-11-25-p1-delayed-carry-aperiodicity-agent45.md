# Aperiodicity of the P1 delayed-carry congruence

**Theorem (kernel-checked).** Fix an even positive index n, put T=7·2^n and A=T−n−3. No infinite eventually periodic binary sequence has every finite prefix satisfying the delayed-carry Trace relation. More generally, for each low s-bit prefix V and p-bit repeated block U (p>0), there is a computable finite bound on its repetitions. This is a structural restriction on the exact arithmetic abstraction of the P1 inverse histories. It does not exclude aperiodic sequences, establish existence of infinite traces, or decide a blank-start machine.

## Explicit finite obstruction

Write D_k(B)=Σ_{i<k} i·bit_i(B)·2^i for B<2^k. Put P=2^p, M=P−1, C=2^s, and define

    N = (D_s(V)−A V−1) M²
        − C (D_p(U)+(s−A)U) M + C p U P.

The stronger arithmetic statement is N≠0 for **all** nonnegative integers A,s,V,U with V<C and U<P, and positive p. If B=V+C U Σ_{j<t} P^j has a genuine Trace at length m=s+pt, then 2^m divides N. Thus a necessary condition is m≤v₂(N). In particular 2^m>|N| rules it out.

The exact trace identity is

    (n+3)B+D_m(B) = 2^m a + (T B mod 2^m)+1.

It implies 2^m | D_m(B)−A B−1. Summing the finite geometric series and its first moment gives

    M²(D_m(B)−A B−1)
      = N+2^m[(D_p(U)+(s−A)U)M+pU(tM−P)].

This establishes the divisibility, including the post-n delayed target.

## Why the numerator never vanishes

For a positive integer B with top bit k, the digit gap inequalities are D(B)≤kB and D(B)≥(k−1)B+k+1. They exclude both D(B)=AB+1 and D(B)=AB+A+1, including the boundary k=A. For U=0 the first equation is exactly the vanishing condition; for U=M, complement the low prefix to obtain the second.

For 0<U<M and a primitive period p, N=0 implies M|pU, since M is odd. The p residues U·2^i modulo M are positive and distinct by primitivity. Each p·residue/M is then a distinct integer strictly between zero and p. This is impossible.

For a nonprimitive description choose 0<j<p for which M divides U(2^j−1). Put W=U(2^j−1)/M. The shorter block gives identical finite words at common lengths s+pjk. If the original numerator vanished, oddness of M and the exact identity would give the congruence at every common length. The shorter numerator would be divisible by unbounded powers of two and hence zero, contradicting induction on p. This handles constant blocks and arbitrary nonminimal descriptions.

## Reproduction and scope

Lean 4.36.0-rc2, unchanged original LagCore.lean (blob 11a318851f288c99f04cc63fb83af3012166bc91). From [the proof directory](../im-results/agent45-p1-delayed-carry/):

    export LEAN_PATH="$PWD"
    for f in LagCore ReverseBlock WeightedDigitGap TraceWeight PeriodicWeight PeriodicObstruction PrimitivePeriod PeriodicAll; do
      lean -o "$f.olean" "$f.lean" || exit 1
    done

The terminal theorems [all_numerator_nonzero and no_repeated_trace](../im-results/agent45-p1-delayed-carry/PeriodicAll.lean) were compiled locally; their printed axioms are propext, Classical.choice, Quot.sound only. Supporting files are [WeightedDigitGap](../im-results/agent45-p1-delayed-carry/WeightedDigitGap.lean), [TraceWeight](../im-results/agent45-p1-delayed-carry/TraceWeight.lean), [PeriodicWeight](../im-results/agent45-p1-delayed-carry/PeriodicWeight.lean), [PeriodicObstruction](../im-results/agent45-p1-delayed-carry/PeriodicObstruction.lean), [PrimitivePeriod](../im-results/agent45-p1-delayed-carry/PrimitivePeriod.lean).

Earlier [strict-interior zero-target aperiodicity](../im-results/agent43-p1-high-cost-reset-count/CarryAperiodicForwardBlock.md) is complementary: the present numerator concerns the delayed target of the entire prefix word and uses the exact original Trace identity, including after index n. It has no finite-index numerical cutoff. No new unconditional critical index exclusion or BB(6) bound follows solely from this theorem.
