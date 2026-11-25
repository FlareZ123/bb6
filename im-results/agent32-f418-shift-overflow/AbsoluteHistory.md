# Absolute-coordinate return history and periodic-word obstruction

**Intermediate mathematical result; does not decide F418.** This file concerns the exact normal-return branch of the source-connected F418 model. The algebraic lemmas in [F418AbsoluteHistory.lean](F418AbsoluteHistory.lean) were compiled locally with Lean 4.36.0-rc2 (b35cb10); all six audited theorems have only propext, Classical.choice and Quot.sound. The specialization to the already-proved Prefix return equations is explained below; it is not a new full-source CI claim.

## Absolute history

For a legal normal word, let p_i be its first-even-bit index divided by two, C_i its correction, b_i its low prefix integer (Prefix.value 0). Put L_i=2p_i+1, S_i=sum_{j<=i} L_j, W_i=W_0+sum_{j<=i}(5p_j+3), A_i=S_i+W_i-1. Then

    N_t = floor((N_0 + sum_{i<=t} 2^A_i - sum_{i<=t} C_i 2^S_i)/2^S_t).

This is exact, even using signed intermediates: nested integer divisions compose, and each newly added term is divisible by the current power of two. The Lean theorem advance_value checks the one-step identity; iteration gives the displayed formula. Also

    A_i - A_(i-1) = 7p_i+4,   A_0=W_0-1.

Thus an odd p_i creates a parity-changing gap in the emitted powers. The equality gives a direct causal certificate: at any proposed cut S_i, terms from later events have exponents at least S_i, and cannot change the already-consumed low bits. A candidate infinite normal prefix word is legal precisely when each proposed b_i is the actual low word of this history modulo 2^L_i, and each b_i is a valid Prefix low word. The existing source safety theorem supplies width and positivity on the genuine path. This condition does not assume the existence of such a word for the genuine seed.

## Exact repeat-block obstruction

For a finite nonempty word of complete Prefix blocks, set

    L = sum L_i, D = sum(5p_i+3), H=L+D,
    U = sum 2^(A_i-W_0),
    K = sum (b_i 2^S_(i-1) + C_i 2^S_i),
    M=2^L, R=2^H.

The exact normal-return equation, multiplied by its consumed power of two, gives

    M N' = N + U 2^W - K,
    2^W' = 2^D 2^W.

The composition theorem Block.rel_append checks this multiplication law; Block.rel_one is its specialization to the one-step relation N=2^(2p+1)Q+b. The latter is exactly Prefix.value_affine in F418SignedQueue.lean, with C=b.C and b=b.value 0; the no-underflow return is the established Prefix.next equation on a safe source checkpoint.

Define the integer defect

    Z(N,W) = (M-1)(R-1)N - (M-1)U 2^W + (R-1)K.

Every execution of the same complete block satisfies M Z(N',W')=Z(N,W). Consequently arbitrarily many consecutive repetitions imply Z=0, since a nonzero integer cannot be divisible by every power of M>=2. The Lean theorems periodic_defect_zero and Block.periodic_required quantify over every such infinite repeat, without a simulation cutoff.

In particular every indefinitely repeated *single* complete Prefix is impossible, from any initial checkpoint. Here H=7p+4, L=2p+1, U=2^(H-1), and Z=0 would require (2^H-1) dividing (2^L-1)2^(W+H-1). Cancel the power of two, since the divisor is odd. This contradicts 0<2^L-1<2^H-1. This argument, for arbitrary p, C, low word and starting width, is kernel-checked in no_constant_prefix.

### Stronger consequence for periodic words (paper proof)

For any repeated complete word the defect identity requires

    (2^H-1) | (2^L-1) U.

Put g=gcd(H,L). The elementary identity gcd(2^H-1,2^L-1)=2^g-1 implies

    U = v (2^H-1)/(2^g-1),   0<v<2^g-1.

Consequently the H-bit pulse word is a concatenation of H/g identical g-bit blocks: multiply v by 1+2^g+...+2^(H-g), with no binary carries. Its one positions have cyclic gaps 7p_i+4, including the wraparound gap to the first emitted power. Repetition of the pulse word therefore forces repetition of the p-word itself. Since g<H, no indefinitely repeated full normal word can have a primitive (non-repeating) p-word.

More precisely, if the p-sequence within the complete word has primitive period r, let H_0 and L_0 be the pulse span and consumed span of those r events. The minimal cyclic bit period of the pulse word is H_0 (its pulses and gap sequence determine one another). Since the pulse word has period g, H_0 divides g, hence H_0 divides L. If m events comprise the complete repeated word, its length must satisfy

    m/r is a multiple of H_0/gcd(H_0,L_0).

This rules out periodic certificates with an independently primitive p-word, but it does not exclude longer periods of the odd-prefix bits when the p-sequence repeats with a shorter period.

## Boundary of progress

The actual F418 root may generate nonperiodic normal prefixes forever, reach a recoverable odd-only word, or reach a fatal word. None of these alternatives is established here. A periodic-word obstruction is a restriction on the form of a possible infinite orbit, not a nonhalting certificate. The remaining target is a genuine all-time bound on the spacing of parity-changing emissions relative to the current cancellation debt. The exact absolute history makes such a statement depend only on the return-word history, instead of the enormous register.
