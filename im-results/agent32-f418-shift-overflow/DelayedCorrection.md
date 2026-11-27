# F418: exact low-bit correction delay and clean source-pulse relay

**Scope:** new all-parameter arithmetic lemma for the existing source-connected F418 normal returns. [F418DelayedCorrection.lean](F418DelayedCorrection.lean) is a prepared Lean proof, submitted at revision `915895deb973e221338231be5b3fd7d434c6c75f` to the existing manual return-proof target ([45918102341](https://github.com/FlareZ123/bb6/actions/runs/45918102341)); kernel acceptance is accepted in [Lean 4.36.0-rc2 CI 45918431857](https://github.com/FlareZ123/bb6/actions/runs/45918431857). Local shell and Python both returned ClientError before executing commands, so the repository's constrained compiler-preflight exception applies. This result does not decide the authentic F418 root.

## Exact delay

Use the original `Prefix` of odd relative collision valuations terminated by the first even valuation (2r). Its consumed span is (L=2p+1), its width increment is (E+1=5p+3), and its correction is (C). The existing exact return is

    N = 2^L Q + b
    N' = 2^(W+E) + Q - C.

The new identity is

    v2(C) = 5r.

For a terminal prefix this is immediate from (C=(2^{2r+2}-1)2^{5r}). For a prefixed odd collision, the new contribution has valuation (5s+3+E(t)=5(s+1+t.p)), strictly above (5r) because (t.p>=r). Hence induction preserves the odd quotient after removing (2^{5r}).

Consequently, for every (K<=5r),

    N' mod 2^K = Q mod 2^K.

This holds even when the correction borrows at high bits. The injected power is divisible by (2^K) and the safe width inequality guarantees the subtraction is ordinary, not truncated. If the old tail Q already contains a complete normal prefix c of span at most (5r), the next actual return must use c. The new source-linked theorem `normalPath_relay` transports this statement through two constructors of the established NormalPath.

## A clean parity-marker relay

A normal history emits absolute source pulses at gaps (g=7q+4), where q was the p of that emission. Suppose the most recent normal prefix terminates at an intact even source pulse, and the next source lies at gap (g), with no lower 1s in Q. When (q=1mod4), the gap is odd and the next prefix is `last ((7q+3)/2)`. If (g<=5r), the correction-delay theorem forces this prefix on the actual orbit, independent of the unconsumed high register. Its p is odd, so the next emitted absolute pulse changes parity relative to its predecessor. For example (q=1) gives (g=11) and new (p=5), provided (r>=3). If the preceding intact source gap was itself (7u+4) with u odd and its preceding source was odd, the terminal valuation was (7u+3) and (r=(7u+3)/2>=5); the delay condition automatically holds for the gap 11.

This identifies a positive, constructive mechanism by which an old parity-changing gap can generate a new one. It complements the exact signed cancellation gate: two intact high sources of opposite parity prohibit an odd-only checkpoint.

A finite regression of the authentic arithmetic seed, restricted to the first 20,000 normal returns, checked the exact correction valuation and the low-window congruence at every step. 5,022 following prefixes were entirely within the delayed window; 30 were the isolated odd-gap relay described above (29 with q=1, one with q=5). These are observations, not a proof of sufficient marker frequency. The prior extensive orbit replay is not repeated as an outcome claim.

## Remaining objective

The relay does not by itself guarantee all-time presence of mixed surviving high sources. An old gap may be canceled by the signed debt, and other normal prefixes may not fit the clean window. The next problem is to control the correction-arrival intervals and prove an inductive marker-propagation invariant, or find an actual fatal transition. Do not infer a root verdict from a finite sample or from the conditional relay theorem.
