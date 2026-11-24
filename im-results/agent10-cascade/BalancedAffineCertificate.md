# Balanced affine certificates with one endpoint congruence

## Exact construction

Use centered height X=2h+5. A reset token is (a,delta), with v=a+1 and next level k+delta. The established reset grammar is equivalent to

    2^v Y = 3^a (X+16*2^k+2*k+5)

when the source band is strict (nonfatal) and Y is odd. Every finite word has summary (A,D,R,S,T,n), where A=sum(v), D=sum(delta), n=length, and

    2^A Y = R X + S*2^k + T.

Token summary: (a+1,delta,3^a,16*3^a,(2*k+5)*3^a,1). Compose consecutive summaries l,r by

    A = l.A+r.A
    D = l.D+r.D
    R = l.R*r.R
    S = r.R*l.S + 2^(l.A+l.D)*r.S
    T = r.R*l.T + 2^l.A*r.T
    n = l.n+r.n.

### Single-congruence theorem

For a candidate word, propagate only an outward-rounded interval enclosing X/2^k at integer scale 2^64, checking the strict band at every source. The balanced affine summary is independent of all intermediate full heights.

Then ONE exact endpoint congruence suffices:

    N = R X + S*2^k + T
    N mod 2^(A+1) = 2^A.

Proof: let l,r be any split, and L=l.R*X+l.S*2^k+l.T. The composite equality is

    2^l.A * (2^r.A * Y) = r.R*L + 2^l.A*(r.S*2^(k+l.D)+r.T).

Since r.R is odd, 2^l.A divides L. Put M=L/2^l.A. If r is nonempty, its denominator is even, S even, T odd, and R odd; reduction of the right-side recurrence modulo 2 forces M odd. If r is empty, M=Y. Recursing gives integral odd centered heights at every boundary, and the high interval ensures each source band, hence every token is an exact reset edge. No intermediate low-bit tests or full-height arithmetic are needed by the verifier.

Local Lean 4.36.0-rc2 checked the generic interval, exact low valuation, composition, split congruence and checker soundness theorems (standard axioms only). The source of Grammar is copied verbatim from FirstInverseComplete.ResetParent. The original-machine import closure and HighWordShield adapter have not yet been run. This is not a new source-certified fatal cutoff.

## Computational generator

block746.cpp uses GMP exact integers. It predicts tokens from a 64-bit fixed-point high interval and a finite low residue. Divide-and-conquer consumes half the low precision, computes a midpoint residue with the balanced affine summary, and predicts the second half. A full-height update occurs only at a block boundary. Precision or interval failures cause conservative exact fallback. The low-bit nonfatal test can also accept a source that the high-only checker would conservatively reject; in that case split or use the old exact certificate.

Compile:

    g++ -O3 -std=c++20 block746.cpp -lgmpxx -lgmp -o block746
    ./block746 1000000 1048576
    ./block746 1000000 1048576 direct
    ./block746 100000 1048576 fast fast.tokens
    ./block746 100000 1048576 direct direct.tokens
    cmp fast.tokens direct.tokens

Each trace token is two bytes (a,delta). Entire 100k token streams were byte-identical (SHA256 08aed1c7a37b56d0057080c44de6158af3498364e0037bbeffb5105dd5e6ab2a). The 1m endpoints matched level and mod-1e9+7 fingerprint; the initial direct implementation took 21.26s, recursive block predictor 0.31s. These are local single-machine measurements, not asymptotic guarantees.

    ./block746 50000000 16777216

Computed 50,000,000 reset edges without detected fatality in 19.85s, level 38,915,474, centered height bit length 38,915,478, 23 blocks, no exact fallbacks or interval stops, maximum v=27, fingerprint mod 1e9+7 = 150605044. This is computational evidence only. It is not a 50m-step kernel certificate or a decision of nonhalting.

## Kernel benchmark

From this directory compile in order (LEAN_PATH includes the directory):

    lean -o PeriodicRigidity.olean PeriodicRigidity.lean
    lean -o PeriodicReset.olean PeriodicReset.lean
    lean -o BlockIntervalLow.olean BlockIntervalLow.lean
    lean -o HighWordCertificate.olean HighWordCertificate.lean
    python make_high_example.py 10000 > HighExample.lean
    lean HighExample.lean

The 10,000-reset balanced certificate from h=2 passed by decide +kernel, endpoint level 7671, endpoint height bit length 7674. Local compile 8.67s vs 17.59s for a prior balanced high+low checker. Axioms: propext, Classical.choice, Quot.sound; no sorryAx/native_decide. Benchmark compares the two new approaches, not the optimized source-accepted EvenBatch checker. This method should scale better in the big-integer work; parsing certificates and kernel overhead remain costs.

Next: use packed token certificates and sharded exact endpoints, and integrate the generic source bridge with the already accepted ResetBlockCore and ResetChain. The all-time rooted fatal-index question remains open.
