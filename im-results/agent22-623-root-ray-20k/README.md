# #623 root-ray audit to 20,000 transitions

This is an intermediate computational cross-check of the root-specific old-ray distance predicate for the #623 high-level orbit starting at D(0,7). It is deliberately stored under `im-results/`; it is not an academic proof and does not establish that the orbit is infinite.

## Reproduction

The independent C++ mirror uses GMP:

```sh
g++ -O3 -std=c++17 trace623_gmp.cpp -lgmpxx -lgmp -o trace623_gmp
./trace623_gmp 20000
```

The implementation mirrors the `evalA`, `drainB`, and high-level transition branches used in the existing source-derived Python mirror. The source and existing analysis are in:

- `im-results/agent49-parity623/Parity623Source.lean`
- `im-results/agent49-parity623/root_inverse_explorer.py`
- `im-results/agent49-parity623/RootRayBridge.md`
- `im-results/agent49-parity623/CanonicalRayRootDistanceArithmetic.lean`

The upstream machine source is `google-deepmind/cryptids/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean`.

## Cross-check against the existing Python mirror

After 10,000 transitions, the C++ state at index 10,000 agrees with the Python mirror's state exactly. SHA-256 hashes of the decimal representations, including the trailing newline, are:

- `a_10000`: `e964a28bea585be847c37c8280065c69204c604d18fb52800088d70d261f3399`
- `d_10000`: `5455c06c482d51df8f9f2895a217ed4680f9bfe9c2af3368d32a26a2faf8d01a`

## 20,000-transition observation

Run output:

```text
i=0 a_bits=1 d_bits=3 old=1 badSquare=0 minLog2=inf@0 minAfter16=inf@0
i=10000 a_bits=3067 d_bits=3067 old=6809 badSquare=0 minLog2=0.584963@2 minAfter16=4.50313@16
DONE N=20000 old=13600 badSquare=0 minLog2=0.584963@2 minAfter16=4.50313@16 finalABits=6137 finalDBits=6136
```

The code checks every state index 0 through 19,999 before applying its transition. It classifies an old left ray by parity and the corresponding condition `a >= 2*d+9` or `a >= 2*d+5`, and an old right ray by `d >= 2*a+1` or `d >= 2*a+2`. The tested integer inequalities are:

- left odd/even: `(a-4*d-9)^2 >= d` or `(a-4*d-5)^2 >= d`;
- right odd/even: `(d-4*a-1)^2 >= 4*a` or `(d-4*a-2)^2 >= 4*a`.

For right rays, the tested gap is twice `s-a`, so the second pair is equivalent to the usual `(s-a)^2 >= a` normalization.

Observed over the 20,000 checked states:

- 13,600 states satisfy one of the four old-ray classifications;
- no old-ray state violates the corresponding square-distance inequality;
- the minimum ratio `gap^2/scale` over all old-ray states is `3/2`, at index 2;
- from index 16 onward, the minimum is `5329/235`, at index 16, where `D(a,d)=D(876,235)` and the left-odd gap is `-73`;
- the state after 20,000 transitions has `a` and `d` bit lengths 6,137 and 6,136.

## Formal algebra behind the projective gap calculation

The companion `GapCoordinateMatrices.lean` was checked locally with Lean 4.36.0-rc2. With the unshifted coordinates `R=y-4*x` and `L=x-4*y`, it proves:

- `15*x = -(4*R+L)` and `15*y = -(R+4*L)`;
- the far-left leading pair `(7*y-4*x, x-13*y)` is `((3*R-8*L)/5, (3*R+17*L)/5)`;
- the near-left leading pair `(7*x-4*y, y-13*x)` is `((-8*R+3*L)/5, (17*R+3*L)/5)`.

The Lean file proves the corresponding denominator-cleared integer identities exactly. These are algebraic coordinate changes for the leading bridge forms. They do not absorb the parity-dependent constants or the logarithmic correction bounds in `RootRayBridge.md`, and they do not establish an invariant for the root orbit.

## Exact corrected gap-scale recurrence

The new `GapScaleExactArithmetic.lean` proves the exact algebraic update for any canonical ray representation. Let `m=min(a,d)`, let `g` be the signed ratio-four gap, and write the current state in the form

`g = u + c + v - 3m`,

where `u` is the actual ray shift, `v` is the scaled canonical exponent, and `c` is the sector constant. Let the canonical base transition return `(B,E)), and define the two exact correction statistics

`beta = B-c-v`, `delta = E-3m`.

The translated output is `(B+u,E)). If it is on the left (`E ≤ B+u`), its next gap and scale satisfy

`g' = g - 9m + beta - 4*delta`, `m' = 3m + delta`.

If it is on the right (`B+u < E`), they satisfy

`g' = -4g - 9m + delta - 4*beta`, `m' = 3m + g + beta`.

Both identities are kernel-checked with Lean 4.36.0-rc2, with no admitted axioms beyond Lean's standard propositional extensionality and quotient soundness. This isolates the exact source-dependent corrections that the leading projective matrices suppress. The remaining task is to instantiate `beta` and `delta` through the four source branches, establish which output-side condition holds along the authentic root, and prove a root-specific lower bound strong enough to exclude all terminal windows.

## Interpretation and limitation

This is a formal algebraic reduction plus a finite computational cross-check. It is not a source-level all-time theorem and does not establish nonhalting or a BB(6) classification. The unresolved mathematical task remains an all-time proof that the root orbit avoids every terminal window.
