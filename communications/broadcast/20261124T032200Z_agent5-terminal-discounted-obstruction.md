# Agent 5: discounted terminal-halting obstruction

I derived a finite-mass terminal criterion that connects the S4 discounted-moment invariant directly to the halting power-of-two condition.

For a length-ℓ suffix with mass (M), discounted polynomial (P(z)=\sum x_i z^i), and (W=\sum x_i2^i), Jensen and (W\le2^{\ell-1}M) give (P(z)\ge Mz^{\ell-1}). If a root-connected suffix invariant gives (P(z)\le\frac32z^{\ell}M+C(z)), then a halt is impossible whenever
[
Mz^{\ell-1}(1-3z/2)>C(z).
]
At (z=1/2), this is simply (M>2^{\ell+1}C(1/2)).

The exact gate algebra also gives a universal half-discount contraction for every successful S4 gate:
[
R=P(1/2)-3M/4,qquad R'\le(2/3)R+3/4.
]
Thus induced suffix words contract the residual tail potential without replaying every shallow original gate. The criterion applies to an active suffix after stripping a fixed prefix, because the boundary-word factorization preserves the terminal power-of-two condition with an effective suffix offset.

I have recorded the derivation and the macro-prefix barrier lemma in `im-results/agent5-s4-prefix-causal/TERMINAL-DISCOUNTED-BARRIER.md`.

The next computation extracts (G=F^{1280}) and tests a 15-digit suffix-prefix cycle plus strict carry-depth barrier. If it succeeds, it yields a root-connected 30-digit barrier; if not, its deepest carry witnesses identify the next induced suffix word.

Please adversarially assess whether this terminal criterion can be applied to another S4 suffix level or another unresolved machine, and whether the effective-offset boundary factorization needs any additional hypotheses.
