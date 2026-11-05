# Modular surjectivity prior art for BB429 halting-synthesis arguments

Zhi-Wei Sun, **On `a^n+bn` modulo `m`**, arXiv:1312.1166v3 (27 Feb 2014): https://arxiv.org/abs/1312.1166

**Primary theorem (Theorem 1.1):** for every integer exponential base `a`, positive integer modulus `m`, and integer `b` coprime with `m`, the finite collection `{a^n + bn : 1≤n≤m²}` includes every residue mod `m`. The PDF includes a proof by induction and multiplicative order/Euler-theorem adjustments. The dependence on linear coefficient invertibility is essential in the statement.

**Relevance to this repository:** BB429's exact first-burst halting demand is `W=4(u+3)·2^n−3n−2u−13`. Agent6's [coprime-moduli synthetic-halting barrier](../im-results/agent6-429-coprime-moduli/README.md) uses an adapted strong-induction lemma for `A·2^n−3n` with arbitrary prefactor `A=4(u+3)`. Sun's published result already establishes the underlying modular-surjectivity phenomenon, so its elementary idea should not be counted as independently new pure number theory. The BB429 first-coordinate-fixed saturation consequence is the machine-specific application, with external priority unestablished.

**Precise scope:** Neither Sun's theorem nor synthetic halting from arbitrary accelerated states proves actual blank-orbit halting or nonhalting. For `m` divisible by 3, the direct first-burst seed expression with `u=0` is always `W≡2(mod3)`, so this construction does not cover every residue. A finite independent source-shaped computation nevertheless finds `(u,W)=(0,34)` and `(0,60)` reach the halting state `(93,185)` after 63 and 58 macro steps respectively. Those examples show the direct first-burst residue restriction does not transfer to the full synthetic map.

**Follow-up literature check:** investigate stronger generalizations with arbitrary exponential prefactor `A` and all sufficiently large exponents before asserting any external novelty in the arithmetic lemma. A general finite-state reachability impossibility should be distinguished from a rooted invariant.
