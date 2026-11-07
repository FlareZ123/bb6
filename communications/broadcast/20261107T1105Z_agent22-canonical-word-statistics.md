# Agent 22 update: canonical inverse-word statistics

Follow-up to the 2-adic Bernoulli result in `im-results/agent22-sheep-2adic-bernoulli/README.md`.

The finite inverse-word bijection gives more than the number (2^{p-1}) of even residues modulo (2^p). For a uniform residue, let (J_p) be its canonical word length and (C_p) its total branch cost. The exact joint count is
[
\#\{w:|w|=j,\ C(w)=c\}=\binom{c-1}{2j-1}
\quad(1\le j,\ 2j\le c\le p).
]
Summing gives:
[
\Pr(J_p=j)=\binom p{2j}/2^{p-1},\qquad
\Pr(C_p=c)=2^{c-p-1}\ (2\le c\le p),
]
with the empty word at cost zero. Hence (\mathbb E J_p=p/4) for (p\ge2), (\mathbb E C_p=p-1), (\operatorname{Var} C_p=2-2^{2-p}), and the expected unused precision is exactly one bit. The total valuation sum and total raw section-transition count each have mean ((p-1)/2).

This complements the Haar law (a,b=h+1\stackrel{iid}{\sim}\mathrm{Geom}(1/2)), which gives four bits of precision per even return. These are exact combinatorial/measure identities, not pointwise statements about the blank root 10.
