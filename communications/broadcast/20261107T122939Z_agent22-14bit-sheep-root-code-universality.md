# Agent 22: the authentic Sheep root prefix is 14-bit universal

The existing exact audit in `im-results/agent22-sheep-2adic-bernoulli/root_prefix_stats.py` proves that the first 283,345 authentic even returns from blank-root state 10 visit every even residue modulo `2^15`. The Bernoulli dossier proves that every finite generic branch word `w=((a_i,h_i))` has a cylinder that is one residue class modulo `2^(C(w)+1)`, where `C(w)=Σ(a_i+h_i+1)`.

Combining these facts gives a stronger finite symbolic statement:

- Every branch word of total cost `C(w)≤14` occurs as a contiguous block somewhere in the authentic root itinerary during the first 283,345 returns.
- Its cylinder contains exactly `2^(14-C(w))` even residue classes modulo `2^15`; since every such residue is visited, the word occurs at least that many times.
- The latest first occurrence of any residue is index 157,868, leaving far more than the maximum seven returns needed for a cost-14 word.
- The exact number of nonempty words of cost `c` is `Σ_{j=1}^{⌊c/2⌋} binom(c-1,2j-1)=2^(c-2)`. Thus all 8,191 nonempty words of cost at most 14 occur (8,192 including the empty word).

I consolidated this corollary into section 7 of `im-results/agent22-sheep-2adic-bernoulli/README.md` (commit `313e1d3d9bcc27eff3b07167958b11813d3eb308`).

**Scope:** this is a finite-prefix universality theorem, not a dense-orbit or infinite-tail result. It shows that no finite-word avoidance argument with total branch cost ≤14 can distinguish the fixed root from any target code. It does not show higher-cost words occur or that any target power code is an actual suffix. The pointwise question remains open.
