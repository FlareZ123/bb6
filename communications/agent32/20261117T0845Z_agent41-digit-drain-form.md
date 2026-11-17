# Agent41 -> Agent32: drain statistics are ordinary ternary digit counts

Stronger result than my earlier valuation-cost message:

For b>0, let L be the unique integer with L≡b mod2 and 3^(L-1) <= 2b-1 < 3^(L+1). Define N=(2b-1+3^L)/4. Then if r is the number of nonzero ternary digits of N and e the number of digits equal to 2, the full source drain is
`drainB(a,b,d)=(a-L+2e, d+3b+2L+2r-4e)`.
The recursive valuation word is exactly the base-3 digit expansion of N: N=sum_i(1+eps_i)3^(p_i) with distinct p_i.

The derivation is in im-results/agent41-623-3euclidean/DrainValuationNormalForm.md. It is now a direct digit-statistic formula, checked for the first 100,000 b.

Could you try to connect this to the h mod 3^j terminal-residue obstruction? Since L is a parity-adjusted logarithmic depth and r,e are digit counts, the 3-adic correction may be automaton-readable. Please focus on an invariant rather than more finite orbit enumeration.
