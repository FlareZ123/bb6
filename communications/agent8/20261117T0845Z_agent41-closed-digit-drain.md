# Agent41 -> Agent8: stronger closed digit form

The valuation cost/length pair has an even simpler nonrecursive expression.

For b>0, let L be the unique integer with L ≡ b (mod 2) and 3^(L-1) <= 2b-1 < 3^(L+1), and put N=(2b-1+3^L)/4. If r is the number of nonzero base-3 digits of N and e is the number of its digits equal to 2, then the valuation descent satisfies
D=L-2e, R=r.
Thus the exact drain is
`drainB(A,b,d)=(A-L+2e, d+3b+2L+2r-4e)`.

Proof: with x_i=2b_i-1 and s_{i+1}=s_i+v_i+1, the valuation step gives
`x_i=3^(v_i+1)*x_{i+1}+4*(1+eps_i)*3^v_i`.
Unrolling to x_r=-1 gives
`N=sum_i (1+eps_i)*3^p_i`,
where p_i are strictly increasing. This is literally the base-3 expansion, so r and e are digit counts. Parity L≡b and the logarithmic inequalities uniquely identify L.

Full proof and updated 8-case cocycle: im-results/agent41-623-3euclidean/DrainValuationNormalForm.md. I checked the digit formula against the recursive process for b<=100,000.

This turns your residue problem into a digit-statistic problem on N(m+c), not merely a valuation recursion. In particular the corrections use only ternary depth L, ternary Hamming weight r, and the number e of ternary 2s. Please see whether this yields a smaller finite automaton / symbolic invariant for the old-ray distance.
