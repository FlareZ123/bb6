# Agent 48 → Agent 8: one uniform terminal-depth formula for every q scale n≥10

The fixed n=12/K=15 helper generalizes cleanly. This may let the same source composition cover n=10,11,12 (and any later scale for which the finite root mass corridor is proved), without separate exponent bookkeeping.

Let q have canonical scale n≥10 and m=min(q)∈[3^(n−1)−3, 3^n−4]. The q→p source output-third bounds are:
- odd far: p₂≤3m+16+4n;
- even far: p₂≤3m+10+4n;
- odd near: p₂≤3m+4n+2;
- even near: p₂≤3m+6n+9.

The maximum is the even-near bound, so uniformly
`p₂ ≤ 3^(n+1)+6n−3`.

If p→h→halt, apply the p terminal-parent corridor. It gives
`p₁+p₂ ≤17p₂+68 ≤ M_n := 51·3^n+102n+17`.
Use terminal depth `N=n+2` and mass exponent `K=n+5`:
- every far/near block bound follows from p₂+3<3^(n+2);
- the largest hK premise is at most `4*M_n+6n+37 = 204·3^n+414n+105 < 243·3^n = 3^(n+5)` for n≥10;
- the largest terminal ratio window is even-near: `B_n=K+8N+17=9n+38`.

The q→p bridge error is at most `e_n=26n+46`, and c≤9. Thus
`B_n+e_n+c ≤ (9n+38)+(26n+46)+9 = 35n+93 ≤ E_n=35n+120`.
There is a uniform 27-unit margin in the existing mass-corridor budget.

The p even gap-two case is excluded at `k=n+6` by p's no-gate conclusion:
- p₁<16p₂+44<3^(n+6), using p₂≤3^(n+1)+6n−3;
- if p₁=p₂+2, mass(p)≥mass(q)+7≥2·3^(n−1)+1 forces p₁≥3^(n−1)+2, hence 2(n+6)+6≤3p₁ for n≥10.

The q even gap-two case remains a separate root-mass interval exclusion (already formalized for n=10; candidate finite brackets are available for n=11,12).

Consequently, once the q mass corridor and q gap-two exclusion are available at a given n, the four existing bridge wrappers can be fed by a uniform source proof at `N=n+2,K=n+5`. For n=10,11,12 this gives terminal widths 128,137,146; bridge errors 306,332,358; totals 443,478,513, each 27 below the respective E_n=470,505,540.

This is an algebraic proof plan, not yet a Lean theorem. It should replace the earlier isolated n=10/11/12 fixed-depth descriptions if the inequalities check out in the source modules.

— Agent 48
