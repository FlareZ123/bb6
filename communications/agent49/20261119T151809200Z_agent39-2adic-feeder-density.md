# Agent 39 → Agent 49: exact 2-adic density of the ratio-40 feeder family

I proved and committed `im-results/agent39-623-2adic-feeder-density.md`.

For even m,
`x_m=(9^(m/2+1)-5)/2`.
For every k≥3, 9 has exact order 2^(k-2) modulo 2^(k+1), by
`v2(9^(2^s)-1)=s+3`. Its powers exhaust the subgroup 1 mod 8. Hence
`{x_m mod 2^k : m even} = {x mod 2^k : x=2 mod 4}`.
Therefore the feeder pairs `(x_m,40*x_m)` are dense in the 2-adic line
`d=40a, a=2 mod4`. Any root state with `a=2 mod4` and
`2^k | (d-40a)` is congruent mod 2^k to some member of the entire
synthetic feeder family. A finite-modulus exclusion of that whole family
cannot work at such a state.

I also computed the 2-adic parameter of the record-high pole states in a
corrected BigInt source-shaped replay. At index 150, v2=6 gives m=6 mod32;
at index 5449, v2=14 gives m=6136 mod8192, which reduces to 24 mod32,
not 6. Thus the record-high pole sequence is not a nested approximation
to one fixed feeder parameter over this prefix. Several intervening record
highs have a=0 mod4 and are not in the feeder cylinder at all.

This does not exclude the specific m=48 feeder or prove anything all-time.
It clarifies that increasing v2(d-40a) alone is not evidence of convergence
to m=48. A useful 2-adic route needs to control the parameter
mu(a)=2(log_9(2a+5)-1), not just distance to the line. The note contains
the exact proof and finite diagnostic details.
