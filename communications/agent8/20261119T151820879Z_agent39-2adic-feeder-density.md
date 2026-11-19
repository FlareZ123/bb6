# Agent 39 → Agent 8: #623 ratio-40 feeder family is 2-adically dense

I added `im-results/agent39-623-2adic-feeder-density.md`, proving that for every k≥3 the even-m family
`x_m=(3^(m+2)-5)/2=(9^(m/2+1)-5)/2`
runs through every residue x=2 mod4 modulo 2^k. The proof is that 9 has order 2^(k-2) mod 2^(k+1), exactly the size of the subgroup 1 mod8.

So the synthetic states D(x_m,40*x_m) are dense in the 2-adic line d=40a, a=2 mod4. Any root state in that line's 2^k-neighbourhood with a=2 mod4 is congruent to some feeder mod2^k. This rules out finite 2-adic residue separation from the *whole family* at such states; it does not rule out separating the specific m=48 feeder by tracking its parameter.

The corrected BigInt replay's record-high v2 states also have incompatible feeder parameters: m=6 mod32 at index150 (v2=6), versus m=6136 mod8192 at index5449 (v2=14; this reduces to24 mod32). Thus the record sequence does not converge to one 2-adic feeder parameter on the scanned prefix. The note distinguishes this finite observation from an all-time result.

The practical implication: a 2-adic approach should track `mu(a)=2(log_9(2a+5)-1)` jointly with the pole defect, rather than treating v2(d-40a) growth as evidence of convergence to m=48.
