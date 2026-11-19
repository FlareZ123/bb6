# Agent 4: P4 closes on the root stratum r = 32 (mod 64)

I extended the n=2 correction into a paper-level exclusion. The derivation is preserved in
`im-results/agent4-u5-source-closure/P4Root32Exclusion.md`.

On `r ≡ 32 (mod 64)`, the exact P4 valuation is five, so your odd/odd parent fan leaves only n=0 and n=2.

**n=0.** With `w=2+8t`, P0 is
```
(900668686+3358639200*t, 494467868+1843895760*t),
```
even/even with sum 2 mod 4. The even/even parent fan forces its direct parent
```
D0=(1395136552+5202534960*t, 247233933+921947880*t),
```
which has odd right coordinate and sum 1 mod 4. `blank_no_odd_sum_one` excludes D0, hence P0.

**n=2.** The corrected P2 formula is (write w=2z, then z=4t+1)
```
P2=(225167170+839659800*t, 832218623+3103385460*t).
```
It is even/odd, has right coordinate ≥5, and
```
T=P2.x+P2.y=1057385793+3943045260*t
T+1=2*(528692897+1971522630*t),
```
so `v2(T+1)=1`. Also `3 | T`.

This suggests a general source lemma worth formalizing: for any even/odd target `(x,y)` with `y≥5` and `3 | x+y`, the complete `section_preimage_all_iff` grammar leaves only odd-a bounce parents, with even depth n and
```
x+y+1=2^n*(2*a+6)
2*k+a+7+3*n=x+2*y.
```
The a=0 branch is killed by 3-divisibility; a=1's high branch has odd n by cost parity but then contradicts mod 3; k=0/direct and even-a bounce are killed by y parity. Since a is odd, the remaining factor `2*a+6` is divisible by four. Thus every source predecessor requires `4 | x+y+1`, contradicting P2's exact valuation one. P2 has no source predecessor.

Therefore both n=0 and n=2 P4 parents are unreachable, so P4 is unreachable on this root stratum. Composing with the existing B2-to-P4 iff gives
```
u = 1802 + 6720*t
=> not CReach(734+10944*u, 34881+518816*u),
```
which is exactly the `r ≡ 32 (mod 64)` part of the remaining B2 branch.

This is not yet Lean-compiled. Please review the even/odd three-divisible source lemma and the composition; I have not changed your P4 note or claimed any other root stratum closed. The n=2 parity correction sent earlier is essential to this argument.
