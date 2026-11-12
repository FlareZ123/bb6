# Agent 11: exact source-parent grammar for even-even sum-zero outputs

This is a reusable algebraic reduction from Agent3's already source-checked `section_preimage_all_iff` (`im-results/agent3-c-bounce-inverse/SectionAllInverse.lean`). It is **not yet a new Lean theorem** and does not decide blank-root reachability.

For any target `(x,y)` with x,y even, y>=6 and 8|(x+y), all source parents fall into exactly these alternatives:

1. `a=0,k>=2`, with odd n and
   `x+y=2^(n+3)`, `2*k+9+3*n=x+2*y`.
2. Direct/low parent:
   `a=x+y-2`, `k=(y-2)/2`.
3. `a>=2` even, `k>=1`, `2*k>a`, with odd n and
   `x+y=2^(n+1)*(a+2)`, `2*k+a+7+3*n=x+2*y`.

The a=1 and odd-a high-bounce branches are parity-impossible because they require the odd quantity x+y+1 to be an even power-of-two multiple. The a=0 and even-a bounce depths are both odd by the cost equation.

For the Machine C odd-t residual
`A_s=(130+208*s,94+152*s)`, let `S=28+45*s`. The a=0 branch is absent: S≡1 mod3 forces a hypothetical power-of-two exponent even, while S≡3 mod5 forces it 3 mod4. The complete algebraic parent list is:
- `L_s=(222+360*s,46+76*s)`;
- for each `r>=0` with `4^r|S`, writing `q=S/4^r`,
  `B_{r,s}=(2*q-2,155+256*s-q-3*r)`.

Thus the total number of incoming parents is `floor(v2(S)/2)+2`; for odd s there are exactly two, `L_s` and `B_{0,s}=(54+90*s,127+211*s)`.

**Arithmetic correction:** the even-a bounce cost is `2*k+a+7+3*n=x+2*y`, not `+9`; therefore the n=1 parent has right coordinate `127+211*s`, not `126+211*s`. Its right coordinate is odd iff s is even. Earlier parity deductions based on the old value are withdrawn.

Detailed derivation and the current open root branches are in `im-results/agent11-c-low58/M0EvenEvenSumZeroResidual.md`. The generic grammar is intended to help Machine C researchers replace the unresolved sum-zero case with a finite, explicit 2-adic parent fan. It is an intermediate result only: no blank-root closure or BB(6) bound follows yet.
