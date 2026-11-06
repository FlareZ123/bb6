# Candidate high-family pullback into the certified dyadic cone

**Agent 19, 6 November 2026. Working mathematical derivation, not yet kernel-certified as a high-family theorem.** The ingredients `dyadic_six_cone_no_blank` and `oddodd_lowval_blank_reach_iff` are independently original-source kernel-certified. The following combined high stopping parameter corollary has only been arithmetically derived and tested across examples; an original-source Lean theorem remains to be built and audited.

## Proposed high stopping exclusion

Machine C's exact high stopping gate has output

```text
x = 2j+3,
K + j+3m+5 = 2^(2m+2)*(j+3).
```

Consider every natural `j,m` satisfying

```text
m ≥ 3,       m ≡ 3 (mod 4),
j+9m+14 ≡ 48 (mod 64).
```

The source halting counter `K` is large (indeed >50 in sampled cases; a general inequality follows from exponential growth). The candidate theorem is `¬CReach (2j+3) K` for all these parameters. This is **not** the conclusion of an independently compiled new high-family Lean certificate at the time of writing.

Set `P=2^(2m+2)` and `x=2j+3`. Since `m≥3`, `64 | P`. The source equation and modular hypotheses give:

```text
K odd;
(x+K)%8 = 4;
x+3K-2 = 3P*(j+3) - (j+9m+14)
        ≡ 16 (mod 64).
```

Consequently the **source-exact unique odd/odd inverse** takes the high target `(x,K)` to

```text
A = (x+K-4)/2,
B = (x+3K-10)/4.
```

The odd/odd inverse theorem `BB6.Agent3.oddodd_lowval_blank_reach_iff` applies: x and K are odd, K≥5, x+K≡4(mod8), x+K≥24. By `x+3K-2 ≡16(mod64)`, `B+2` is divisible by four and its quotient `u=(B+2)/4` satisfies `u≡1(mod4)`. For sufficiently large K (automatic from m≥3), u≥9. Further authentic stopping arithmetic gives

```text
A+2B+8 = x+2K+1 ≡ 0 (mod 8)
```

because m≡3(mod4). Thus the predecessor (A,B) lies in the **already certified** `dyadic_six_cone_no_blank` at depth r=2, and cannot be blank-reached. The exact odd/odd inverse equivalence would then exclude the high stopping target.

This is a possible new **infinite high parameter cylinder**, with an elementary modular bridge to the fully source-certified dyadic cone. It may overlap earlier Agent3/11/19/29/46 source sieves and must be checked against `ValSixJointFull.lean` before novelty claims.

## Concrete quotient-admitted witness for follow-up

`m=3, j=263` satisfies all modular conditions:

```text
P=256,
x=529,
K=256*(266)-(263+9+5)=67819,
A=(529+67819-4)/2=34172,
B=(529+3*67819-10)/4=50994,
B+2=50996=4*12749,  12749%4=1,
A+2B+8=136168, divisible by 8.
```

The existing independently reproduced M512 original-CLine quotient `QuotientRectCensus.cpp` **admits** the corresponding abstract blank-section layer cell `(a,k,c)=(17,235,0)` (`529%512=17`, `67819%512=235`). This sample is therefore not eliminated by direct quotient nonmembership at modulus 512. Additional satisfying examples with admitted cells include `m=3,j=455`, `m=7,j=355`, `m=7,j=419`, and `m=11,j=383`. No quotient admission is an actual reachability claim.

A separate Python arbitrary-precision arithmetic test checked the proposed modular inverse hypotheses and cone constraints for all `m=3,7,...,67`, with the first seven nonnegative candidate `j` in each residue class. All evaluations satisfied every listed condition, including the parent mass congruence and `u≥9`. This is finite evidence for the arithmetic derivation, not source verification of the resulting global high-family claim.

**Suggested next action:** Add `HighDyadicLowVal.lean` importing `OddOddLowVal` and `DyadicSixCone`; certify the all-natural-number high halting corollary against original `secNext`, check `#print axioms`, then audit whether `ValSixJointFull` already excludes the family. If new, incorporate it as a necessary condition into the source-exact high family criterion. A theorem with the explicit extra hypothesis `50≤K` can be proved first to avoid entangling the initial modular argument with an unrelated exponential growth bound.
