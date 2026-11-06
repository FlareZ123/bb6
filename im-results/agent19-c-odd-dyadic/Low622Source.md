# Machine C: seven forced authentic inverse returns exclude a quotient-admitted low halting family

**Agent 19, 6 November 2026.** This is intermediate mathematical research toward BB(6). Machine C and BB(6) remain open. The original-source Lean certificate is [Low622Source.lean](Low622Source.lean); verification status is tracked below.

## Uniform infinite true-blank exclusion

Let `CReach x y` mean that the authentic Machine C section map `BB6.Agent46.secNext`, starting from the exact blank-entry section `(5,1)`, reaches `(x,y)` after some finite number of section steps.

The proposed theorem is

```lean
BB6.Agent19Low622.blank_no_one_622_mod1024 (q : Nat) :
  ¬ BB6.Agent3.CReach 1 (1024*q+622)
```

It is stronger than an exclusion of halting-gate parameters: it forbids **every** right counter in the complete cylinder `622 mod 1024`, for arbitrary nonnegative `q`, all times, without assuming the halting equation. Its inverse ancestry comes exclusively from existing source-exact *blank-reachability iff* lemmas, rather than finite quotient simulation.

| Inverse node | x | y | Source-certified forced predecessor |
| --- | --- | --- | --- |
| R0 | 1 | 1024q+622 | sum-seven odd/even gate |
| R1 | 1024q+621 | 512q+310 | even-right six-class gate |
| R2 | 1536q+929 | 256q+154 | even-right six-class gate |
| R3 | 1792q+1081 | 128q+76 | affine even-right gate |
| R4 | 1920q+1155 | 64q+37 | odd/odd valuation-two-or-three gate |
| R5 | 992q+594 | 528q+314 | even-right six-class gate |
| R6 | 1520q+906 | 264q+156 | even-right six-class gate |
| R7 | 1784q+1060 | 132q+77 | forbidden original-section image |

Every source gate holds **uniformly for all q≥0** and transports genuine blank reachability backwards to the next row. At R7 the right counter is odd and at least 77, while the sum is `1916q+1137 ≡ 1 (mod 4)`. The original `BB6.Agent3.blank_section_odd_image` theorem says a post-initial source section with odd right counter at least five can have sum residue only zero or three modulo four. The genuine initial section is `(5,1)`, which differs from R7. Consequently R7 is blank-unreachable, and the seven equivalences propagate the contradiction to R0.

The original low stopping equation is `k+3m+4=2^(2m+3)`. For `m%1024=474`, the power is divisible by `1024`, and arithmetic forces `k%1024=622`. Thus

```lean
BB6.Agent19Low622.low_m474_mod1024_unreachable (m k : Nat)
  (hm : m%1024=474)
  (hgate : k+3*m+4=2^(2*m+3)) :
  ¬ BB6.Agent3.CReach 1 k
```

The new class survives all restrictions in the existing source-checked `Agent11Joint.lowAllowed` predicate: it has `m%64=26`, `m%16=10`, `m%8=2`, `m%128=90`. The other forbidden residues in `Agent3.jointLowAllowed` reduce to different residues modulo 1024. This gives an additional necessary condition `m%1024 ≠ 474` for an authentic low-gate halting witness. This does not exclude the second stopping family or the infinitely many other first-family parameters.

## Independent M512 overapproximation check

Using the complete original nine-case `BB6CLine.nextC` quotient algorithm already documented in [QuotientRectCensus.cpp](QuotientRectCensus.cpp), independently rebuilt locally at `M=512`, the reachable abstract CLine layer contains the cell `(a mod512,k mod512,c=0)=(1,110,0)`. The graph had exactly **27,858,704** abstract reachable vertices and **221,572,376** representative edges, matching the prior census. Since `622%512=110`, the new all-time source exclusion cannot be read off from nonmembership of this cell in that quotient. Abstract reachability is an overapproximation and is never evidence of genuine blank reachability.

## Verification and limits

The proposed Lean 4.36.0-rc2 source was typechecked locally against **matching declaration signatures** for the already source-verified inverse lemmas, and printed no `sorryAx`. This local mock does **not** establish original-source certification. The manually dispatched [full unchanged-source workflow](../../.github/workflows/agent19-c-odd-dyadic.yml) compiles `Low622Source.lean` after the authentic original modules; treat the named result as provisional until its workflow is successful and the final axiom report contains only standard kernel axioms. All numerical quotient findings are independently reproducible finite computation, not part of the Lean theorem.

The source certificate is based on seven forced returns and a pre-existing global odd-image impossibility. No assertion of external academic originality, complete Machine C nonhalting, a Busy Beaver champion, or a universal upper bound is made.
