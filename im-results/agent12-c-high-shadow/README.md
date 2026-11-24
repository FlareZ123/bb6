# Machine C high-stop negative-shadow first-parent bridge

For high stopping parameters j,m with 2 <= j <= 3m and m >= 2, put b=2m+2, E=2^b(j+3), x=2j+3, y=E-(j+3m+5), o=(3m+2-j) mod 2, and c=3m+2-j-o. Then x+y+o=E-c and x+2y=2E-6m-7.

For any certified valuation v=v2(c), v+1<=b, the equations give the exact valuation of the positive rounded mass x+y+o and exclude the pure-power case. The complete source-parent grammar covers every reachable parent. Shadows (actual parent coordinate PLUS shadow coordinate divisible by the specified power of two) are:

* Direct parent (when y even): (3m+4-j,(j+3m+7)/2), precision b-1.
* High bounce depth n, for all n+2<=v with n mod2=o: A=c/2^(n+1)+2+o, B=(6m+14+3n-A)/2, precision b-(n+2).

The validity equations are checked on small integers. Every accepting child checker certifies its corresponding actual parent unreachable. An all-child accepting highCheck excludes the stopping target without constructing E. No cutoff on source bounce depths is used.

HighShadowArithmetic.lean compiled standalone with Lean 4.36.0-rc2; the five exported theorems have only standard axioms. highCheck_sound is proved under explicit ParentContract and ShadowContract premises, neither asserted as an axiom. HighShadow.lean instantiates the contracts with Agent13's source parent and negative-shadow lemmas; complete source compilation remains pending due local GitHub DNS failure.

Local interpreted Lean evaluation of the copied negative-shadow checker accepts (j,m)=(4,25),(5,49),(8,5),(2,16) with fuel 20; none is rejected by the four-sector filter. These are not novelty claims against all earlier high sieves. At m=256, fuel 514, 758 of 767 j in 2..768 accepted. Nine remain unresolved. This is a feasibility test, not an unbounded parameter result. A failed certificate is not evidence of reachability. The restriction j<=3m is deliberate; the complementary high region and small left coordinates require different bridges.

Reuse Agent13's existing source workflow. No new CI workflow created. Next mathematical target: signed-shadow extension and a termination/precision bound, rather than longer scans.
