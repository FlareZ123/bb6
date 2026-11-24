# Machine C: signed-residue all-parent cone certificates

## Strongest method (SignedCone.lean and HighSigned.lean)

Represent the authentic section counters as x=P A+u, y=P B+v, P=2^b, where A>=0, B>=1, and either A>=1 or u>5. Offsets u,v are arbitrary signed integers. The executable checker never evaluates A or B. Its guard 2(|u|+|v|+8)<P ensures x>5, y>=8 and the rounded sum Q>P/2. With o=(u+v) mod 2, exact nonzero valuation w of u+v+o and w+1<=b, the source Q has valuation w and is not a pure power. The existing necessary parent grammar therefore enumerates all reachable parents.

Each direct edge (when v even) charges one bit, updates offsets to (u+v-2,(v-2)/2), and leading coefficients to (2(A+B),B). Each high depth n charges n+2 bits, with n+2<=w and the correct parity; update signed offsets

    u' = (u+v+o)/2^(n+1)-2-o
    v' = (u+2v-u'-7-3n)/2,

and coefficients

    A' = 2(A+B)
    B' = 2^(n+1)(A+2B)-(A+B).

Both leading coefficients remain positive. Exact small-integer validity tests ensure integral child offsets. The checker accepts only if all admissible children accept, or if the actual odd-right forbidden-image residue is reached. Thus a finite branching tree certifies unreachability for **all** leading coefficients compatible with the representation. SignedCone.check_sound proves this under explicit ParentContract and forbidden-image premises. It is not restricted to positive negative shadows.

For high stop parameters j>=2,m>=2, take b=2m+2, A=0, B=j+3, u=2j+3, v=-(j+3m+5). Alternatively choose any r<=b, center these offsets modulo 2^r, and use adaptiveExcluded. The source stopping equation implies y>=2^b, so the centered residue representation is sound at every admissible precision; no triangular condition j<=3m remains. Smallness and exact valuation still determine whether a certificate accepts, and the pure-power residual case is not decided by this method.

The adaptive checker is periodic in a **coupled lattice**, with sufficient nonnegative parameter displacements U,V satisfying

    2^r | 2U,    2^r | U+3V.

This lifts entire branching predecessor trees, not only forced chains. At (j,m)=(40,5), r=10, both possible first parents have forbidden odd-right residues. Lean kernel reduction checks adaptiveExcluded 2 10 40 5=true; the general lattice theorem gives

    adaptiveExcluded 2 10 (40+512t) (5+512t)=true    for every t>=0.

The seed is outside j<=3m and survives the four-sector single-parent normalizer. This is not a claim that it survives every earlier integrated high sieve. The generic checker soundness and this infinite branching family are the substantive deliverables, rather than a list of isolated residue counts.

## Verification boundary

SignedCone.lean and HighSigned.lean compiled locally against the independently compiled HighShadowArithmetic.lean, with Lean 4.36.0-rc2. All seven printed theorem profiles contain only standard axioms. HighSignedSource.lean instantiates the actual parent grammar and forbidden-image theorem from Agent13's existing AffineConeLowStop import closure. Its exact source compilation is pending (local shell has no GitHub DNS access). No new CI workflow was created. Reuse Agent13's existing source closure. Do not count the original-source corollaries as source-certified until they compile.

## Earlier positive-shadow bridge

HighShadowArithmetic.lean also provides the first-parent negative-shadow specialization for 2<=j<=3m. Let E=2^(2m+2)(j+3), o=(3m+2-j) mod 2, c=3m+2-j-o. Then x+y+o=E-c and x+2y=2E-6m-7. The direct shadow is (3m+4-j,(j+3m+7)/2), high depth n shadow is (C,(6m+14+3n-C)/2) with C=c/2^(n+1)+2+o. The arithmetic proof compiled standalone; HighShadow.lean's actual NegativeShadow source instantiation is pending. Local interpreted evaluation of copied checker definitions accepted 758/767 j at m=256, leaving nine unresolved. That finite scan was a feasibility diagnostic and not a global proof.

## Remaining mathematical gap

The signed cone covers a wider unbounded parameter domain and provides a proof-carrying all-parent certificate, but not a universal termination or precision bound. The unresolved high and low parameter existentials remain unbounded. A naive universal negative-shadow termination theorem is false: the direct shadow at right coordinate 2 has an infinite direct path (x,2)->(x+4,2). Whether reachable from specific parameter domains requires separate analysis. The pure-power rounded residue and small original left-coordinate cases also need separate treatment. No Machine C or BB(6) decision is claimed.
