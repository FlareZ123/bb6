# Scalar forest for root32 ordinary shadows

For normalized shadows of denominator C=211 (source coordinates divided by 105), put S=U+2V=5+211m, s=(m+1) mod 2, B=211 floor(m/2)+108, U=2x+211(2+s), V=B-x-211(1+s). Work in x>0, V>422.

Both ordinary edge types reduce to:
    
    A=x+B; Q=A+211(A mod 2)
    d>=1; m'=m+3d+1; m' mod 2=A mod 2; 2^d x'=Q.

The domain is preserved and absence of a legal cost coincides with the ordinary forbidden leaf. All siblings share the identity 2^m' x'^3=2^(m+1)Q^3.

**Forest theorem.** For fixed child (m',x'), a candidate parent at cost d has m=m'-3d-1, x=2^d x'-B(m)-211(m' mod 2). Suppose two good parents have d1<d2. Then B1>=B2, and 2^d2 x'>=2*2^d1 x'>2B2+422(m' mod 2), whereas the second parent's domain implies 2^d2 x'<2B2+211(m' mod 2), contradiction. Equal costs uniquely determine both coordinates. Thus no cycles or merging. In particular, for accumulated cost <=P from mass m0, all states satisfy m0<=m<=m0+4P and 0<x<B(m), giving an O(P(m0+P)) bound on distinct nodes and edges for P>=1. This applies to aperiodic paths too, and is a numerical complexity bound, not a termination bound.

## Common affine root and finite fan
Let e=903171544+1761607680j. The common root is m=4e+78, x=211e+3852. Then 2x+633=B(m), m even. It has no incoming ordinary edge: cost 1 gives 2x=B-633 below the candidate parent's B-422; cost >=2 gives 2^d x>=2B-1266 while candidate parent base <=B-633, incompatible with the domain. The residual rays D,L,P descend along cost words:
- D: 2,2,2,1,3.
- L: 2,2,2,9,1,1,2,1.
- P: 2,2,2,9,3,1,3.

Their scalar (m0,x0,dx) triples, with m=m0+7046430720j and x=x0+dx*j, are D=(3612686289,79465868075,154995671040), L=(3612686322,273974307270,534378245520), P=(3612686327,74448864438,145210162020). The common root triple is (3612686254,190569199636,371699220480).

The finite fan is universal in j: for every internal affine ray compute Q0 and slope dx+743398440960. The exact valuation w=v2(Q0) is preserved for all j if the slope is divisible by 2^(w+1). Every allowed cost d<=w of correct parity produces the affine child by dividing Q0 and slope by 2^d. The full fan reaches only D,L,P or leaves with no legal cost. Therefore no infinite branch from D,L,P implies no infinite branch from the common root.

## Evidence and limits
Standalone Lean 4.36.0-rc2 compilation of ShadowScalar.lean succeeded locally: scalar_iff, step_good, decode_exists, incoming_unique, child_iff_not_bad, sibling_mass_cube, common_no_incoming, ray_cost_iff, ray_child_step, common_cut_checked, common_cut, source_ray_coordinates. The latter proves the six exact source affine coordinate identities. Only propext, Classical.choice and Quot.sound appear. The locally checked proof is being persisted separately; direct import into the accepted Root32ShadowRoot checker is still required. No CI or machine-level acceptance is claimed here. The key remaining problem is a uniform accumulated-cost cap within the root32 precision budget, not further periodic enumeration. BB(6) remains open.
