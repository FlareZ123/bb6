# M16 exclusions for residual Machine C stopping families

**Status:** intermediate integration result. The underlying Agent 43 modulus-16 quotient was kernel-checked by workflow run [41412951906](https://github.com/FlareZ123/bb6/actions/runs/41412951906) on 2026-11-02. The short wrapper importing its exported Reach-to-seen theorem for the families below has not yet been compiled in this directory; exact theorem names were requested from Agent 43.

## High-family exclusion

The high stopping family in ValSixJointFull.lean is

\[ H_{j,m}=(2j+3,\;2^{2m+2}(j+3)-(j+3m+5),\;0). \]

Take m=3 and j=8t+6, t>=0. Then

\[ a=2j+3=16t+15, \]
\[ k=2^8(j+3)-(j+14)=255j+754=2040t+2284. \]

Thus a mod16=15. If t is even, k mod16=12 and the Agent 43 quotient projection is q(a,k,0)=(15,12,0). If t is odd, k mod16=4; since k>=8, q(k)=8+(k-8) mod16=20, so q(a,k,0)=(15,20,0). Both (15,12,0) and (15,20,0) are absent from the independently reconstructed 24^3 quotient reachable set.

The Agent 43 quotient uses q(x)=x for x<8 and q(x)=8+(x-8) mod16 otherwise. Its independently reproduced BFS census is 7,115 abstract states and 34,992 representative edges. The checked bundle contains the generic quotient-soundness and original-source bridge modules (CQuotientSound16.lean, CSourceBridge16.lean); the successful workflow compiles them after all 24 P16Block files.

Therefore, by the checked Reach-to-seen invariant, no CLine source-reachable state can equal H_(8t+6,3). This is an infinite family of exact non-reachability statements, not a finite simulation bound.

The current highAllowedValSixFull j m predicate admits every (j,m)=(8t+6,3). The hand derivation is:

- In jointHighAllowed, j mod4=2 and j is even, so the j mod4 in {1,3} and odd-j clauses fail; the m>=4 and m=1 clauses fail.
- jointHighRectAllowed's added condition fails since m mod32=3.
- The four Agent 19 odd-special exclusions require j mod8 in {7,3,5,1}, while j mod8=6. Its universal n-condition has n<=4. For odd n, (2j+3) mod8=7, not 3. For even n, j+3m+3=8t+18 is 2 mod8, whereas 2^(n+2) is 4,0,0 mod8 for n=0,2,4.
- The four Agent 29 extra exclusions fail: the first three require m>=4, and the fourth requires m mod32=6.
- Agent 11's added conditions fail because j+m=8t+9 is 1 mod4, and j+m mod16 is 1 or 9, not 6.
- The Agent 19 Five condition fails since m mod16=3, not 10.
- The ValSix and ValSixThree extra restrictions require m>=4.
- The three final modular restrictions fail: j mod32 is 6,14,22,or30; j mod8=6; and m mod32=3.
- In the final affine-normalization condition, a+k=2056t+2299 is 3 mod4, so its first guard is false; normalization leaves k unchanged, and k>4.

Consequently, the exact full high criterion can be strictly strengthened by adding not (m=3 and j mod8=6). This removes an infinite arithmetic progression of high parameters that the current full criterion still admits. The predicate-admission derivation is hand-checked here; it still needs a Lean lemma.

## Low-family exclusions

The low stopping family is L_m=(1,2^(2m+3)-(3m+4),0), m>=1. For m mod16 in {1,5,7,9,13}, the Agent 43 quotient projection q(L_m) is respectively one of (1,9,0), (1,13,0), (1,23,0), (1,17,0), (1,21,0); all five quotient states are absent. The quotient projection is constant on each such m residue class because 2^(2m+3) is divisible by16 for m>=1 and the second coordinate remains >=8.

The other absent low residues are m mod16 in {4,12,14}; these are already excluded by jointLowAllowed (m mod8=4 or m mod16=14). The full low predicate also excludes m mod128=0. Thus the Agent 43 M16 quotient gives five clean new infinite low exclusions:

\[m\bmod16\in\{1,5,7,9,13\}.\]

## Integration action

Reuse Agent 43's already checked 24-cubed certificate rather than re-proving the quotient. Import its general reachable-state invariant and source bridge, prove the absent quotient states by computation, and add the high and low parameter restrictions to a new exact Machine C criterion. The communication requesting the exported theorem names is in communications/agent43/20261116T0800Z_agent42-reuse-m16-for-high-family.md.