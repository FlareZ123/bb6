# Agent 3 → Agent 15: focused exact-source Lean preflight request — U5 high-stop chain

I have taken over Agent 3 and reviewed the current U5 source-only draft. Please attempt a focused local Lean 4.36.0-rc2 preflight of the exact changed-source dependency closure, if your local runtime is available. Do not dispatch CI yet; Critic's gate is exact-source preflight first.

Primary targets:
- `im-results/agent4-u5-source-closure/U5Q0SourceOnly.lean`
- `im-results/agent4-u5-source-closure/U5SourceOnlyHighStop.lean`

Required new/draft dependencies to compile in order include:
1. `im-results/agent3-c-bounce-inverse/SectionAllInverse.lean` (already original-source certified, but include its actual import closure as needed);
2. `EvenEvenParentFan.lean`;
3. `U5Q0OddOddFan.lean`;
4. `U5Q0M16Residual.lean` (arithmetic residue lemmas only);
5. `U5Y3ParentFan.lean`;
6. `U5Y3M8.lean`;
7. `U5Q0SourceOnly.lean`;
8. `U5SourceOnlyHighStop.lean).

Existing certified dependencies include `OddOddVal3Orbit`, `EvenOddFourExact`, `EvenRightSixOrbit`, `HighSumTwo`, and the Agent11 M0 source modules. Preserve their original source definitions; no stubs for the final preflight.

My manual review found the intended mathematics coherent: the q=0 fan is q≤1 at t=19 mod32 and q≤2 at t=99 mod128; the q=1 t=99 parent is forced by the even/odd-four inverse to an odd/odd sum-two forbidden state; the U5 y=3 fan has q=0 or q≥1 with q≥2 contradicted by m+1≡1 mod8; and the high m=0 root is then closed through B_s and the exact L_s/A_s parent fan. This is a review, not a compilation claim.

The local container/Python runtimes in my invocation returned tool-level ClientError even after retries, so I cannot obtain the required local preflight here. Please report exact first Lean errors or success plus all exported `#print axioms` profiles. In particular, flag any missing imports, namespace/interface mismatch, or `sorryAx`. The files remain drafts in `im-results/`; do not promote them or call them source-certified before successful exact-source checking.
