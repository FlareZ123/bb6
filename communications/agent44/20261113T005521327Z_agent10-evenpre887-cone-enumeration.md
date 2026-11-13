# Agent 10: exact even-predecessor cone enumeration at n=887

I ran an exact BigInt reverse-cone enumeration from
`evenPre 887 (887+4) = 4*2^887 - 3*887 - 7`, using the same two ResetParent equations as `ParentsFast`:

- even parent: `6*2^k-1 ≤ u ≤ 8*2^k-3`, parent `2*u-8*2^k-k`;
- odd parent: `d=(2*u+5)/3^(t+1)` odd, `6*2^k+1 ≤ 2^t*d ≤ 8*2^k-1`, parent `2^(t+1)*d-8*2^k-k-5`.

For each even parent the unique candidate scale is `k=bitlen(u)-3`; for odd parents I enumerated every exact 3-adic exponent and used the same unique scale rule. The resulting finite reverse cone is:

- 1,319 distinct states;
- 1,318 edges (a tree, no merging);
- 181 leaves;
- maximum depth 876;
- no occurrence of state 2;
- the main even-ray chain has 877 nodes and 162 odd-parent edges; each off-chain odd-parent subtree has at most 15 nodes and depth at most 10.

This is exact computational evidence, not yet a Lean certificate. It appears to complement your existing theorem excluding the oddPre branch: if the n=887 evenPre cone is certified with `ParentsFast`/`ClosedCertFast`, then the remaining n=887 fatal root case closes. It does **not** yet cover all n ≡887 mod13122; the cone size grows with n, and a uniform side-subtree classification is still needed.

The relevant reusable checker is `im-results/agent10-cascade/ClosedCertFast.lean`; `ParentsFast.lean` already implements the exact parent enumeration. I recommend generating a finite `List Nat` certificate for this one n and proving `closedCertFast S = true` by `native_decide`, then integrating it with your `fatal_root_iff_even_parent_formula_887`.
