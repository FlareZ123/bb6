# Source-wall to carry-DP bridge (proof sketch; Finset source theorem pending)

This note records the exact interface between the merged source theorem and Agent 50's dyadic carry obstruction. It is deliberately split into what is already kernel-checked and what remains conditional on PR #99.

## 1. Kernel-checked root identity

WallTelescopingSource.lean on main proves, for every original P1 CountCone history reaching the shifted wall,

    1 + 7·2^n·S = 2^n·2^m + Ufull.

The proof is source-level: it inducts on the original CountCone constructors and uses the exact inverse-transition equivalence and source mass invariant. The public theorem returns existential natural aggregates S and Ufull. It does not yet expose the underlying finite cost set in its theorem statement.

## 2. Intended finite-set representation

PR #99 (not yet kernel-verified) strengthens the source induction to return a finite set A of edge-start costs, with:

- every s∈A satisfies s<m;
- A=∅ when m=0;
- 0∈A when m>0;
- S=∑_{s∈A}2^s;
- U=∑_{s∈A}(n+3+s)2^s.

Because the edge-start costs strictly increase, the Finset insertion is legitimate: each new start mp is strictly larger than all starts already in A.

Define B=insert m A. Then m∉A, B is exactly the set of all edge-start costs together with the terminal cost m, and 0∈B. The finite-set wall identity is:

    1 + 7·2^n·(∑_{s∈A}2^s)
      = 2^n·2^m + ∑_{s∈B}(n+3+s)2^s.

Reducing modulo 2^n immediately gives:

    ∑_{s∈B}(n+3+s)2^s ≡ 1 (mod 2^n).

Now let C=B∩{0,…,n−1}. Every discarded s≥n contributes a multiple of 2^n, so:

    0∈C,   C⊆{0,…,n−1},
    ∑_{s∈C}(n+3+s)2^s ≡ 1 (mod 2^n).

This is exactly the finite modular-subset condition used by Agent 50's carry DP. It is not an extra heuristic assumption: once PR #99 is checked, it follows from the original source path and the wall equation.

## 3. Last non-depth-two edge argument

Agent 50's wall_cost_telescoping.md derives the integer identity

    N = -1 + ∑_j (8−2^{e_j})·2^{s_j},

where s_j are the distinct increasing edge-start costs and e_j are the positive inverse-edge costs. At the original root, N≥1; for the restart formulation with d₀≤2·2^n−1, N≥0.

The suffix conclusion follows from this identity and the distinct-start bound:

    ∑_{s∈F} 2^s ≤ 2^r−1

for any finite set F of distinct nonnegative integers strictly below r.

- If there were no shallow edge (e_j≤2), then every coefficient 8−2^{e_j} would be nonpositive, giving N≤−1, contradiction.
- Let j be the last edge with e_j≠3. If e_j≥4, then its contribution is at most −8·2^{s_j}; all later contributions vanish because e=3. Earlier high-depth contributions are nonpositive. Earlier shallow contributions are at most 6·(2^{s_j}−1). Hence

    N ≤ −1 + 6(2^{s_j}−1) − 8·2^{s_j} < 0,

again a contradiction.

Therefore the last edge whose cost is not 3 must be shallow (cost 1 or 2), and every subsequent edge has cost exactly 3 (depth two).

The finite-set representation in PR #99 supplies the distinct-start structure needed to formalize the bound on earlier powers. The depth trace still needs to be exposed by the source induction for a fully kernel-checked suffix theorem.

## 4. What is and is not established

- **Proven and merged:** original-source natural weighted-sum invariant and root shifted-wall identity; Lean axiom audit has no sorryAx.
- **Draft, awaiting a manual CI dispatch:** Finset-valued source invariant and finite-set wall identity in PR #99. Its first CI attempt stopped at a missing open scoped BigOperators; that scope and a subsequent algebra-order issue were fixed on the branch. Do not treat the Finset theorems as checked yet.
- **Paper derivation from Agent 50's identity:** last non-depth-two edge must be shallow; the suffix after it consists entirely of depth-two transitions.
- **Still needed:** expose the depth trace in Lean, formalize the modular reduction to C, and connect the exact carry DP's empty-state certificate to a source-level P1 wall exclusion.

## References

- im-results/agent43-p1-high-cost-reset-count/WallTelescopingSource.lean
- im-results/agent50-p1-dyadic-width/wall_cost_telescoping.md
- im-results/agent50-p1-dyadic-width/wall_modular_obstruction.md
- im-results/agent50-p1-dyadic-width/small_index_wall_dp.md
- PR #99 branch: agent43-wall-telescoping-finset-20261113 (unverified)
