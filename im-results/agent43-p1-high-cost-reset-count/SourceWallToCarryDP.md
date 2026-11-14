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

where s_j are the distinct increasing edge-start costs and e_j are the positive inverse-edge costs. At the original root, N≥1; for the restart formulation with d₀≤2·2^n−1, N≥0. The positivity check is short: the restart identity has
```
2^n·N = R − (d₀−1)/2,
R = 2^L(m₀+L+n+3) + (m₀+n+3)S + T > 0.
```
Since d₀ is odd and d₀≤2·2^n−1, we have (d₀−1)/2≤2^n−1, hence 2^n·N>−2^n. As it is an integer multiple of 2^n, N≥0. At the original root, (d₀−1)/2=1 and R≥n+3>1, so N≥1.

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

## 5. Corrected full-wall carry target and exact finite scan

An independent algebra audit found that the earlier version of WallFullDPTo10000.js checked the terminal carry against P+m+n+2. This is one too small. From the source wall identity,

    1 + 7·P·S = P·2^m + ∑_{s∈A}(n+3+s)2^s + (n+3+m)2^m,

put Q=7P−(n+3) and T=∑s·2^s. Rearranging gives the exact full-wall equation

    ∑_{s<m}(Q−s)2^s = 2^m(P+m+n+3) − 1.

The implemented recurrence subtracts target bit 1 at each of the m positions, so after m bits its carry is `(sum−(2^m−1))/2^m`. From the full-wall equation this is `P+m+n+2`, one less than the coefficient `P+m+n+3` before the low all-ones word is removed.

I independently reran the modular subset DP for every 14≤n≤10000: it returns a nonempty terminal state only for

    (30,8), (286,88), (350,112), (1614,563), (2990,1068), (3342,1145),

where each pair is (n, minimum number of adjacent gaps 1 or 2). I then reran the BigInt full-wall scan for all six candidates with the corrected +3 carry. The results are unchanged: no exact carry hit, and the state sets become empty at m=82, 1442, 586, 5824, 6154, and 13730 respectively. Once the state set is empty at m₀, no terminal cost m≥m₀ can work, because restricting any candidate subset to positions below m₀ would already have to satisfy the impossible low-m₀-bit condition.

Thus the exact finite computation still excludes the shifted wall for all 14≤n≤10000, conditional on the source modular reduction (whose root identity is kernel-checked). The +2 error affected the exact-hit diagnostic but not the final finite exclusion; the corrected +3 computation independently confirms no hits. This remains a finite computational result, not an unbounded P1 exclusion.

## 6. Arbitrary restart roots after a high-depth edge

The same telescoping calculation is not limited to the original root. Let a restart state be (b₀,d₀,m₀), let L be the remaining relative cost to the wall, and put c=m₀+n. The source mass invariant at the restart is

    b₀+d₀+2c+13 = 14P,   P=2^n.

For each subsequent inverse edge with relative start s_j and cost e_j=t_j+1, the unchanged-source inverse equations give

    (d_j−1)+14P = 2^{e_j}(d_{j+1}−1) + 2(s_j+c+3).

Multiplying by 2^{s_j} and summing telescopes. With S=∑2^{s_j} and T=∑s_j2^{s_j},

    d₀−1 + 14P·S = 2^L(d−1) + 2((c+3)S+T).

At the shifted wall in absolute cost m₀+L,

    b+4L+4c+20 = 12P,

and the endpoint mass equation gives d=2P+2L+2c+7. Substitution and division by two yield Agent 50's restart identity:

    P(7S−2^L) = 2^L(L+c+3) + (c+3)S + T − (d₀−1)/2.

Since L=∑e_j and s_{j+1}=s_j+e_j, the same telescoping of powers gives

    N := 7S−2^L = −1 + ∑_j(8−2^{e_j})2^{s_j}.

For a restart immediately after a depth-≥3 edge, the defect bound recorded in HighDepthRestartPotential.md gives F'≥P/4−6, with F'=2P−d'−5. Hence d'≤7P/4+1. In particular (d₀−1)/2≤7P/8, and also d₀≤2P−1 for P≥8. The positive part
R=2^L(L+c+3)+(c+3)S+T
is strictly positive, so P·N=R−(d₀−1)/2>−7P/8>−P. It is an integer multiple of P, hence N≥0.

The last-shallow-edge argument in §3 therefore applies after every such high-depth restart: the suffix must contain a shallow edge, the last edge whose cost differs from 3 must be shallow, and every edge after it has cost exactly 3. This is a paper derivation from the exact source recurrence and the existing defect bound. The general restart identity and the resulting suffix theorem have not yet been added as Lean theorems; formalizing them is a high-value next step.

## 7. Exact initial energy at a high-depth restart

The existing five-shallow source model starts its depth-two prefix at the original root, where its affine energy is

    I(P,W₀,B₀)=98P−(14n+92).

For a general restart state (b₀,d₀,m₀), using the same coordinates
W₀=b₀+4m₀+4n+20 and B₀=m₀+n+6, the restart mass equation gives

    W₀ = 14P−d₀+2m₀+2n+7,
    I(P,W₀,B₀) = 98P−49d₀−14(m₀+n)+55.

Thus the exact remainder replacing 14n+92 is

    D₀ = 49d₀+14(m₀+n)−55.

A depth-two prefix of length s still divides I by 8^s, so the generalized source model would need to control 98P−D₀ (including its sign) and the divisibility of D₀. The high-depth defect bound d₀≤7P/4+1 controls the d₀ term, but by itself does not ensure D₀<98P when m₀ is large. This is the precise obstacle to reusing FiveShallowSourceModel.lean unchanged after a high-depth restart. A useful next step is to derive a sharper joint bound on m₀ and d₀ from the high-depth transition and the remaining wall suffix, then generalize the five-shallow affine barrier with that bound.

### Combining the restart defect with the terminal suffix bound

Under the five-shallow hypothesis, the terminal suffix bound also controls the restart cost m₀. If the last shallow edge has cost 1, then m+n+3<93P/128; if it has cost 2, then m+n+3<77P/256. Since m₀≤m, this gives m₀+n<CP with C equal to the corresponding constant. Combining with d₀≤7P/4+1:

- for last shallow cost 1, D₀< (6139/64)P−6, hence I₀=98P−D₀>(133/64)P+6;
- for last shallow cost 2, D₀< (11515/128)P−6, hence I₀>(1029/128)P+6.

So the joint high-depth/terminal-suffix hypotheses do give a substantial positive restart energy, not merely I₀>0. The remaining issue is the dyadic scaling: from I₀<98P and 8^s∣I₀ one gets only 3s≤n+6, whereas the existing FiveShallowSourceModel proof uses 3s≤n to write P=8^s·p with integral p and apply root_two_prefix_divisor. A generalized barrier may be possible with a six-bit slack, or by proving the stronger divisibility 8^s∣P from the exact high-depth congruence. This is a concrete route to extend the five-shallow theorem beyond the original root.

### High-depth congruence available for the six-bit slack

If the restart state is the child of a depth-t edge, then d₀−1=c+3 is divisible by 2^t. Also t≤n+1, since the inverseAt mass term is at most 14P and c+3≥4. Substituting d₀=1+2^tq into the restart energy gives the exact congruence

    I₀ = 98P−49d₀−14(m₀+n)+55
       ≡ 2(3−7(m₀+n))  (mod 2^t).

Thus, whenever 3s≤t for the following depth-two prefix, the divisibility 2^{3s}∣I₀ forces 2^{3s−1}∣(3−7(m₀+n)). Since the terminal suffix bounds put m₀+n<P, the nonzero integer 3−7(m₀+n) has absolute value below 7P<2^{n+3}; this gives an explicit congruence restriction on m₀+n but does not by itself close the scaling gap. The remaining case 3s>t is also unresolved. This is a useful arithmetic constraint for a sharper restart-prefix argument, not yet a proof of the needed 3s≤n.
