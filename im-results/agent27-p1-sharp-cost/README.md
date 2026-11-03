# Agent 27: sharp P1 inverse-cost / two-feeder dichotomy

**Status, 2026-11-03:** Universally quantified, Lean 4.36.0-rc2, source-connected *intermediate* result on the original P1 accelerated Turing machine. It neither proves P1 nonhalting nor determines BB(6), and external mathematical novelty has not been independently assessed. Keep in im-results/.

## Direct original-source theorem

Fix q>=1, P=2^(16q), u=7P-4q-3, and choose either of the two genuine feeder roots from Agent45's source-verified P1 n=16q+2 critical-root equivalence:

- **L0** = (4u-4, 4u+9), corresponding to root=true.
- **L1** = (6u-2, 2u+5), corresponding to root=false.

Take *any length* genuine Agent1Quarter.OddCone from that root to (b,d), with accumulated inverse cost m, b>=8, b%4=0 and d odd. Suppose the original Agent47P1.inverseAt b d t = some(k,c) has c>=2 even, k>=2, and **actual blank-entry** Agent1.Reach (2k-4) (c+4) holds. Then the final authentic-source theorem Agent27Budget.published_two_feeder_precise_cost_or_wall establishes:

    L0: (t=1 and b=4m+64q+12) OR (28P <= 3m+48q+16).
    L1: (t=1 and b=4m+64q+16) OR (28P <= 3m+48q+19).

The corollary Agent27Budget.authentic_two_feeder_nine_or_wall gives, in either case:

    (t=1 and b=4m+64q+delta) OR (9P < m),
    with delta=12 for L0 and delta=16 for L1.

This strengthens Agent9's source-certified non-wall **m>=8P** barrier, preserving the same affine-wall branch. The sharper explicit bound is approximately m>9.333P-O(q). Both statements require full source OddCone and genuine blank-entry reachability for their respective predecessor. No finite inverse-tree cap is used.

## Universal arithmetic mechanism

For n>=4 and arbitrary natural b,d,k,c,m,j,t with b>=8, b divisible by four, d odd, c>=2 even, assume the following exact constraints:

    b+d+2m+2n+13 = 14*2^n
    d+b/2+3 = 2^t*(c+3)
    2k+c+2t+1 = b+d
    2k+8 = 14*2^j

Then the pure, kernel-checked Agent27Budget.sharp_even_exit proves

    (t=1 and j+1=n and b=4(m+n))
    OR (7*2^n <= 3m+3n+7).

For root mass offset 2r, the generalization sharp_even_exit_shifted absorbs r into m: the affine wall becomes b=4(m+n+r) and the lower-cost alternative becomes 7*2^n <= 3(m+r)+3n+7.

The arithmetic argument splits the depth t=1 from t>=2 and the neighboring exponential indices j. It uses an explicit all-t bound 16t <= 6*2^t+8, plus the source inverse mass and dyadic power equalities. This source connects through unmodified Agent1Quarter.inverseAt_iff_power_mass, Agent1Quarter.odd_cone_mass and Agent1.even_left_power_shape. The two original feeder mass deficits are r=1 for L0 and r=2 for L1.

## Sharpness is arithmetic, not historical reachability

The inequality is *sharp under the stated pointwise equations*: for every k>=0, with U(0)=0, U(k+1)=4U(k)+2, set n=2(k+1), m=14U(k)+7-n, and

    (b,d,t,k_input,c,j) =
      (8, 56U(k)+21, 2, 21U(k)+10, 14U(k)+4, 2k+1).

The Lean theorem infinite_sharp_source_terminal proves that the actual unmodified inverseAt 8 (56U(k)+21) 2 evaluates to the displayed (k_input,c), the parameter satisfies the critical precursor mass identity, 2*k_input+8=14*2^j, and equality 7*2^n=3m+3n+7 holds. This is **not** a proof of an OddCone path from the critical root, nor of Reach for that even-right predecessor. An n=14 arithmetic instance is also certified in sharpness_n14.

Therefore the coefficient 7/3 cannot be improved under only these pointwise premises; further progress must exploit actual odd-cone history or stronger reachable-even-hub invariants. Synthetic terminal edges can satisfy necessary shape constraints while remaining unreachable.

## Exact source and verification

- Main standalone arithmetic source: P1Budget.lean.xz.b64, decompressed SHA256 1e21104d2350e8f3dd9f9662770dbafc096156baf078b57288ff78c7ce36abe1.
- Shifted-offset arithmetic: P1BudgetOffsetPure.lean.xz.b64, SHA256 336893c46393e36a80015720fda21a68e67cfce76e9bd5b3f83ed6e61dcbc5d7.
- Infinite sharpness certificate: P1SharpInfinite.lean.xz.b64, SHA256 3141b759bd9f1a88653b78d29b1cf1224384e4ed50033e132970557ecd7e3470.
- Original-source theorem bridges: P1BudgetBridge.lean.xz.b64 (SHA256 190f3310dc1e1ce55f644d20b94b512ea700488c33e4e6cd3b213a965c91f387), P1SharpInfiniteBridge.lean, P1BudgetTwoSector.lean, and P1BudgetTwoSectorBridge.lean.
- Authenticated original-source full arithmetic and two-feeder proof: [GitHub Actions 41716252786](https://github.com/FlareZ123/bb6/actions/runs/41716252786), successful. It compiles the unchanged original G, inverseAt, OddCone, Reach definitions. The final axioms are [propext, Classical.choice, Quot.sound], no sorryAx.
- The additional unmodified **Agent45 P1TwoSector.u2** cross-definition bridge is checked by manual CI in .github/workflows/agent27-p1-two-sector-bridge.yml, which compiles the full original P1TwoSector dependency chain. See workflow runs for completion state.
- The single-workflow source proof and sharpness audit is .github/workflows/agent27-p1-sharp-cost.yml; all workflows are manual dispatch only.

## Remaining research questions

The affine-wall case remains unresolved, as do non-wall odd histories of cost at least (28P-48q-O(1))/3 and the exceptional inverse input c=1. The n=16q+14 sector, and all other unresolved six-state machines, require separate proofs. A uniform cone-history bound excluding costs near 9.333P, or a stronger blank-root invariant for wall predecessors, would directly advance P1. Do not infer a BB(6) upper bound from this necessary-condition theorem.
