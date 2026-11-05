# Fatal-index 3-adic density and synthetic odd first-reset fan-in

**Agent 7, 2026-11-05.** Intermediate result for six-state #746, exact table `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`. The blank-tape halting question remains open. The theorem concerns hypothetical predecessor **heights**, not predecessors known to occur on the authentic blank-root orbit. No BB(6) bound follows. External mathematical novelty is unassessed.

## Kernel-checked 3-adic residue theorem

Let

\[
F(n)=4\cdot2^n-n-4,\qquad Z(n)=2F(n)+5=8\cdot2^n-2n-3.
\]

The two surviving fatal-index sectors are `n=s+6j` for `s=4` or `5` and `j\ge0`. The checked-in [FatalHenselResidue.lean](FatalHenselResidue.lean) defines a computable ternary lifting residue `liftResidue s k` and proves, for every `k,j\in\mathbb N`,

\[
0\le b_{s,k}<3^k,\qquad
3^{k+1}\mid Z(s+6j)\quad\Longleftrightarrow\quad
j\equiv b_{s,k}\pmod{3^k},
\qquad b_{s,k}:=\operatorname{liftResidue}(s,k).
\tag{1}
\]

The residue is unique. Its digit recursion is

\[
b_{s,0}=0,\qquad
b_{s,k+1}=b_{s,k}+3^k\left(\frac{Z(s+6b_{s,k})}{3^{k+1}}\bmod3\right).
\]

The quotient is integral because the previous lift satisfies (1). **This is a source-linked all-index result**, invoking earlier independently proved [FatalValuationExact.lean](../agent7-cascade-forward/FatalValuationExact.lean) lemmas `fatal_shift_balance`, `fatal_shift_exact` and `fatal_shift_keeps_divisibility`. The local Lean 4.36.0-rc2 test with *exact theorem-signature stubs* passed the new proofs, but the dependency stubs in the local test make this **not yet an unchanged-source verification**. An original-source check was requested through the manual [agent7-746-uniform-fatal-parent workflow](../../.github/workflows/agent7-746-uniform-fatal-parent.yml) via [issue #23](https://github.com/FlareZ123/bb6/issues/23). Upgrade this provenance only after the corresponding CI succeeds, with standard-axiom audit.

### Derivation of the density, from (1)

For every fixed `k>=1`, the successful `j` form exactly one residue class modulo `3^(k-1)`. Counting integers in residue classes gives the exact natural density, separately in either surviving sector,

\[
\operatorname{dens}\{j\ge0: v_3(Z(s+6j))\ge k\}=3^{1-k}.
\tag{2}
\]

Equivalently, the valuation has limiting geometric law `Pr(V=k)=2*3^(-k)` for `k>=1`. The unique-residue theorem is Lean checked against the earlier source interfaces; this density consequence is a conventional paper derivation using elementary counts of periodic subsets. It has **not** been separately formalized as a Lean density theorem.

The first residues `b_(s,k)` for `k=0,1,...,7`, as independent arithmetic diagnostics, are:
- `s=4: 0,0,3,21,48,48,534,1263`.
- `s=5: 0,0,0,0,0,81,81,81`.

## Paper consequence: limiting distribution of odd inverse fan-in

Agent 10's fully proved [FirstInverseComplete.lean](../agent10-cascade/FirstInverseComplete.lean) gives the exact first-reset `ResetParent` grammar. Agent 44's [ExactOdd.lean](../agent44-746-fanin/ExactOdd.lean) proves distinct admissible odd valuation labels give distinct source-genuine parent heights, and [ExactCount.md](../agent44-746-fanin/ExactCount.md) relates labels to dyadic bands.

Write `A(n)` for the total number of **distinct odd-arm source-genuine immediate predecessor heights** of fatal reset `F(n)`. For a fixed odd valuation parameter `t\ge0`, the source grammar permits this label only when `3^(t+1)|Z(n)` and `q_t(n)=2^t Z(n)/3^(t+1)` lies in a source odd dyadic band `6*2^h+1 <= q <= 8*2^h-1` for some `h>=1`, or the isolated `q=7` case.

For each *fixed* `t`, as `n\to\infty` among indices with `3^(t+1)|Z(n)`, the strict band indicator eventually stabilizes to

\[
e_t=2+\operatorname{bitlen}(3^{t+1})-\operatorname{bitlen}(3^{t+2})\in\{0,1\}.
\tag{3}
\]

**Proof of stabilization.** Since `Z(n)=8*2^n-2n-3`, the scaled input `q_t(n)/2^n` tends to `2^(t+3)/3^(t+1)`. Membership in an odd band becomes membership in one of the *open* scaled intervals `(6*2^m,8*2^m)`, for integral `m=h-n`. This fixed rational limit is never an endpoint, by unique factorization, so for sufficiently large `n` its band membership is stable. Comparing `3^(t+1)` with its bounding consecutive powers of two reduces this open-band test to (3). The isolated `q=7` cannot occur for sufficiently large `n` at fixed `t`.

Let `T_r` be the `r`th index `t` with `e_t=1`, starting with `r=1`. These are

\[
T_1,T_2,\dots=1,3,6,8,11,13,15,18,20,23,25,27,30,32,35,37,\dots
\]

For each **fixed** positive `r`, there is a threshold `N_r` so that for every `n>=N_r` in either surviving sector,

\[
A(n)\ge r\quad\Longleftrightarrow\quad3^{T_r+1}\mid Z(n).
\tag{4}
\]

The forward implication is justified by applying the stabilized indicators to the *finite* set of earlier labels `t<T_r`. When the divisibility holds, the first `r` eventually admissible labels supply distinct parents. This works even if `v_3(Z(n))` itself is arbitrarily large. Combining (2) and (4) gives, for each sector separately, the precise limiting tail and point distribution

\[
\boxed{\operatorname{dens}\{A(n)\ge r\}=3^{-T_r}\quad(r\ge1)}
\]

\[
\operatorname{dens}\{A(n)=0\}=\frac23,\qquad
\operatorname{dens}\{A(n)=r\}=3^{-T_r}-3^{-T_{r+1}}\quad(r\ge1).
\tag{5}
\]

For example, the first six limiting tail probabilities are `1/3,1/27,1/729,1/6561,1/177147,1/1594323`. The formula for the stabilized indicators telescopes exactly:

\[
\sum_{t=0}^{m-1} e_t=2m+2-\operatorname{bitlen}(3^{m+1})
  =(2-\log_2 3)m+O(1).
\]

It follows that `T_r=r/(2-log_2(3))+O(1)`, giving exponentially decaying limiting fan-in tails `3^(-r/(2-log_2(3))+O(1))`. This clarifies why arbitrarily large hypothetical parent fan-in proved by Agent 44 is consistent with an extremely sparse large-fan-in distribution.

The **expected odd-parent count of the limiting distribution**, distinct from a yet-to-be-proved limit of raw finite-prefix empirical means, is

\[
\mathbb E_{\mathrm{lim}}A=\sum_{r\ge1}3^{-T_r}
=0.37190087309950323\ldots.
\]

The first 15 summands have exact rational sum `18606775304835163/50031545098999707`; the remainder is at most `3/(2*3^36)<10^(-17)`. The unique even reset predecessor for every `F(n)` with `n>=4` adds one to the limiting total first-reset in-degree, giving limiting expected total `1.37190087309950323...`. The finite-prefix mean has **not** been proved to converge to that value.

## Boundaries and next research use

- (1) is a local Lean 4.36.0-rc2 theorem whose real-source integration is awaiting its CI verdict. (2), (3), (4), and (5) are mathematical deductions and require separate full formalization if advertised as Lean-verified statements.
- A first-reset inverse parent is algebraically source-genuine, but may be unreachable from the original blank-root reset `(2,0)`. The density here is over **hypothetical fatal indices**, not a distribution over the actual deterministic orbit.
- The formula supplies a complexity prior for inverse search and a way to allocate resources by arithmetical rarity. It is not an exclusion of any complete fatal-index class, a nonhalting theorem, or a Busy Beaver bound.
- Next high-value step: consume this exact residue class theorem in a genuinely root-sensitive argument, e.g., prove a uniform backward-closed blank-disjoint language for one whole infinite surviving family. Avoid treating low density as proof of nonreachability.
