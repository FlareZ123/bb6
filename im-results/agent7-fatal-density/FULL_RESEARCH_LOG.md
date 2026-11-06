# Historical full research log

**Unabridged snapshot of the former research README, 6 November 2026.** The original mathematical equations, source links, experiments, failed approaches, uncertainty, and chronological proof reports are preserved. Any “pending” or “current” claims below describe the old writing time. For current synthesis use the [maintained README](README.md).

---

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

The quotient is integral because the previous lift satisfies (1). **This is a source-linked all-index result**, invoking earlier independently proved [FatalValuationExact.lean](../agent7-cascade-forward/FatalValuationExact.lean) lemmas `fatal_shift_balance`, `fatal_shift_exact` and `fatal_shift_keeps_divisibility`. The new theorems first passed local Lean 4.36.0-rc2 checks against exact theorem-signature stubs. The subsequent **unchanged checked-in original-source Lean 4.36.0-rc2 CI succeeded** in [run 42118974269](https://github.com/FlareZ123/bb6/actions/runs/42118974269), triggered via [issue #23](https://github.com/FlareZ123/bb6/issues/23). Its checked head contains this source file and the complete preceding `FatalValuationExact` dependency chain. `#print axioms` for the new theorem is compiled as part of the source file. No `sorry` or `native_decide` occurs in the new file.

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

- (1) is kernel-verified against the unchanged full original-source dependency chain in successful CI 42118974269. (2), (3), (4), and (5) are mathematical deductions and require separate full formalization if advertised as Lean-verified statements.
- A first-reset inverse parent is algebraically source-genuine, but may be unreachable from the original blank-root reset `(2,0)`. The density here is over **hypothetical fatal indices**, not a distribution over the actual deterministic orbit.
- The formula supplies a complexity prior for inverse search and a way to allocate resources by arithmetical rarity. It is not an exclusion of any complete fatal-index class, a nonhalting theorem, or a Busy Beaver bound.
- Next high-value step: consume this exact residue class theorem in a genuinely root-sensitive argument, e.g., prove a uniform backward-closed blank-disjoint language for one whole infinite surviving family. Avoid treating low density as proof of nonreachability.


## Uniform odd-depth inverse ray, genuine-root lemma

Additional theorem file: [OddRayForced.lean](OddRayForced.lean). Its local Lean 4.36.0-rc2 stub-interface test was followed by **successful full unchanged-original-source Lean CI**, [run 42121009702](https://github.com/FlareZ123/bb6/actions/runs/42121009702), triggered via [issue #29](https://github.com/FlareZ123/bb6/issues/29). The module imports unchanged `UniqueEvenBand` source and checks genuine `ResetParent` and `ReachC` propositions, with no `sorry`. The separate [OddRayDeep.lean](OddRayDeep.lean) proves explicit unbounded eligible depths, and its **full unchanged-source Lean CI succeeded** at [run 42122191076](https://github.com/FlareZ123/bb6/actions/runs/42122191076), triggered by [issue #31](https://github.com/FlareZ123/bb6/issues/31), after an import-path issue was repaired. The proof reports standard logical axioms, no sorry.

Define a canonical sequence of hypothetical even inverse ancestors for fatal index `n` by

\[
D_0(n)=n+4,\qquad D_{j+1}(n)=2D_j(n)+(n-1),\qquad U_j(n)=4\cdot2^n-D_j(n).
\]

Whenever `n>=4`, `j` is odd and `D_j(n)<=2^n+1`, the lemma establishes the **complete source-genuine first-return inverse iff**

\[
\operatorname{ResetParent}(q,U_j(n))\quad\Longleftrightarrow\quad q=U_{j+1}(n).
\]

The all-depth true blank-derived source-C consequence is

\[
\operatorname{ReachC}((2,0),(U_j(n),0)) \iff
\operatorname{ReachC}((2,0),(U_{j+1}(n),0)).
\]

The mechanism is an alternating congruence phenomenon: `D_(j+2)%3=D_j%3`, and for **odd** `j`, `D_j%3=1`. Therefore `U_j%3` is either 0 or 1. Every odd-arm first-return parent of any target requires its height congruent to 2 modulo 3. The explicit dyadic margin ensures `U_j` stays within the single high even-image band at scale `n-1`, so Agent7's previously source-verified `any_parent_equals_even` uniquely forces `U_(j+1)`. The existing exact reset-chain transport yields the genuine blank-root equivalence. The index `j` is arbitrary, subject to the explicit band margin; this expands earlier finite-depth odd-step observations in `FourEven.lean` and `SecondEven.lean` into a quantified symbolic family.

This is a **conditional branch compression** for reset targets. Even-indexed levels may still admit multiple inverse parents; no uniform nonreachability, no resolved six-state halting status and no BB6 value follows.


## Further paper derivation: alternating 3-adic towers at every ray depth

See [AlternatingRayValuation.md](AlternatingRayValuation.md) for a generalized signed-numerator Hensel argument at arbitrary symbolic inverse depth. Even depths have exactly one ternary high-valuation index residue class at each power and share the fatal source's limiting synthetic odd fan-in law. Odd depths have no odd-arm predecessors at all. The generalized **even-depth** 3-adic statement is an explicit *mathematical proof awaiting independent formal Lean implementation*; its dependence on genuine source parents is described precisely in the note. Do not confuse this paper derivation with the source-verified odd-depth first-reset equivalence.


## New per-ray 3-adic structure: one arithmetically possible odd fork per six steps

The fully quantified **paper** theorem in [RayForkPeriodicity.md](RayForkPeriodicity.md) proves that for every surviving fatal index n mod6=4 or5, with ray height U_j and signed input Z_j=2U_j+5, every odd depth has Z_j nonzero mod3. At even depths, the three consecutive values Z_j,Z_(j+2),Z_(j+4) have residues **0, 3, 6 modulo 9 in some order**. Consequently, under the high dyadic-band condition, at least five of every six ray positions have one unique source first-reset parent, the next U_(j+1). The sixth is the sole possible odd-arm fork. This strengthens the verified all-odd-level forcing mechanism using Agent10's proven near-top odd-t-zero exclusion, but the full new five-of-six quantified corollary **has not yet been mechanically source-Lean certified**. It remains a proved paper deduction with explicit hypotheses.

The more general [RayDepthHensel.md](RayDepthHensel.md) establishes a **dual Hensel residue tower in ray depth**: at each precision k≥1 and for *every fixed* fatal index n in the surviving sectors, there is exactly one j residue modulo 2*3^(k-1) with 3^k dividing the signed Z_j. Its proof uses the elementary exact lifting 2^(2*3^(k-1)) = 1+3^k*c_k with 3 not dividing c_k. This yields an exact limiting valuation law over all **formal signed ray depths**: mass 1/2 at v3=0 and mass 3^(-k) at v3=k for k≥1. Only finitely many ray depths have nonnegative physical reset heights for fixed n, so the signed limit **does not describe a true blank-orbit frequency**. The duality with the already source-certified Hensel theorem in fatal-index direction is mathematically useful for inverse-graph compression.

The modular Python diagnostic [ray_tower.py](ray_tower.py) verifies complete small residue periods and computes 256 ternary lifts in ordinary integer modular arithmetic without constructing astronomical powers of two. The direct independent modular tests in the two new notes help check their formulas. Formalize the dual ray-depth tower and source-root five-of-six corollary next; all remain **intermediate results** without a #746 blank-root halting decision or a BB(6) bound.


## Kernel-checked six-step periodicity subtheorem

[SignedRayPeriod.lean](SignedRayPeriod.lean) defines the signed formal ray numerator `signedZ n j = 8*2^n + 2*n+3 - 2^(j+1)*(2*n+3)` as an integer and proves the exact fully quantified **six-step period modulo nine**, for all natural n and j:

`CascadeRayPeriod.signed_ray_six_period : signedZ n (j+6)%9 = signedZ n j%9`.

This proof typechecked **locally with Lean 4.36.0-rc2**, no sorry, no native_decide, axiom audit exactly `[propext, Quot.sound]`. It is included in the existing manual full-original-source workflow and was dispatched for source checking through [issue #33](https://github.com/FlareZ123/bb6/issues/33), [CI 42124540499](https://github.com/FlareZ123/bb6/actions/runs/42124540499). **The unchanged checked-in-source [CI 42124540499](https://github.com/FlareZ123/bb6/actions/runs/42124540499) has now completed SUCCESS**, compiling the complete earlier source dependency chain and this exact new file. The theorem's local and source check is free of sorry; local axiom audit is `[propext, Quot.sound]`. The per-block 0/3/6 exact residue permutation and rooted five-of-six forced parent corollary are still paper-derived; their complete Lean formalizations are separate and must not be inferred from the period-only theorem.


## 2026-11-06: exact original-source six-packet root and odd-fork pruning

Full unchanged-source Lean 4.36.0-rc2 successful audits: [42132557789](https://github.com/FlareZ123/bb6/actions/runs/42132557789), [42133134677](https://github.com/FlareZ123/bb6/actions/runs/42133134677), [42133586305](https://github.com/FlareZ123/bb6/actions/runs/42133586305), [42134663672](https://github.com/FlareZ123/bb6/actions/runs/42134663672), [42135230195](https://github.com/FlareZ123/bb6/actions/runs/42135230195).

The source-certified modules `RayResidues`, `RayNonFork`, `SixPacketRoot`, `ForkDecompose`, `PacketSelector`, `FatalPacket`, `RayForkPrune`, `OddCandidate` prove the exact 0/3/6 modulo-9 even-depth permutation, five unique nonfork reset-root edges per complete high-band six-packet, and a lossless exact blank-origin source-C criterion reducing each packet to its depth-six continuation or all source-genuine odd-arm ancestors at its unique computably selected even fork. `FatalPacket` applies to every surviving fatal n>=10. The odd t=1 predecessor exists source-genuinely under explicit dyadic margin 16*D+27*n+16<=2^n and Z=9d. If d%3=1 it is excluded from true C(2,0)-root reachability. If d%3=2 and its own 2q+5 is not divisible by nine it is likewise excluded; root reachability in this branch requires a secondary nine-divisibility constraint. Proof exploits exact original source reset-image gap. These restrictions leave more complicated odd valutions/forks and do not decide source machine #746, its original raw tape, or BB(6).

Additional locally Lean-proved symbolic residue result: `RayTriplePeriod.lean` (currently local only, not source-certified) gives every three successive six-packet fork numerators the exact 0/9/18 permutation modulo27, conditional on the initial numerator divisible by9. This is **unpublished local draft pending repository persistence and full-source CI** and is not a blank-orbit frequency theorem.
