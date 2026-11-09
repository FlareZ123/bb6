# Machine #746: an exact dyadic middle-band image and two-step blank-root exclusions

*9 November 2026. Mathematical source theorems for a six-state, two-symbol Busy Beaver holdout.*

## Scope

The machine is `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`. The authenticated original-C first-reset system starts at the genuine blank-origin post-initial reset height `C(2,0)`. Write `K(h)` for the least natural `k` such that

\[
h+k+5<8\cdot2^k
\]

and let `bitOutcome(h)` be the source-equivalent exact first-reset map. The classification below is for **every arbitrary natural first-reset source**, with no assumption that the source itself comes from the blank run. The subsequent unreachability corollaries concern the **genuine blank-start orbit at every time**.

The results exclude substantial reset-image regions and a new all-index double-obstruction family. They do not determine whether #746 eventually halts, and do not determine BB(6).

## Theorem 1. Complete image classification in the dyadic middle-low strip

For every `k≥3` and natural `h` satisfying

\[
4\cdot2^k\le h,\qquad 2h+5<9\cdot2^k,
\]

the following are equivalent:

\[
\boxed{\exists a,\;\operatorname{bitOutcome}(a)=\operatorname{some}(h)
\quad\Longleftrightarrow\quad h\equiv2\pmod9.}
\]

This equivalence describes the **full** first-reset image, including both parity branches. Its exact source Lean proof is [`middle_low_full_image_iff`](../im-results/agent10-cascade/MiddleLowOddExact.lean). The quantified odd-image equivalence is [`middle_low_odd_image_iff`](../im-results/agent10-cascade/MiddleLowOddExact.lean).

### Proof mechanism

The source inverse grammar admits even image bands `[6·2^j−1,8·2^j−3]`. The displayed middle-low strip is inside the gap between the `j=k−1` band and the `j=k` band, so it contains **no even first-reset outputs**.

For an odd predecessor there exist `t≥0`, odd `d`, and an admissible source quotient `q=2^t d` such that

\[
2h+5=3^{t+1}d,\qquad 6\cdot2^j+1\le q\le8\cdot2^j-1.
\]

At `t=0`, the assumed height interval forces

\[
2\cdot2^k<q=(2h+5)/3<3\cdot2^k.
\]

This is a gap between all admissible source quotient bands. Hence `t≥1`, requiring `9\mid(2h+5)`, equivalently `h≡2 (mod 9)`.

Conversely, when `9\mid(2h+5)`, take

\[
j=k-2,\quad d=(2h+5)/9,\quad q=2d,\quad
a=2q-8\cdot2^j-j-5.
\]

The strip inequalities put `q` inside the exact admissible quotient interval for `j`. The authenticated original inverse grammar proves that `a` is a genuine odd first-reset predecessor, establishing sufficiency. The source proof constructs this `a` for all sizes, rather than extrapolating finite simulation.

Every `h` in the strip in the other eight residue classes has **no reset predecessor at all** and, since `h≠2`, is unreachable from the authentic blank reset root.

## Theorem 2. Infinite authentic nonreachable residue-two family

Let `k_n=10+6n` and `h_n=4·2^(k_n)+4`. For every `n≥0`,

\[
\boxed{\neg\operatorname{ReachC}(2,0)(h_n,0),\qquad
h_n\equiv2\pmod3.}
\]

The [source theorem `middle_low_infinite_root_exclusion`](../im-results/agent10-cascade/MiddleLowRootFamily.lean) uses `2^{k_n}≡7 (mod 9)`; thus `(2h_n+5)%9=6`. These are actual all-time blank-root exclusions that the earlier coarse `mod 3` test cannot yield.

## Theorem 3. Two-stage root exclusion beyond both coarse residue tests

Fix `k≥3` and an authentic reset target `e` with `K(e)=k`. Put

\[
p=2^k,\qquad h=2e-8p-k.
\]

Suppose

\[
12p+k+4\le2e,\quad 4e+10<27p,\quad
27\nmid(2e+5),
\]
\[
2h+5<9p,\qquad 9\nmid(2h+5).
\]

Then

\[
\boxed{\neg\operatorname{ReachC}(2,0)(e,0).}
\]

The [all-index source theorem `narrow_27_middle9_root_exclusion`](../im-results/agent10-cascade/DoubleOddGapRoot.lean) uses the independently source-certified exact 27-adic image criterion in [Agent 7's `SweepOddFatal27Band.lean`](../im-results/agent7-746-fatal-depth-27/SweepOddFatal27Band.lean). It excludes every odd parent of `e`; source even-band uniqueness forces the sole remaining candidate parent `h`. Theorem 1 excludes `h` by its exact 9-adic image obstruction. The first step is a quantified genuine root-chain implication, so the conclusion covers all original source times.

The theorem applies even when **both** `e` and `h` are congruent to 2 modulo 3. For an explicit infinite such family, set

\[
k_n=12+54n,\qquad e_n=6\cdot2^{k_n}+k_n+5,\qquad
h_n=4\cdot2^{k_n}+k_n+10.
\]

For every `n≥0`,

\[
\boxed{\neg\operatorname{ReachC}(2,0)(e_n,0),\quad
e_n\equiv h_n\equiv2\pmod3.}
\]

Indeed, `2^{k_n}≡19 (mod 27)`, `(2e_n+5)%27=24`, and `(2h_n+5)%9=3`. The all-natural [source theorem `double_gap_infinite_root_exclusion`](../im-results/agent10-cascade/DoubleOddGapFamily.lean) establishes the dyadic inequalities and authentic source-root conclusion. The first example has `k=12`, `e=24593`, `h=16406`.

## Theorem 4. Upper high-image blank-root obstruction

For `K(e)=k≥3`, the already exact upper odd-image theorem gives `9\mid(2e+5)` whenever `e≥6·2^k`, `27·2^k≤4e+10`, and `e` has an odd first-reset predecessor. If this condition fails and the unique even parent lies in the no-even-image dyadic gap with residue other than 2 modulo 3, the original blank root cannot reach `e`. This is the source theorem [`upper_high_root_gap_exclusion`](../im-results/agent10-cascade/UpperHighRootGap.lean).

An explicit infinite family is

\[
k_n=10+6n,\qquad e_n=27\cdot2^{8+6n}+5,\qquad
\neg\operatorname{ReachC}(2,0)(e_n,0)
\]

for all `n≥0`, by [`upper_high_infinite_root_exclusion`](../im-results/agent10-cascade/UpperHighRootFamily.lean). The base target `e_0=6917` is congruent to 2 modulo 3.

## Theorem 5. A genuine fatal odd-predecessor branch is unreachable in infinitely many fatal levels

Let `F_j=4·2^j-j-4` denote the exact first-reset fatal height at level `j`. For `j≥22`, the valuation-one candidate odd parent is

\[
x_j=4\left\lfloor\frac{2F_j+5}{9}\right\rfloor
       -8\cdot2^{j-2}-(j-2)-5.
\]

At every `j=22+486t`, `t≥0`, the original source inverse theorem establishes `ResetParent(x_j,F_j)`, and the new source theorem [`fatal_odd_feeder_unreachable`](../im-results/agent10-cascade/FatalOddFeederGap.lean) proves

\[
\boxed{\neg\operatorname{ReachC}(2,0)(x_j,0).}
\]

This result concerns a **genuine predecessor of a fatal target**, rather than a synthetic unrelated reset hole. It rules out the source-`t=1` odd branch of each listed fatal height at every genuine blank-start time, including `j=508,994,1480,\ldots` above the known finite fatal threshold.

Here `k=j-2`, `p=2^k`, and the exact numerator identities are

\[
9x_j+17j+39=56p,\qquad
9h_j+43j+60=40p,\qquad h_j=2x_j-8p-k.
\]

The period `2^162≡1 (mod 243)` and `486≡0 (mod 243)` imply `p%243=31` and `j%243=22` throughout this family, hence `x_j%27=12`, `h_j%9=8`. Thus `(2x_j+5)%27=2` and `(2h_j+5)%9=3`. The full source proof verifies `K(x_j)=k`, both requisite dyadic bands, and the two-stage blank-root exclusion. It uses the existing original-source `fatal_has_odd_parent` to prove the inverse edge is genuine.

The more general [`fatal_odd_feeder_modular_root_exclusion`](../im-results/agent10-cascade/FatalOddFeederCriterion.lean) establishes an **all-index conditional theorem** for any `j≥22`: if `9|(2F_j+5)`, `27∤(2x_j+5)`, and `9∤(2h_j+5)`, then `x_j` is an authentic source parent of `F_j` and is blank-root unreachable. This lifts the two-stage sieve from arbitrary reset holes to a specific fatal inverse branch throughout the infinite domain.

The proof leaves the even first-reset parent of each `F_j` unresolved. Additional odd inverse valuation branches may also exist. Consequently, this theorem excludes a genuine fatal feeder branch without proving global fatal unreachability.

## Verification, limits, and reusable contribution

All modules above compile with the **unchanged original C first-reset grammar**, linked Lean 4.36.0-rc2, no `sorry`, and only standard logical axioms. [Manual original-source CI 42600378353](https://github.com/FlareZ123/bb6/actions/runs/42600378353) succeeded for the exact middle-strip image and upper/low infinite families. [Manual original-source CI 42601104142](https://github.com/FlareZ123/bb6/actions/runs/42601104142) additionally succeeded for the double-root exclusion and its all-natural infinite family.

The novelty here relative to the previous [high-entry exact image and narrow 27-adic root exclusion](../im-results/agent7-746-fatal-depth-27/README.md) is a **complete lower-middle image classification**, a stronger no-parent strip that includes `mod 3 = 2` targets, and a compositional 27/9 root exclusion even when both the target and its forced parent lie in that coarse residue class. These results offer new algebraic pruning rules for infinite inverse fatal cones.

These heights are not generally the fatal source heights `F_j=4·2^j-j-4`. Other authentic reverse branches remain, and a full machine #746 halting/nonhalting proof is still missing.
