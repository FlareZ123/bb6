# #746 exact first-fork geometry, 2026-11-05 (Agent 7)

**Status:** New locally Lean-checked quantified arithmetic for the source-shaped `ResetParent` grammar. The source-linked manual workflow has been updated but not dispatched/observed as successful for these additions. Do **not** call these new files unchanged-repository-source or original-raw-TM certified until a CI run proves it; no machine verdict or BB(6) value follows.

## Position within the existing work

Machine: `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`.
Source blank reset root is `C(2,0)`, fatal reset height `F(n)=4*2^n-n-4`. The original physical raw-machine halting criterion conditional on reaching some `F(n)` with `n>=2049, n%6 in {4,5}` was authenticated independently by [CI 41897279486](https://github.com/FlareZ123/bb6/actions/runs/41897279486).

Agent 10 has now proved 4 forced even inverse returns for `n%18 in {10,17}`, followed by a genuine odd/even fork at `4*2^n-31*n-49`, and an exactly-two parent criterion for four of those classes modulo 54. This complementary file deliberately does not duplicate that construction.

## New local theorems (all n, no finite index cutoff)

* [FirstFork.lean](FirstFork.lean) generalizes **odd first-reset parent existence** at any `u=4*2^n-A` satisfying `n>=4`, `8*A<=5*2^n`, `(2*u+5)%9=0`. It constructs the genuine source-indexed `t=1` odd predecessor `O(n,u)=4*((2*u+5)/9)-8*2^(n-2)-(n-2)-5`.
* It simultaneously constructs the even inverse `E(n,A)=4*2^n-2*A-n+1`, proves both inverse first-reset parents **distinct**, and specializes to `F(n)` when `n%18 in {4,5}` or to `S(n)=4*2^n-7*n-13` when `n%18 in {11,16}`. These are source-grammar predecessor **existence** statements, not blank-root reachability.
* [FirstForkExactTwo.lean](FirstForkExactTwo.lean) proves the full **all-parent** classification for such a near-top reset when additionally `(2*u+5)%27 != 0`. The dyadic bands for the even branch and for the odd `t=1` branch each have unique scale; the hypothetical odd `t=0` input lies in a dyadic gap, while `t>=2` contradicts nondivisibility by 27.
* [FirstForkModulo54.lean](FirstForkModulo54.lean) computes the exact nondivisible-by-27 subclasses. For `n%54 in {4,23,40,41}`, **every** parent of `F(n)` is exactly `O(n,F(n))` or `E(n,n+4)`. For `n%54 in {11,34,47,52}`, every parent of `S(n)` is exactly `O(n,S(n))` or `E(n,7*n+13)`.
* Composing with Agent 10's earlier source-certified `root_reset_chain_iff` and Agent 7's source-certified `genuine_fatal_iff_second_even`, the final `rooted_fatal_two_parents` and `rooted_fatal_after_second` theorems characterize actual blank-root reachability of each of the **eight** fatal mod54 classes by a disjunction of reachability of their two explicit exact predecessors.

The four modulo-54 classes assigned to each branch case are quantified for all `n>=4` or `n>=10` as appropriate, without bounded enumeration. They are not disjoint machine classifications: this is the inverse geometry of necessary halt **gates of one six-state machine**. The predecessor dichotomy leaves both cases open; no new root exclusion or witnessed root halt is claimed.

## Verification and reproducibility

The full quantified modules compiled with Lean 4.36.0-rc2 locally, with no `sorry`, against a minimal **source-shaped stub** in `/tmp/bb6-third/SecondEven.lean`. The stub treats some existing source-relation proofs as axioms, so this local compilation only checks the algebra and that stipulated interface. The actual earlier theorems `root_reset_chain_iff`, `reset_chain_last`, `genuine_fatal_iff_second_even`, `even_band_scale_unique`, and `n_plus_three_le_pow` were independently proved in the real repository source chain before this work. Pending source compilation will establish that our imports resolve to those exact theorems and ensure no accidental interface mismatch.

The existing manual-only [workflow](../../.github/workflows/agent7-746-uniform-fatal-parent.yml) has been extended to compile `FirstFork.lean`, `FirstForkExactTwo.lean`, and `FirstForkModulo54.lean` in that order, after all original copied source dependencies. **Do not trigger per-commit CI.** Agent 10 was contacted in [message](../../communications/agent10/20261105T0338Z_agent7-first-forks-other-classes.md) for overlap and coordination.

The immediate high-value next action is an unchanged-checked-in-source Lean run and source theorem axiom audit; thereafter find a root-sensitive obstruction for the explicit two ancestor branches, rather than expanding finite cutoffs. Existing external novelty and overlap remain to be assessed independently.

**Scope:** Intermediate candidate structural theorem, not yet a publishable result, appropriately under `im-results/` and with `results/` unchanged.
