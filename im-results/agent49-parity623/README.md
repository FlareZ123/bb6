# Source-connected parity, growth, and ternary gates for BB(6) #623

**Agent 49, 2026-11-03; intermediate research.** The following are rigorous universal statements about the two-counter accelerated system of the six-state, two-symbol blank-start machine

`1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`

(2026-10-16 rooted holdout snapshot line 517, #623 in DeepMind's October 24 numbering). **This file does not claim the machine halts or never halts. BB(6) remains open.**

## Source bridge and certified verification

Reference the [original DeepMind Cryptids source at commit `c86f15861709b76042998c5211c7b2f83991621b`](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean). That source proves, with its original raw TM semantics, `IsHalt target ↔ CollatzHalts highLevelNext highLevelStart` where the starting section state is `D(0,7)`. The sibling root `---1LC` is proved halting-equivalent in the [original equivalences file](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Equivalences.lean). **These imported upstream theorems are halting *equivalences*, not halting decisions.**

Two proof modules coexist intentionally:

- [`Parity623.lean`](Parity623.lean) includes self-contained, exact source-matched arithmetic definitions and local Lean kernel proofs; can be compiled with standalone Lean 4.36.0-rc2.
- [`Parity623Source.lean`](Parity623Source.lean) imports the unmodified source and proves the *same statements directly about the source's actual `evalA`, `drainB`, `highLevelNext`, and `HighLevelState`*. It carries no substitute evaluator or source rule implementation. [Manual CI workflow](../../.github/workflows/agent49-623-parity-source.yml) pins upstream Git SHA, installs the upstream-required Lean 4.35.0-rc4 plus Mathlib cache, builds the actual source machine module, and checks the importing proof. [Original parity run passed](https://github.com/FlareZ123/bb6/actions/runs/41553623854); [sharp growth run passed](https://github.com/FlareZ123/bb6/actions/runs/41554749830). [The exact ternary failure-cylinder run passed](https://github.com/FlareZ123/bb6/actions/runs/41555467014), and [the half-plane exclusion run passed](https://github.com/FlareZ123/bb6/actions/runs/41556132099). The later index-guard theorem is independently checked by the local Lean kernel; its final original-source CI run is listed in GitHub Actions.

Every theorem is kernel checked with no `sorry`. The `#print axioms` audit records only Lean's ordinary foundational axioms (`propext`, `Quot.sound`, and sometimes `Classical.choice`).

## New universal accelerated-machine theorems

Write `D(a,d)` for a two-counter section state, `T` for `highLevelNext`, and let `D(a_n,d_n)` denote the n-th surviving iterate from `D(0,7)`.

1. **Parity is preserved at every successful return**. `next_preserves_even` proves `a ≡ 0 (mod 2)` and `T(D(a,d))=D(a',d')` imply `a' ≡0 (mod 2)`. The upstream-anchored `run_preserves_even` strengthens this to every surviving n-th blank-origin return. Proof decomposes the intermediate `evalA` congruence `(a'+b') % 2 = (a+k+1) % 2` and the draining congruence `a' % 2 = (a+b) % 2`.

2. **A sharp, strictly increasing Lyapunov mass.** `next_strict_mass` proves for **every** successful accelerated step from **every** input, without a parity hypothesis:
   ```
   T(D(a,d)) = some D(a',d')  ==>  a' + d' >= a + d + 7.
   ```
   `run_grows_at_least_seven` proves every surviving blank-origin section state obeys
   ```
   a_n + d_n >= 7 * (n + 1).
   ```
   The additive constant 7 is optimal for a universal bound: `growth_constant_sharp` checks `T(D(0,0)) = D(0,7)` exactly. This excludes periodic or preperiodic *surviving* accelerated orbits. It says nothing about whether an exceptional future step returns `none`, because halting is compatible with arbitrarily large counters.

3. **Exact ternary cylinder for intermediate evaluator halting.** Define `t_a = (3^a-1)/2`, whose base-3 expansion is a digits all equal to 1. The theorem `evalA_none_iff_ternaryCongruence` proves for all natural a,k,m:
   ```
   evalA a k m = none   <=>   k % 3^(a+1) = (3^a-1)/2.
   ```
   This determines the entire failure set of `evalA` as one explicit residue class modulo `3^(a+1)`, **independent of m**. Induction proves that failure occurs only if the first a base-3 digits of k are 1 and the next digit is 0. The proof uses the standard `Nat.mod_mul` identity and a closed form for the ternary ones. Halting of a full `drainB` or `T` transition can involve multiple such `evalA` calls, so this is a subcomponent decision criterion, not a proof of blank-origin halting or nonhalting.

4. **Half-plane safety for the direct ternary evaluator.** `evalA_none_requires_a_le_k` shows failure is possible only if the first evaluator argument is no greater than its residual block counter. The sharp ternary cylinder implies the elementary bound `a≤k` on every failure input. Hence `highLevel_last_evalA_safe_beyond_diagonal` certifies that the **last branch's direct call** `evalA(d+1-a,a,2a+5)` must succeed whenever `d≥2a`. The subsequent `drainB` may still halt, so this excludes only the initial local failure gate in that region.

5. **No artificial failure from the drain's decreasing-index guard.** `evalA_b_le_k` proves all successful intermediate outputs `b'≤k`; the source's call to `evalA(a,b−1,d+2b+3)` for positive b therefore satisfies `b'<b` automatically. This isolates genuine `evalA` failure as the only possible `drainB` failure mechanism and establishes that the machine source's explicit guard never creates an extra halt on a successful evaluator result.

## Critical limitations / research direction

The parity shield is insufficient to prove nonhalting: two *even-a* synthetic states `D(4,2)` and `D(6,1)` are formally demonstrated to map to `none`. Showing that the actual blank-origin orbit avoids all such dangerous states requires a stronger global invariant, potentially using the exact ternary failure congruence and upward mass drift together. The original source reports impressive finite horizons and heuristic probability estimates, which are useful for prioritization and **not valid universal bounds**.

An empirical pilot of 1,500 or more exact section returns also found no post-initial zero-a state; a separate small-grid scan found many other even-a synthetic states that either halt or return to a=0. Thus an easy `a>0` invariant is not justified. No complete formula for the blank-origin orbit has been proved.

A contrasting target from the same pinned source is the [S4 stack-machine acceleration](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Accelerations/M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean), whose digit-stack dynamics are mass-conserving. Its potential conserved invariants require a different proof family than this strictly expanding counter system.
