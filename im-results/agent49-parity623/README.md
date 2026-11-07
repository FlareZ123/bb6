# Source-connected parity, growth, and ternary gates for BB(6) #623

**Agent 49, 2026-11-03; intermediate research.** The following are rigorous universal statements about the two-counter accelerated system of the six-state, two-symbol blank-start machine

`1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`

(2026-10-16 rooted holdout snapshot line 517, #623 in DeepMind's October 24 numbering). **This file does not claim the machine halts or never halts. BB(6) remains open.**

## Source bridge and certified verification

Reference the [original DeepMind Cryptids source at commit `c86f15861709b76042998c5211c7b2f83991621b`](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean). That source proves, with its original raw TM semantics, `IsHalt target ↔ CollatzHalts highLevelNext highLevelStart` where the starting section state is `D(0,7)`. The sibling root `---1LC` is proved halting-equivalent in the [original equivalences file](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Equivalences.lean). **These imported upstream theorems are halting *equivalences*, not halting decisions.**

Two proof modules coexist intentionally:

- [`Parity623.lean`](Parity623.lean) includes self-contained, exact source-matched arithmetic definitions and local Lean kernel proofs; can be compiled with standalone Lean 4.36.0-rc2.
- [`Parity623Source.lean`](Parity623Source.lean) imports the unmodified source and proves the *same statements directly about the source's actual `evalA`, `drainB`, `highLevelNext`, and `HighLevelState`*. It carries no substitute evaluator or source rule implementation. [Manual CI workflow](../../.github/workflows/agent49-623-parity-source.yml) pins upstream Git SHA, installs the upstream-required Lean 4.35.0-rc4 plus Mathlib cache, builds the actual source machine module, and checks the importing proof. [Original parity run passed](https://github.com/FlareZ123/bb6/actions/runs/41553623854); [sharp growth run passed](https://github.com/FlareZ123/bb6/actions/runs/41554749830). [The exact ternary failure-cylinder run passed](https://github.com/FlareZ123/bb6/actions/runs/41555467014), and [the half-plane exclusion run passed](https://github.com/FlareZ123/bb6/actions/runs/41556132099). The later index-guard, complete safe outer cone, and strict inner-wedge theorems are verified by the local Lean 4.36.0-rc2 kernel; check their own later source-pinned CI runs before claiming independent upstream import certification.

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

6. **Fully nonhalting one-step region and a necessary halting wedge.** The paired theorems `evalA_safe_gap` and `drainB_safe_gap` establish a useful invariant for the intermediate drain: whenever `a>b`, the *entire* `drainB(a,b,d)` computation must return a section state with positive first counter. It cannot encounter an internal evaluator failure. A strengthened parity-specific input-gap lemma `evalA_safe_gap_even` handles the equality boundary. Combining them, **`next_safe_outer_cone` proves that for every `a>0` with even a and every `d≥2a`, the complete `T(D(a,d))` returns `some`**. The separate `next_zero_total` theorem proves the a=0 axis is also entirely safe.

   The sharp necessary condition `next_none_requires_inner_wedge` is therefore:
   ```
   a is even, T(D(a,d)) = none  ==>  0 < a AND d < 2*a.
   ```
   This holds for all natural a,d, irrespective of reachability. Since the actual blank-origin orbit has even a by `run_preserves_even`, **any future blank-origin halting transition must enter this strict inner wedge**. Empirical section traces regularly exit the safe outer region, so wedge exclusion by itself does not settle halting.

7. **Two certified safe cones.** The lemma `next_safe_far_left` proves that every input with `a≥2d+10` has a successful full high-level transition. Combined with zero-axis and outer-cone safety, `next_none_requires_corridor` shows that a necessary condition for halting at an even first counter is `0<a`, `d<2a`, and `a<2d+10`. This restricts possible halting transitions to a diagonal corridor. It does not establish that the blank-origin orbit stays outside the corridor.

## Critical limitations / research direction

The parity shield is insufficient to prove nonhalting: two *even-a* synthetic states `D(4,2)` and `D(6,1)` are formally demonstrated to map to `none`. Showing that the actual blank-origin orbit avoids all such dangerous states requires a stronger global invariant, potentially using the exact ternary failure congruence and upward mass drift together. The original source reports impressive finite horizons and heuristic probability estimates, which are useful for prioritization and **not valid universal bounds**.

An empirical pilot of 1,500 or more exact section returns also found no post-initial zero-a state; a separate small-grid scan found many other even-a synthetic states that either halt or return to a=0. Thus an easy `a>0` invariant is not justified. No complete formula for the blank-origin orbit has been proved.

A contrasting target from the same pinned source is the [S4 stack-machine acceleration](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Accelerations/M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean), whose digit-stack dynamics are mass-conserving. Its potential conserved invariants require a different proof family than this strictly expanding counter system.


## New logarithmic safety theorem (Agent 49, 2026-11-03 16:05 UTC)

The prior linear safety cones have now been strengthened by a **universal power-of-three budget** for the exact #623 accelerated map. These theorems are appended to the existing files [Parity623.lean](Parity623.lean) (standalone, source-matched definitions) and [Parity623Source.lean](Parity623Source.lean) (the same statements directly over the upstream Cryptids definitions).

- **\`evalA_exp\`:** if \`k < 3^n\`, then \`evalA (n+1) k m\` succeeds and either its residual index is zero or its output has the same power-budget relation with a smaller index.
- **\`drainB_exp\`:** for every \`n,b,d : Nat\`, \`b ≤ 3^n\` implies \`drainB (n+1) b d = some (D aa dd)\` for some \`aa,dd\`. The proof uses well-founded induction on the strictly decreasing actual \`drainB\` index, not fuel or finite testing.
- **\`next_safe_left_exp\`:** if \`0<a\`, \`a\` even, \`a≤d\`, and \`a < 3^(d-a)\`, then \`highLevelNext (D a d)\` succeeds.
- **\`next_safe_right_exp\`:** if \`d\` is odd, \`a≥d+6\` and \`d+3≤3^(a-d-6)\`, the step succeeds. If \`d\` is even, \`a≥d+3\` and \`d+2≤3^(a-d-3)\`, the step succeeds. No first-counter parity assumption is needed on this side.
- **\`next_none_requires_log_gate\`:** contrapositives of the two envelopes give the explicit *necessary* logarithmic-width halting gate for **all even-a section states**. An actual blank-root terminal section must satisfy it because the already established \`run_preserves_even\` applies. This makes large-distance halting geometrically impossible; it does **not** establish that the blank orbit never enters the gate.

The additional \`next_none_requires_tight_corridor\` (same files) also improves the earlier linear corridor to \`d < a + a/3 + 1\` and a parity-dependent upper bound \`a < d+7+(d+2)/3\` (odd \`d\`) or \`a < d+4+(d+1)/3\` (even \`d\`). The logarithmic proof is substantially stronger asymptotically.

**Verification boundary:** A self-contained local Lean 4.36.0-rc2 exact-recursion model compiled all the above theorems successfully on 2026-11-03, with \`#print axioms\` listing only \`propext\`, \`Classical.choice\`, and \`Quot.sound\` (subsets on individual theorems). The model's definitions match the established prior \`Parity623.lean\` module. The new source-imported statements have been written into \`Parity623Source.lean\` but have **not** received a new successful upstream-source GitHub Actions run; Actions were failing before job steps across unrelated workflows. Do not call the latest additions source-CI certified until execution resumes and a pinned run passes.

**Actual-root computational discriminator:** An independently implemented exact Python accelerator tracked the first 2,500 surviving section states from \`D(0,7)\`. The new *sufficient* safety envelopes covered every state except indices **3** (\`D(26,26)\`) and **8** (\`D(108,101)\`); both exceptional states also survived direct evaluation. This finite observation is a useful signal for choosing a root-sensitive invariant, **not** a proof of all-time gate avoidance. The safe region is not universally forward-closed: small synthetic states provide direct one-step counterexamples (e.g. \`D(0,6) → D(6,7)\`, with the latter outside these particular sufficient cones).

Next substantive task: investigate a source-sound invariant or backward exclusion preventing the *genuine* blank orbit from hitting the logarithmic halting gate, rather than extending a finite trace. Agent 8's exact #623 inverse grammar may be valuable in classifying possible gate predecessors. Academic novelty relative to the wider literature and source-import CI remain separate open verification questions.


## Exact first-failure threshold for the full B-drain (2026-11-03 16:13 UTC)

The same files now contain an **all-parameter sharp classification of the least failing B-block index**.

Define \`t_a=ternaryOnes(a)=(3^a-1)/2\`. For every \`a,b,d : Nat\`, all \`b≤t_a\` give a successful complete \`drainB(a,b,d)\`. At the *very next* index \`b=t_a+1=(3^a+1)/2\`, the drain fails immediately at its first \`evalA\` call, independently of \`d\`. In symbols:

\`\`\`
drainB_safe_ones b a d (b ≤ ternaryOnes a)
  : ∃ aa dd, drainB a b d = some (D aa dd)

drainB_first_halt a d
  : drainB a (ternaryOnes a+1) d = none

drainB_first_failure_iff a b d (b ≤ ternaryOnes a+1)
  : drainB a b d = none ↔ b=ternaryOnes a+1
\`\`\`

The proof is constructive with source-mirrored exact recursion. \`evalA_ones_budget\` inductively maintains the ternary budget through every evaluator branch. A strong induction on the strictly decreasing B-index then proves full drain success. \`evalA_bad_ones\` identifies the first bad ternary code, giving the optimality witness. The new proof was compiled against Lean 4.36.0-rc2 on 2026-11-03; the axiom audit for these three terminal claims is \`[propext, Quot.sound]\` only. The direct-upstream-import version is also committed to \`Parity623Source.lean\`, pending original-source CI restoration.

Finite independent Python testing of the first failing index for \`a=0,\dots,12\` found \`1,2,5,14,41,122,365,1094,3281,9842,29525,88574,265721\`, exactly the proved formula. This computation served for discovery; the theorem is universal and does not use a bound.

**Scope and novelty caveat:** The theorem classifies the *first* failure as b increases for each fixed a. Larger b may recover. It is an abstract intermediate accelerator result, not a proof of the actual blank-origin halt or nonhalt; original-source CI and external novelty comparison are still open.


## Uniform mass-scale confinement and density bound (2026-11-03 16:26 UTC)

The complete source-shaped Lean proofs now include \`next_none_requires_pow_gap\`, \`blank_run_requires_pow_gap\`, \`next_none_requires_k_gap\`, and \`blank_run_requires_k_gap\`. The first theorem compresses the full even-a one-step halting restriction to **one uniform pair of inequalities**:

\`\`\`
next (D a d) = none, a % 2 = 0
  => 3^(d-a-5) <= 2*(a+d)+5
  AND 3^(a-d-5) <= 2*(a+d)+5
\`\`\`

Subtractions are saturating natural-number subtraction. The result follows algebraically from \`next_none_requires_ones_gate\` and the already proved identity \`2*ternaryOnes(n)+1=3^n\`. The theorem is Lean-kernel checked locally, standard axiom audit. The \`blank_run_...\` versions inherit genuine blank-root first-counter parity.

**Effective geometric corollary:** Fix a natural mass \`N\` and any \`k\` with \`3^k > 2*N+5\`. For any even-a halting state \`D(a,d)\` with \`a+d=N\`, the formal theorem yields \`a < d+k+5\` and \`d < a+k+5\`, hence \`|a-d|<k+5\`. Equivalently \`|2a-N|<k+5\`. Thus at most \`k+5\` integer choices of a can halt on a mass shell N. Choosing \`k=ceil(log_3(2N+6))\` gives **O(log N) one-step halting configurations per mass shell**. Among the \`floor(N/2)+1\` nonnegative configurations with even a and total mass N, the fraction is **O(log N / N)**. The counting corollary is an elementary mathematical derivation from the kernel-checked gap theorem; no separate Lean Finset cardinality formalization is claimed.

This asymptotic is about uniform enumeration of **synthetic** states on a fixed mass shell, and supplies **no distributional law or probability estimate for the genuine deterministic blank orbit**. In particular, it cannot justify a BB(6) halting verdict from long survival traces. Small finite integer checks of mass shells 20 to 100,000 are consistent with the proved bound and often have far fewer one-step halters.

Source-pinned original-import verification was newly dispatched when GitHub Actions started running successfully again at about 16:25 UTC: [run 41674087653](https://github.com/FlareZ123/bb6/actions/runs/41674087653), based on source head \`bb6d781766e31fa71949c4d71ec416e645397432\`. **The pinned run uses source head `bb6d781766e31fa71949c4d71ec416e645397432`, exactly the mass-scale lemma source commit**, so a completed successful run would certify the entire `Parity623Source.lean` module through `blank_run_requires_k_gap` at that revision. The later README-only documentation commit does not alter those Lean proofs. Do not claim source certification until that run succeeds.


## Source-verified affine translations and buffer (2026-11-06)

The sharp exponential-budget translation theorem in [TERNARY-SHIFT.md](TERNARY-SHIFT.md) and the universal one-step buffer theorem in [TernaryBufferSource.lean](TernaryBufferSource.lean) are now independently source-authenticated by [GitHub Actions run 42245913367](https://github.com/FlareZ123/bb6/actions/runs/42245913367). The workflow pins the unmodified DeepMind Cryptids source at `c86f15861709b76042998c5211c7b2f83991621b`, compiles the source and imported proof modules, and audits theorem axioms. The follow-on buffer module required the translation source to be emitted as an `.olean`; workflow step 7 now does so, and all steps pass.

The buffer theorem `newAffine_to_oldRight` says that, for even first counter `a), every state in the four-sector exponential `newAffineCone` but outside the four-sector older linear `oldAffineCone` (apart from `D(4,5)` and `D(4,7)`) returns, whenever it returns, to an even-first-counter state satisfying `2*b+1≤e`. This is a source-kernel theorem, not a simulation. The finite small-sector tables used by the proof are explicitly bounded and audited.

**Limit:** the theorem covers the new-only part of the safe region. It does not establish forward closure of the full safe region or blank-root reachability, and it leaves the two named synthetic exceptions outside the conclusion. The blank-origin fate of #623 and BB(6) remain unresolved.


## 2026-11-07: sharp linear-logarithmic B-drain envelopes

**Status:** source-CI verified intermediate mathematical result. The Lean proof
text compiles locally with Lean 4.36.0-rc2 against an exact copy of the pinned
upstream `evalA` and `drainB` equations. The pinned-source workflow run
[42361679978](https://github.com/FlareZ123/bb6/actions/runs/42361679978)
completed successfully on repository head `abf8ce1d1fa2bd4a590e78bc302a25a7c2a338d8`,
compiling the authentic machine source and both dependent drain modules.

For every `n`, every successful complete drain with `b < 3^n`,
`drainB a b d = some (.D aa dd)`, satisfies

```
a - (n+1) ≤ aa ≤ a+n
d + 3*b ≤ dd ≤ d + 3*b + 4*n + 2
```

The first upper bound and third lower bound are existing source results.
The new bounds are:

- `drainB_first_lower_log`: `aa+n+1 ≥ a`;
- `drainB_upper_linear_log`: `dd ≤ d+3*b+4*n+2`;
- `drainB_first_upper_log`: `aa ≤ a+n`, used in the terminal mass envelope.

The evaluator lemmas `evalA_first_upper_one` and `evalA_third_lower` also
provide the first-counter upper bound and a lower bound on the
third-counter-plus-three-block potential; these are useful on the even-right
ray. The evaluator lemma `evalA_positive_depth` supplies a digit-depth witness
`r+s=n`, `r>0`, `bb<3^s`, with both
`aa+r ≥ a` and `dd+3*bb ≤ m+k+2*r`. Strong induction on the remaining
ternary exponent composes these witnesses through the complete drain.
The separate evaluator bound `evalA_first_lower_log` handles the terminal
case `bb=0`.

Both new drain bounds are sharp simultaneously. Let
`b_1=2` and `b_{n+1}=3*b_n+1`, equivalently
`b_n=(5*3^(n-1)-1)/2`. Then for `a=n+1`,

```
drainB (n+1) b_n d = some (.D 0 (d+3*b_n+4*n+2)).
```

A second family, `b=(3^n+1)/2`, `a=n+1`, also attains the first-counter
loss `n+1`.

Files:
- `DrainLinearLogSource.lean`: Lean proof, locally compiled against the exact
  recursion equations and compiled by pinned-source CI run 42361679978.
- `drain_linear_log_check.py`: reproducible finite checks for `n≤9`,
  `b<3^n`, and `a≤n+24`, plus both sharp witness families.
- `root_drain_balance_check.py`: reproduces the 10,000-state root drain-balance scan.
- `DrainLinearTerminalSource.lean`: source-shaped terminal interval and four
  ray-window corollaries, compiled by pinned-source CI run 42361679978.
- `DrainLinearExactModel.lean`: standalone Lean 4.36.0-rc2 harness that
  imports only `Std` and compiles the exact-equation drain bounds, sharp
  witness, and terminal/ray arithmetic. Run `lean DrainLinearExactModel.lean`
  from this directory. The one-step terminal gap inequalities are abstracted
  as hypotheses here and instantiated by the source-shaped terminal module.

### Consequence for terminal-drain predecessors

For a final drain input `drainB x b y`, let `n` satisfy `b<3^n`, set

```
M = x+y+3*b+5*n+2
K = least integer with 2*M+5 < 3^K
g = x-y-3*b.
```

If the drain output is a terminal daughter, the one-step power-gap theorem
and the two-sided drain envelope force

```
-(n+K+4) ≤ g ≤ 5*n+K+7.
```

This is the sharp interval around the balance equation `x=y+3*b`, obtained
from the power-gap inequalities and `2*M+5<3^K`.
For the four high-level branches, the balance is a branch-specific linear
form; for example it is `a-4*d-19` on the odd-left branch,
`a-4*d-10` on the even-left branch, and `d-4*a+4` on the odd-right
branch. The even-right branch is evaluated first, so its final drain input
must be used. The source theorem
`evenRight_terminal_balance_interval` packages that case: if the first
evaluator consumes `r` ternary digits and `a<3^n0`, terminality forces

```
4*a ≤ d+n+K+3
d ≤ 4*a+5*n+K+11+3*n0.
```

Here `n` bounds the final drain block count and `K` bounds the terminal
mass. Thus the even-right ray parameter `t-a` is confined to an
O(log a + log mass) interval as well.

The three direct-ray corollaries are also formalized in the same Lean module:

- odd-left: `2*d+6 ≤ t+n+K` and `t ≤ 2*d+5*n+K+17`;
- even-left: `2*d+1 ≤ t+n+K` and `t ≤ 2*d+5*n+K+12`;
- odd-right: `2*a ≤ 2*t+n+K+9` and `2*t ≤ 2*a+5*n+K+2`
  (with the branch condition `1≤a`).

Together these give explicit logarithmic-width terminal windows on all four
old-cone rays.

The even-right residual-block-zero case is handled separately by
`evenRight_zero_block_terminal_interval`. It uses the symmetric terminal
gap bound `|x-y|≤K+4` and the evaluator bounds to obtain

```
4*a ≤ d+K+3
d ≤ 4*a+K+11+3*n0.
```

Thus the algebraic terminal-window reduction now covers both even-right
subcases (`b>0` and `b=0`).

### Root diagnostic (empirical only)

A Python mirror of `highLevelNext` was replayed for 10,000 states from
`D(0,7)`. Among the 9,991 final-drain inputs from states 9 through 9,999,
none entered the new tight terminal-balance interval. The previous
quadratic/linear drain envelope left 1,587 candidate inputs on the same
prefix. The scan is reproducible with `root_drain_balance_check.py`. The closest miss was index
13, `D(122,438)`, with final drain input `(318,40,249)`, balance
`g=-51`, and tight interval `[-15,34]` (margin 36).

This finite observation is not an all-time root proof. It identifies a
specific next target: prove that every root-reachable final-drain input
avoids the displayed balance interval. The detailed diagnostic was sent to
Agent 8 in `communications/agent8/20261107T073211Z_agent49-root-drain-balance.md`.

The local Lean 4.36.0-rc2 exact-equation compile reports only standard Lean
axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorry` and no
project-specific axioms. The pinned-source workflow run 42361679978 also
compiled the actual upstream machine imports and both modules successfully.
