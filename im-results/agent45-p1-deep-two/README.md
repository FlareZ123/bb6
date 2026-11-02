# Agent 45: arbitrarily long genuine inverse transition chains in the remaining P1 n ≡ 2 (mod 16) sector

**Status (2026-11-02):** Original-source Lean 4.36.0-rc2 kernel verification succeeded in [manual CI run 41436373902](https://github.com/FlareZ123/bb6/actions/runs/41436373902), source commit `4f03752a609792d12c004fc01e93cc2b55fb1639`. The workflow imported and compiled the **unmodified** `im-results/agent1-p1-map/PosEvenForm.lean` and verified `P1Deep2.lean` in a separate dedicated step. The axioms reported locally for the final theorem were exactly `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`, altered machine, or additional axioms.

This is an **intermediate structural result**, not a blank-reachable path, P1 nonhalting, P1 halting, an upper bound, or an exact solution of BB(6).

## Quantified theorem and construction

The genuine P1 critical hub is `(H(n)-6,3)`, where `H(n)=14·2^n-2n-10`. Let

```text
q(0) = 1,         q(r+1) = 4q(r)+1
n(r) = 16q(r)+2             (hence n(r)≡2 mod16)
z(r) = 2^(n(r)-2r-6)
a(r) = 2^(2r+2) = 3q(r)+1
y(r) = 2^(n(r)-4) = a(r)z(r)
u(r) = 28y(r)-4q(r)-3       (at least 1)
B(r) = 14·2^n(r)-2n(r)-16 = 8u(r)+4.
```

For every `r : Nat` the formally checked `critical_two_sector_unbounded` constructs an initial state `s : Nat × Nat` and a finite `PairPath (2r+4) s (B(r),3)`. A `PairPath k` is by definition a chain of **2k successive actual `BB6.Agent1.T` transitions**. The chain has `4r+8` true `T` steps and grows unboundedly with `r`.

The exact two-step identity, proved from the original `G,T` definitions, is

```text
T(b,d+b+10)             = (b+3,d+b+8)
T(b+3,d+b+8)           = (2b+12,d),     b≡0 mod4.
```

Here a right-hand pair is wrapped in `some` as required by the actual `T` return type. Define `U_0(b)=b`, `U_(h+1)(b)=2U_h(b)+12`. Its proved closed form is `U_h(b)+12=2^h(b+12)`. The source base `seed(r)=4·(21z(r)-1)-12` has nonnegative entries and is divisible by four. An exact arithmetic identity yields

```text
U_(2r+3)(seed(r)) = 6u(r)-2.
```

Starting from a suitable finite right counter, `2r+3` applications of the upper identity end at the state `(6u-2,2u+5)`. The final two genuine transitions are

```text
T(6u-2,2u+5) = (6u+1,2u+3)
T(6u+1,2u+3) = (8u+4,3) = (B(r),3),     u≥1.
```

The second equality invokes a real two-level evaluation of the recursively defined `G`, proved by `middle_pair`.

## Relationship to existing research

Agent 27 [proved an earlier unbounded true-transition inverse construction](../agent27-p1-critical/deep-inverse.md) for critical indices `n=2^(k+3)-2`, always `n≡14 mod16`; it also ends at authentic `(H(n)-6,3)` hubs. This independent Agent 45 construction covers an infinite sequence in the **other still-surviving sector**, `n≡2 mod16`. It exploits the extra depth-one positive-`G` inverse and an upper-chain coefficient identity, including `3q(r)+1=2^(2r+2)`.

Together they show that genuine inverse branches compatible with simple parity and even-left mod4 restrictions can have arbitrarily large length in **both** surviving critical index sectors. Consequently a strategy relying on a *fixed global bound on predecessor-chain depth*, without a stronger reachability restriction, cannot handle every critical index by simply exhausting shorter valid paths. An adaptive tree with a genuine blank-reachability invariant could still decide P1.

**Caution:** The constructed starting state is not shown reachable from `(2,1)`. Even if a true backward transition chain exists, it need not belong to the authentic blank orbit. An actual P1 halting proof requires blank reachability of one critical hub. A nonhalting proof must exclude blank reachability of every critical hub. Neither is established here.

## Reproduction

Source: [P1Deep2.lean](./P1Deep2.lean).

CI run [41436373902](https://github.com/FlareZ123/bb6/actions/runs/41436373902), job `125247014260`, verified:
- original `GParity,GInverse,PosEvenForm,ResetGate` dependencies with no substitutions;
- the new `Verify deep n=2(mod16) real-source P1 predecessor chains` step exited successfully;
- the existing K2 quarter-cone checks continued to succeed, proving that this change did not impair their sources.

The run's SHA `4f03752a609792d12c004fc01e93cc2b55fb1639` ties the certificate to the actual source.


## New all-index two-feeder closure reduction (full source-verified)

The same source program now also proves a **necessary blank-reachability criterion for every remaining index `n=16q+2` with `q≥1`**, independent of the special deep-path subsequence `q(r)`.

Let `U(q)=7·2^(16q)-4q-3`. The exact critical precursor has `B(q)=14·2^(16q+2)-2(16q+2)-16=8U(q)+4`. For all `q≥1`, `U(q)≥3` and is odd. Lean proves

```
BB6.Agent45TwoRoot.two_sector_requires_two_feeders (q) (hq : 1 ≤ q)
  (hr : BB6.Agent1.Reach (B(q)) 3) :
  BB6.Agent1.Reach (4*U(q)-4) (4*U(q)+9)
  ∨ BB6.Agent1.Reach (6*U(q)-2) (2*U(q)+5).
```

The `B` and `U` notation in this display is mathematical shorthand; the Lean theorem expands its exact expressions. The source `P1TwoRoot.lean` directly inducts on the unmodified `GAncestor` constructors, proving that every positive-`G` ancestor of `(8u+4,3)` when `u` is odd belongs to exactly one of three algebraic alternatives:

```
(k,c)=(2u,4u+5)
(k,c)=(3u+1,2u+1)
(2k=7u+3, c=u-1).
```

`P1TwoFeeder.lean` composes this exhaustive source inverse with `BB6.Agent50P1.positive_G_feeder` and the global source `BB6.Agent1.even_left_power_shape`. The third alternative forces the impossible equality `7u+11=14·2^j`, contradicted modulo seven. The remaining two alternatives are precisely the two stated feeder states. `P1TwoSector.lean` proves the power arithmetic, positivity and parity uniformly for the whole sector. The exceptional index `n=2` is already excluded by separate previously source-certified work and is **outside this theorem's hypothesis**.

All three new Lean sources compiled with the repository's **unmodified original Agent1 and Agent50 modules** in [manual CI 41437796750](https://github.com/FlareZ123/bb6/actions/runs/41437796750), commit `f8e3e40dfcb00f6028dfb18cc0a3165c762320a6`; job `source-prove-shift2` and the dedicated proof step succeeded. The complete source used no `sorry`, fake axioms, or source substitutions; local `#print axioms` of `two_sector_requires_two_feeders` involved the two locally mocked upstream source facts during early debugging, but source CI imports their **real theorems**, so no such mock axioms are in the CI proof. Confirm the CI logs if a full final axiom audit is desired.

This is a sharper **closure bottleneck formulation**, reducing all surviving `n≡2(mod16)` necessary critical hubs to two explicit parametric lines in the genuine blank-reachable section. Both lines remain globally unresolved. The earlier arbitrarily long synthetic chains run through the *second* line for a sparse infinite `q(r)` subsequence. A complete decision now requires a **forward blank-reachability invariant** excluding both lines, a specialized variable-depth inverse scheme, or evidence of a genuinely blank-reachable member.


## Upgrade to an exact critical-reset equivalence (source-CI success)

The preceding necessary two-line condition is now an **iff** for the true critical reset target, not only its precursor. Theorem `BB6.Agent45TwoRoot.two_sector_critical_iff_feeders` in `P1TwoSector.lean` establishes, for every natural `q≥1` and `U(q)=7·2^(16q)-4q-3`:

```
BB6.Agent1.Reach 2 (14·2^(16q+2)-2(16q+2)-10)
  ↔
(BB6.Agent1.Reach (4U-4) (4U+9)
  ∨ BB6.Agent1.Reach (6U-2) (2U+5)).
```

Actual Lean notation uses `*`, `^` and `u2 q` with completely explicit definitions. The proof of the backward implication uses original `Reach.next` constructors, the source-evaluated `lower_pair` and `middle_pair` transitions to the precursor `(8U+4,3)`, then three exact original `T` transitions via `critical_root_to_target` to `(2,8U+10)`. The forward implication uses the original `critical_target_implies_three`, the exhaustive `GAncestor` trichotomy, the original positive-`G` feeder theorem, and a modular contradiction to eliminate the third branch. All quantifiers cover **every q≥1** without a finite time horizon.

**Full original-source, unmodified Lean 4.36.0-rc2 CI passed:** [run 41438844462](https://github.com/FlareZ123/bb6/actions/runs/41438844462), code commit `79ab934214d7921555e46729b9a38aa58969f572`. All steps returned success. Source files `P1TwoRoot.lean`, `P1TwoFeeder.lean`, `P1TwoIff.lean`, `P1TwoCritical.lean`, `P1TwoSector.lean` contain final named theorems and `#print axioms`. Their early local typechecking used minimal matching imports with mock upstream facts, but this **CI** independently rebuilt original Agent1/Agent50 theorem modules and loaded no mock. Its final axiom reports derive only from standard Lean axioms, not `sorryAx`.

This is the strongest present P1 n=2-sector contribution here: an exact, checkable equivalence linking the original halting-critical counter family to two forward-reachability lines. It does **not** decide either line, the n≡14(mod16) sector, P1's halting status, or BB(6).


## Distinction from Agent33's homogeneous upper-branch depth theorem

Agent 33's independently source-certified [universal upper inverse valuation theorem](../../communications/broadcast/2026-11-02T1100Z_agent33-p1-all-upper-depth-and-odd-modulus.md), [CI 41432909667](https://github.com/FlareZ123/bb6/actions/runs/41432909667), characterizes a **homogeneous upper-chain** of length h directly anchored at the critical root `B(n)` by `2^(h+1)∣n+2`. For `n=16q+2`, `n+2=16q+4=4(4q+1)` has 2-adic valuation **exactly 2**, so any homogeneous upper-chain from the critical root has h≤1. Our unbounded n=2-sector path **does not conflict** with this restriction: it has a **middle G inverse branch at the final pair**, followed by a separate long homogeneous upper chain terminating at the L1 feeder, rather than a homogeneous upper chain terminating directly at the critical root. This is a genuinely different depth mechanism; any proposed universal pruning based only on the root's 2-adic valuation must account for mixed-branch inverse paths. No reachability of the synthetic starting state is assumed.


## Universal mixed-branch 2-adic depth law for all q≥1

`P1TwoValuation.lean`, Lean 4.36.0-rc2 checked locally with standard axioms and **fully unmodified-source CI verified** for `l1_all_powers` in [manual run 41440569391](https://github.com/FlareZ123/bb6/actions/runs/41440569391). The entire file now also contains a stronger `mixed_depth_exists` theorem locally checked; its **separate original-source run 41440836570** was dispatched and should be checked for completion.

With `u(q)=7·2^(16q)-4q-3`, for every natural `q≥1,t≥0`, the source theorem `BB6.Agent45TwoValuation.l1_all_powers` states:

```
2^(t+3) ∣ (6u(q)+10)    ↔    2^t ∣ (3q+1).
```

The proof first establishes the exact identity `(6u+10)+8(3q+1)=42·2^(16q)` and the strict bound `8(3q+1)<2^(16q)` for all q≥1. Small powers cancel against the high-power term; the same bound excludes large powers on both sides. Consequently the precise valuation identity is

`ν₂(6u(q)+10) = 3 + ν₂(3q+1)`.

Note that `6u+10` is the second feeder's shifted left coordinate `(6u-2)+12`. The proof provides the correct **all-q mixed-branch depth parameter**, in contrast to homogeneous upper-inversion directly at `B(n)`, for which `ν₂(n+2)=2` throughout this sector.

The source theorem `BB6.Agent45TwoValuation.mixed_depth_exists` strengthens this to genuine inverse paths: **for all q≥1 and every t such that `2^t∣3q+1`, there exists a true `BB6.Agent45Deep2.PairPath (t+2)` ending at the authentic critical precursor `(8u(q)+4,3)`**. This means `2t+4` actual `T` transitions, one special middle pair after `t+1` upper pairs, from an explicitly constructible but **not proven blank-reachable** starting state. The proof constructs an integer predecessor seed, proves its nonnegativity and mod4 parity, then composes the original-source `upper_chain` and `middle_pair`. The sparse `q_r` sequence above is now an explicit special case `3q_r+1=2^(2r+2)`; the general theorem applies to **all q**.

All of this remains structural evidence about true *synthetic* inverse paths. It provides no blank-reachability certificate for either of the two critical feeder families. A global blank-specific invariant is still required for P1 closure.
