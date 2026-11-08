# Historical BB(6) holdout #310: exact blank-root fatal gate

**Agent 24, 8 November 2026.** This is a new, source-checked, **all-time reduction of a particular unresolved six-state machine's halting problem to a specific finite local tape pattern**. It does **not** decide the machine, imply that the pattern cannot occur, or determine BB(6). Because the remaining gate avoidance problem is open, the contribution belongs in `im-results/`.

## Exact machine and fatal configuration

The October 16 frozen list at [`resources/BB6_holdouts_663_2026-10-16.txt`](../../resources/BB6_holdouts_663_2026-10-16.txt), line 310, gives:

```
1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---
```

In state names A=0 through F=5, the only halting entry is F reading 1. The only transition entering F is E/1 → write 1, move left, F. The only transition entering E is C/0 → write 0, move left, E. Both moves head left, and neither rewrites the cells to which the head next travels.

Hence the **exact three-attempt fatal gate**, checked against the literal source semantics, is:

```
    ... 1  1  [C/0] ...
        -2 -1   0       (positions relative to C's head)
```

Here `[C/0]` means state C scanning 0 and the positions immediately left of the head are both marked 1.

The source file [Root310Gate.lean](Root310Gate.lean) includes the full original machine table, the exact all-state lookup lemma `halt_slot_310`, the two **unique predecessor** lemmas `predecessor_F` and `predecessor_E`, and:

```lean
theorem critical_310_iff (c : Config) :
  gate310 c ↔
    ∃ c1 c2 : Config,
      rawStep root310 c = some c1 ∧
      rawStep root310 c1 = some c2 ∧
      rawStep root310 c2 = none
```

This is an equivalence for **arbitrary complete infinite tapes**, including those never reached from blank; the explicit tape preservation at the two left neighbors is proved rather than inferred from state labels. The quantified **actual blank-origin** theorem `root310_halts_iff_gate` states:

```lean
(∃ n, (run root310 n blank).isSome = true ∧
      run root310 (n+1) blank = none)
 ↔
(∃ n c, run root310 n blank = some c ∧ gate310 c)
```

The separate [Root310Criterion.lean](Root310Criterion.lean) proves the more directly useful universal form:

```lean
NeverHalts root310 ↔
  ∀ n c, run root310 n blank = some c → ¬ gate310 c
```

This theorem exposes the **single missing invariant** for this particular root, with no assumptions about finite cutoff, periodicity, or restricted tape support. It is logically equivalent to deciding nonhalting; it does not supply the required forbidden-gate invariant itself.

## Original-source Lean verification

The manual [workflow](../../.github/workflows/agent24-root310-gate.yml) compiles the **unchanged, actual `BB6Coverage.Frontier` semantics** in `im-results/agent8-coverage-contract/Frontier.lean`, then these two new modules with Lean 4.36.0-rc2. The direct original-source executions both passed:

- [GitHub Actions 42537023767](https://github.com/FlareZ123/bb6/actions/runs/42537023767) checked the literal finite-step and actual all-time blank-run equivalence.
- [GitHub Actions 42537125139](https://github.com/FlareZ123/bb6/actions/runs/42537125139) additionally checked `root310_never_iff_forbid_gate`.

Lean `#print axioms` reports only `[propext, Quot.sound]`, no `sorryAx`, custom axioms, or `native_decide`.

## Finite search and obstruction to immediate closure

Independent raw simulation of the exact literal table for **1,000,000 ordinary transitions** observed **133,570 visits to C reading 0**, without any of these visits having two 1s immediately left. This is a bounded observation only, **not a nonhalting proof**. At 20,000 raw steps the root still had only 16 marked cells across a width-77 finite support; at 3,000,000 raw steps it had 39 marks, showing why finite-support translated cycles were unlikely. No exact-shift recurrence was observed within that period.

A finite head-centered abstract reachability calculation which distinguishes untouched zero from visited zero was attempted at radii 1 through 7. Every radius admitted a **spurious potential halt**, with the earliest abstract false-gate depths increasing from 7 to 55 as radius grew. This failure belongs to the deliberately coarse *overapproximation*, and says nothing about a real blank-origin halt. Increasing the fixed window blindly is unlikely to yield the missing invariant.

**Highest-value next task:** Prove an inductive **root-reachable tape-language condition** excluding precisely the C/0-left-`11` pattern. A regular or structured unary/alternating grammar over complete tape sections, or an exact return map preserving a stronger suffix/counter relation, can provide the desired universally quantified invariant. The Lean source already supplies the exact machine-specific goal and the halting/nonhalting bridge, so future researchers can avoid rebuilding predecessor logic.
