# #429: exact single-state A-corridor halting criterion

## Original-physical all-time theorem

The exact unmodified six-state binary machine is
`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`.
Let `R(n)` be its genuine complete bi-infinite-tape configuration
after `n` successful primitive moves from the blank tape.
Write `A/0(01)^k001` for state A reading the leftmost zero of
the physically present rightward tape word `0(01)^k001`, where the
parameter `k : Nat` is entirely unrestricted.

**Lean-original-source theorem:** The genuine blank run halts **if
and only if** it ever reaches an `A/0(01)^k001` configuration, for
some `k ≥ 0`. Formally,
```
(∃ N, HaltsAfter target429 N)
    ↔ (∃ n k a, run target429 n blank = some a ∧ aGate k a)
```
No synthetic initial tape, artificial bound on `k`, or assumption
about a prior symbolic Junc chart is used.

Source:
[`BB429AGate.lean`](BB429AGate.lean),
theorem `halts_iff_earlier_A_corridor`.
This passed the **unchanged-original-source, SHA-pinned Lean
4.36.0-rc2** audit in
[CI 42585450367](https://github.com/FlareZ123/bb6/actions/runs/42585450367),
job 129054065623, with axioms exactly
`[propext, Quot.sound]`; no `sorryAx`.
The audit also independently checked the quantified backward and
forward corridor theorems.

## Why the reduction is exact

An original B/001 visit is already an exact fatal gate
([Agent 32](../agent32-429-raw-parent/BB429FatalB.lean)).
The only incoming rows of B are A/0 moving right and C/1 moving right.
If a fatal B visit came from A/0, then the predecessor has word
`0001` at its head, corresponding to `k=0`.

If the previous row was C/1, that C/1 must itself have been entered
from B/0. Backtracking these two rightward primitive moves exposes
one additional `01` block at the older B head, without changing
the entire future right tape. This is iterated by **strong induction on
actual blank-run time**. As the root begins in A, the backward chain
cannot extend indefinitely. It reaches an earlier A/0 with some
finite `k`, and that A/0 scans precisely `0(01)^k001`.

Conversely, from any such genuine A/0 state, its first right move
enters the associated B corridor; each subsequent exact B/0,C/1
two-move pair consumes one `01` block, preserving all future cells.
After `k` pairs the authentic B/001 gate is reached and the original
D/1 halt follows. This argument uses source-proved full physical
tape functions, preserving original history and blank-run reachability.

The source explicitly verifies `bGate_has_A_ancestor`,
`bGate_succ_step`, and `bGate_reaches_B001` for all natural
`n` and `k`. It is independent of the narrower
two-parent [`A/0001 ∨ C/1001` gate](../agent3-429-prefatal/README.md),
and logically strengthens that reduction to a **single A-state
regular-language target**.

## Additional exact-runtime and historical geometry

The source also contains `aGate_forces_halt_at` and
`halting_time_iff_A_corridor`:

```
HaltsAfter target429 N
  ↔ ∃ n k a, N = n + 2*k + 3 ∧
       run target429 n blank = some a ∧ aGate k a
```

Thus `N` is the count of successful ordinary transitions; if a
step-scoring convention includes the terminal halt query, that score
is `N+1 = n+2*k+4`. The exact-time original-source theorem and all imported dependencies were
Lean-certified in [CI 42586162764](https://github.com/FlareZ123/bb6/actions/runs/42586162764),
job 129056397951, commit `9b00faf1cafed9c1c4bdfee4b41113502b95be61`,
with only `[propext, Quot.sound]` and no `sorryAx`.

A genuine A corridor has a marked cell exactly `2*k+3` cells
right of the head. The prior-scan lemma
`BB6Coverage.marked_cell_previously_scanned` forces an
earlier physical head visit to that cell. The theorem
`halting_requires_prior_distant_scan` certifies the full
quantified original-run statement:

```
HaltsAfter target429 N → ∃ n k a j d,
  N=n+2*k+3 ∧ R(n)=some a ∧ aGate k a ∧
  j<n ∧ R(j)=some d ∧ d.head=a.head+2*k+3.
```

This unbounded, parameter-sensitive historical head obstruction
is source-certified in the same successful CI 42586162764,
with exactly `[propext, Quot.sound]`.

## Exact remaining research obligation

The hard open problem is to determine whether the actual blank
trajectory ever hits the regular tape language
`A/0(01)*001`. The proven equivalence makes the next target
precise but proves no nonhalting invariant or new six-state Busy Beaver
value. A productive further approach would establish an all-time
original-root invariant excluding this language through the proven
complete source Junc and ScanE transitions. Reachability of
arbitrarily prepared zipper/chart states is insufficient.

This is intermediate original-source mathematical research, so it is
kept in `im-results/`; `results/` remains reserved for
academically significant frontier advances.
