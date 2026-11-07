# #429: authentic raw halting gates and physical right-frontier obligation

**Verified status (7 November 2026).** The six-state blank-root machine
`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` halts **if and only if**
its genuine original raw trajectory reaches either of two equivalent local events:

- A state **B** scanning `001` at its head and two cells to the right.
- A state **C** scanning `0`, with a marked `1` immediately to its right.

Both all-time equivalences are compiled using the repository's unchanged six-state, two-symbol, bi-infinite-tape definitions. The second form admits a causal geometric consequence: **if the machine ever halts, it must previously have scanned a head coordinate one cell to the right of a later C/0 visit.** In particular, a complete proof that every genuine C/0 entry lies at or beyond *all previously scanned head coordinates* would prove nonhalting.

**That universal geometric premise is unproved.** These theorems do not decide #429, another holdout, or BB(6); they are an intermediate reduction in `im-results/`, without a claim of academic novelty.

## Exact source theorems

Let `M = BB429PhysicalFrontier.target429` be the complete literal twelve-input machine, `R n = BB6Coverage.run M n BB6Coverage.blank`, and `h = c.head`. All existential quantifiers over configurations refer to **actual successful blank-root raw steps**; no arbitrary synthetic tape is admitted.

[BB429FatalB.lean](BB429FatalB.lean) proves the first equivalence:
```lean
(∃ n, HaltsAfter M n) ↔
  (∃ n b, R n = some b ∧
     b.state = B ∧ b.tape b.head = false ∧
     b.tape (b.head+1) = false ∧ b.tape (b.head+2) = true)
```
The proof factors the unique authentic halting row D/1 into a C/0 parent and then a B/0 grandparent, using an all-time F-entry adjacent-write exclusion proved in [BB429FEntry.lean](BB429FEntry.lean). For a B/001 event at successful-step index n, the halt occurs after n+2 further successful steps, and the final halting query is score n+3.

[BB429FreshFrontier.lean](BB429FreshFrontier.lean) proves the second, strictly physical event equivalence:
```lean
(∃ n, HaltsAfter M n) ↔
  (∃ n c, R n = some c ∧
     c.state = C ∧ c.tape c.head = false ∧
     c.tape (c.head+1) = true)
```
A genuine B/001 event forces this C/01 configuration by the exact B/0 right move; conversely, C/01 forces the genuine C/0 right move into D/1, which halts. The forward direction uses the independently source-checked B/001 theorem rather than assuming any geometric conjecture.

The same module proves `halt_requires_a_prior_right_head`: if M halts, there are times `k < n` and genuine reachable configurations `d = R k`, `c = R n` with `c` at fatal C/01 and `d.head = c.head + 1`. This uses the **machine-independent** theorem in [FreshCell.lean](FreshCell.lean):
```lean
c.tape y = true ∧ R n = some c →
  ∃ k < n, ∃ d, R k = some d ∧ d.head = y
```
where here `R` can be the blank-origin run of *any* six-state machine in `BB6Coverage`. The proof is by induction on successful raw execution steps, recognizing that only a scanned head cell can be written. Its corollary `blank_right_of_scanned_frontier` states that if all past head positions are at most `c.head`, then `c.tape (c.head+1)=false`. The #429 theorem `all_C_zero_at_record_head_implies_nonhalt` applies this fact to every actual C/0 entry.

These are reusable causal constraints on physical tapes, with no assumptions about finite tape windows, bounded simulation, or accelerating return sections. They remain **conditional** on an unproved all-time property when used to claim nonhalting.

## Verification and provenance

- [Original B/001 source CI 42321557497](https://github.com/FlareZ123/bb6/actions/runs/42321557497), original proof commit `05b9001119d164bb209028657594c8a914da0d5d`, successful.
- [Original universal F-entry source CI 42320830215](https://github.com/FlareZ123/bb6/actions/runs/42320830215), commit `c5a5634bd1b1e43ea4b0ff9c8db547ec038e3319`, successful.
- [Extended original-source CI 42334364089](https://github.com/FlareZ123/bb6/actions/runs/42334364089), successful. This recompiles the unchanged Agent8 `Frontier`, Agent1 `BB429PhysicalFrontier`, the original predecessor theorems, and all new causal/frontier statements with Lean 4.36.0-rc2. `#print axioms` declarations are present and the workflow rejects `sorryAx`. Local compilation of the new algebraic proof against an interface-compatible test stub passed, but this is secondary to the actual unchanged-source CI.
- [Existing manual-only workflow](../../.github/workflows/agent32-429-raw-parent.yml) includes both new modules and retains their original ancestors. It has no per-commit trigger.

Original published Cryptids [#429 machine and acceleration](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean) reduces its authentic blank run to a high-level counter map, with potential halting at a specific counter equality. Agent6's [44/1024 original-source necessary sieve](../agent6-harmonic429/README.md) and Agent1's [673/928 exact inverse filters](../agent1-429-262144-sieve/README.md) already provide substantially stronger high-level arithmetic restrictions. Their original-root quantifiers remain unresolved, and no inclusion/novelty claim over those reductions is made here. The raw C/01 characterization is an alternate physical framing, not a replacement for those filters.

## Remaining obstacle and falsifiable next experiment

To turn the conditional head-record theorem into a machine decision, establish **for all n** that a genuinely reached C/0 at time n has head coordinate at least every earlier genuine head coordinate. This is a very strong statement: Agent1 independently simulated **two billion** raw moves and observed 555 genuine C/0 visits, all at record-right positions, while this repository's earlier 50-million-step screen found the same pattern. Those observations are finite. The pinned external source labels the eventual halt as a *heuristic* possibility at a vastly larger horizon; that heuristic is neither a proof nor a contradiction of this conditional theorem.

A direct falsifier is a reachable C/0 whose current head lies strictly left of an earlier head, even if the next right cell is zero. A decisive affirmative proof must control the actual history-sensitive tape through every exceptional accelerated return. Because the C/01 event is an **exact** halt gate, another useful route is to prove it reachable with a genuine blank-origin witness. Avoid extrapolating from a finite cutoff or treating a synthetic right-tape pattern as an authentic visit.

The new causal theorem may help translate the original accelerated `J(u,w)` return language into a geometric condition. It supplies no universal score upper bound and no exact BB(6) value.


## Agent 32 addition: E/1 shift and finite blank-prefix closure

These results complement the conditional physical C/01 reduction above. They are
intermediate and do not decide the unbounded orbit.

### Exact `shift_E_11` prefix

The pinned Cryptids helper `shift_E_11` at commit
[`c86f15861709b76042998c5211c7b2f83991621b`](https://github.com/google-deepmind/cryptids/tree/c86f15861709b76042998c5211c7b2f83991621b)
has, in the local nearest-first zipper convention, start shape

```text
state = E, current = 1
left  = 1^(2k) ++ tail
right = 1^6 ++ suffix
```

`BB429E1ShiftDelta.e1_left_prefix` proves that every prefix `j ≤ 2k`
has state E/current 1, left `1^(2k-j) ++ tail`, right
`1^(j+6) ++ suffix`, and exact head displacement `-j`.
`shift_E11_total` gives displacement `-2k`.

`BB429E1ShiftPhysical.physical_E1_step` uses the literal raw `target429`
row and `BB429PhysicalBridge.leftRep`. The theorem
`physical_left_prefix` lifts the result to
`BB6Coverage.run target429` for every raw configuration satisfying
`Represents`. The corollary `physical_shift_E11_mark_persists` proves
that the original E/1 cell still contains one after every positive prefix.

This proves one-sided motion inside the helper. It does not prove that the
later orbit never returns to those cells.

### Blank-origin finite witnesses

`BB429E1ShiftRootWitness` computes directly from the raw blank configuration:

- At step 122, the head is at coordinate 4 in E/1, with eleven ones to the
  left and six ones followed by `01` to the right. This is the local k=3
  start shape of the E/1 shift.
- The next six E/1 instructions have head positions
  `4, 3, 2, 1, 0, -1, -2`.
- The head later returns to coordinate 4 at step 192, so those six writes
  are not global last writers.
- A single-pass raw trace through pre-instruction step 2678 classifies every
  D/0, E/1 and F/1 left-writing instruction. Every such write is at a
  coordinate at most 29, and the head is at coordinate 29 at step 2679.
  Therefore every possible left-writer source in this finite prefix is
  crossed by a later head before any possible halt after step 2679.

The last statement is a finite computation checked by Lean `native_decide`.
It is not an all-time theorem.

### Additional CI

The exact zipper prefix passed [Agent32 E/1 CI run 42376334499](https://github.com/FlareZ123/bb6/actions/runs/42376334499).
The raw physical prefix and persistent-mark theorem passed
[Agent18 workflow run 42376526145](https://github.com/FlareZ123/bb6/actions/runs/42376526145).
The blank-origin finite witnesses and the 2679-step left-writer closure passed
[Agent18 workflow run 42377735415](https://github.com/FlareZ123/bb6/actions/runs/42377735415).
All modules contain `#print axioms` audits; these CI runs completed without
`sorryAx` findings.

### Remaining question

The finite prefix closes all candidate D/0, E/1 and F/1 writes only through
step 2678. The global last-writer theorem still requires a uniform
source-connected criterion for every high-level J transition. The local
E/1 sweep is one-sided, while subsequent macros can return across it. A
proof must compose those later returns with the raw head history; neither
the helper theorem nor a finite prefix settles the unbounded orbit.
