# Agent 42: Machine C has no accelerated cycles and bounded target reachability

**Status:** intermediate structural theorem for the full published Machine C counter accelerator. The machine's halting status, every remaining gateway class, and BB(6) remain **undecided**. This is a locally Lean-verified and **independently CI-checked** source-level result, not a publishable BB(6) bound.

## Exact model and mathematical statements

The deterministic partial accelerator is `BB6CLine.nextC` from the **unmodified** `im-results/agent11-c-line/CLine.lean`. The original published six-state machine is `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`; Agent 21 separately certified its original-machine/accelerator halting correspondence in pinned-upstream CI [41389979481](https://github.com/FlareZ123/bb6/actions/runs/41389979481). Our statements concern the accelerator's successful transitions, not the number of raw Turing-machine steps.

For a counter state `s=(a,k,c)` define

- weighted rank `R(s)=a+2k+c`;
- secondary potential `P(s)=a+c`.

A complete exact transition-case proof shows that whenever `nextC(s)=some(t)`, either `R(s)<R(t)`, or `R(s)=R(t)` and `P(t)<P(s)`. Hence the lexicographic progress measure forbids any positive-length loop, **from any initial counter state**, not just the blank-entry state. In Lean: `no_positive_cycle`, transported to Agent 11's source as `source_no_positive_cycle`.

The proof further shows that if a successful run of `n` steps stays on one fixed rank, then `P(t)+n≤P(s)`. Thus surviving `R(s)+1` calls strictly increases rank (`rank_growth_after_rank`).

### Universal quantitative bound

For any integer `B≥0`, on states whose weighted rank is at most `B`, define

```
score_B(s) = R(s)*(B+1) + (B-P(s)).
```

Every successful step with target rank at most `B` increases this integer score by at least one, and the score always satisfies `score_B≤(B+1)^2-1`. Therefore:

```lean
theorem escape_rank_by_square (B : Nat) (s t : S)
    (h : run ((B+1)*(B+1)) (some s) = some t) :
    B < rank t
```

This yields an effective finite-target criterion **for every source and target**:

```lean
theorem hit_target_iff_bounded (s target : S) :
    (∃ n, run n (some s) = some target) ↔
    (∃ n, n < (rank target+1)*(rank target+1) ∧
          run n (some s) = some target)
```

`source_hit_target_iff_bounded` proves exactly the same statement for runs using `BB6CLine.nextC`, rather than the standalone copy. For the halting thin-gateway family `target=(0,2j,4j+10)`, its rank is `8j+10`, hence a *fixed* index `j` can be decided by at most `(8j+11)^2` accelerated calls. This is a statement about a single target at a time; the infinitely many possible `j` remain the decisive global obstruction. A finite bound on reaching individual targets is far weaker than a uniform decision of the machine.

## Proof files

- [CNoCycles.lean](./CNoCycles.lean): exact `nextC` copy, lexicographic strict progress, no cycles, plateau bound, and rank-growth theorem.
- [CNoCyclesBridge.lean](./CNoCyclesBridge.lean): definitionally checks the copy against the unmodified source `BB6CLine.nextC` and transports the main theorems.
- [CBoundedRank.lean](./CBoundedRank.lean): bounded-rank score, all-start escape bound, run composition, global target iff bounded-time target.
- [CBoundedRankBridge.lean](./CBoundedRankBridge.lean): transports finite-target criterion back to `BB6CLine.nextC`.
- [Manual CI workflow](../../.github/workflows/agent42-c-no-cycles.yml): source-level verification on Lean 4.36.0-rc2, no per-commit run.

**Verification:** complete manual GitHub Actions [run 41405671155](https://github.com/FlareZ123/bb6/actions/runs/41405671155) succeeded on commit `5d14a2965e52c7372992feaefd7cd8260c8d542c`, importing the full unmodified Agent 11 `CLine.lean`, then compiling all four Agent 42 files. The final locally and CI-reproduced theorem axiom audits show only `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, `admit`, or `native_decide`.

## Scope and research use

A deterministic, strictly rank-progressing accelerator cannot enter a genuine finite cycle; that does **not** imply it cannot halt. For Machine C, the known remaining halting condition is an **infinite union of increasingly high-rank target families**. An algorithm deciding individual targets in quadratic accelerated time is compatible with the unresolved universal non-reachability question.

Useful next directions: combine the bound with source-certified finite reachability certificates for the low-index targets; seek a recurrence, automaton, or inductive relation that excludes **every** parameter value rather than running one bounded test per parameter; and use the plateau arguments in section/counter reductions where source-level rank monotonicity is independently established. Do not promote this file to `results/` without external novelty assessment and a genuinely frontier-changing theorem.
