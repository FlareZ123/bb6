# A 1,728-family B–C–D closed-control invariant for Raw34

**Status:** unconditional all-completion Lean theorem, original-source accepted. It eliminates complicated tape-growth cases by a purely finite-state invariant; it does not establish BB(6) or completely settle Raw34.

## Parametric statement

The Raw34 four-transition root fixes A0=1RB, B0=1RC, C0=0RD and D0=1LC. Let B1, C1, and D1 be arbitrary ordinary transitions whose next state is one of **B, C, D**; each transition has two write values, two directions, and three successor states, hence twelve possibilities. There are exactly `12³ = 1,728` distinct triples of instructions. The other five state/symbol entries remain completely unspecified, including possible halting instructions.

**Theorem:** Every total six-state, two-symbol machine that extends any of those 1,728 partial tables runs forever from the all-zero blank tape. In the source this is:

```lean
BB6.Agent50Raw34BCD.all_1728
  (b1 c1 d1 : Move)
  (hB : b1 ∈ bcdMoves) (hC : c1 ∈ bcdMoves)
  (hD : d1 ∈ bcdMoves)
  (m : Machine) (hm : compatible (parent b1 c1 d1) m) :
  NeverHalts m
```

The source proves that `bcdMoves` contains precisely twelve pairwise distinct write/direction/next-state actions. Its `move_closed` theorem establishes that every permitted action's next state is B, C, or D, allowing the universal theorem to be instantiated without simulation or a hypothesis on tape shape.

## All-time proof

On a blank tape, A0=1RB writes a one and enters state B after exactly one ordinary transition. Thereafter all two-symbol actions at B, C, and D are defined, nonhalting and remain in the set `{B,C,D}`: B0 goes to C, C0 goes to D, D0 goes to C, and B1/C1/D1 are restricted to those three states. Thus control is trapped in a closed nonhalting component under **every possible tape content**. The source checks the one-step blank prefix with `finitePartialRun_sound`, proves the one-step closed invariant `closed_step`, iterates it with `closed_run`, and concatenates the exact prefix to show `NeverHalts` for every compatible total machine. This proves nonhalting even for machines that exhibit extraordinary long or exponentially spaced tape-growth epochs.

**Source:** [Raw34ClosedBCD.lean](../im-results/agent50-raw34-firsthole/Raw34ClosedBCD.lean). Original-source [Lean CI run 46086997664](https://github.com/FlareZ123/bb6/actions/runs/46086997664), artifact [15239686693](https://github.com/FlareZ123/bb6/actions/runs/46086997664/artifacts/15239686693), SHA256 `532b258102dfdac2565fd8f5334434e8bb720a1073eb85ebbc4aafeb5e164c79`. The complete nine-module source closure compiled in Lean 4.36.0-rc2; `all_1728` and its soundness dependencies use exactly `[propext, Classical.choice, Quot.sound]`, without `sorryAx` or `native_decide`.

## Exact new contributions without overlap

The parametric closed class contains `1,728 × 25⁵ = 16,875,000,000` total physical transition tables, but **most are already certified** by previously source-accepted [11+74 side-cycle families](2026-11-27-raw34-eightyfive-infinite-rays-agent50.md), [unary growth](2026-11-28-raw34-unary-growth-agent50.md), [closed C–D](2026-11-28-raw34-closed-component-agent50.md), and [1,206 depth-three side-cycles](2026-11-28-raw34-depth3-1206-cylinders-agent50.md).

The separate exact finite [25-ary union audit](../im-results/agent50-raw34-firsthole/count_accepted_union.mjs), run in [CI 46087244007](https://github.com/FlareZ123/bb6/actions/runs/46087244007), finds that precisely **four** complete B1/C1/D1 five-hole cylinders from the 1,728 class were not already covered. Each contributes `25⁵=9,765,625` physical tables, so the genuinely new disjoint mass is **39,062,500**. The four previously unresolved triple values are:

| B1 | C1 | D1 | Nature of independent proof |
|---|---|---|---|
| `0LB` | `1LB` | `1RD` | B–C–D closed, all tape values |
| `0LC` | `1LB` | `1RD` | B–C–D closed, all tape values |
| `1LC` | `1LB` | `1RD` | B–C–D closed, all tape values |
| `1LD` | `0RB` | `1RD` | B–C–D closed, all tape values |

All four had appeared as long-running third-level candidate children in the finite discovery search; the closed graph theorem settles them *for all time*, without needing to analyze their tape dynamics.

The exact union of all presently accepted Raw34 certificates is **97,509,765,625 distinct nonhalting total tables** among its `25⁸=152,587,890,625` physical completions. The complement of **55,078,125,000** physical completions is **not classified by these proofs**; it must not be called halting, and the overarching BB(6) exact maximum remains open.
