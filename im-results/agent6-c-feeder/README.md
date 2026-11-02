# Agent 6: finite backward-closed certificates for Machine C

**Status: intermediate formal results; BB(6) remains unresolved.** Machine: `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, accelerated blank entry `(5,0,1)`. The counter transition is copied from published Cryptids; the original machine-to-map bridge is external.

Agents 10 and 11 have proved in Lean that this machine halts exactly if a reachable counter state belongs to the family `(0,2*j,4*j+10)`. The present certificates prove unconditional blank-start nonreachability for **j=0,1,2**.

Files and theorems:

- `NoFirstCFeeder.lean`: copied transition, exact finite-iteration semantics, and `blank_ne_feeder_zero`, excluding `(0,0,10)`.
- `CFeederCertificate.lean`: general-purpose kernel-sound backward-closed finite-set checker. The weighted rank `a+2*k+c` is nondecreasing. A list of states of rank at most B is exhaustively checked for predecessor closure across all source states of rank at most B. Theorem `blank_excluded_by_certificate` excludes any target in such a closed set avoiding the initial state for every finite time. Source states with rank above B cannot transition into the set.
- `NoCFeeder1.lean`: 10-state certificate, B=18; proves `blank_ne_feeder_1`, permanently excluding `(0,2,14)`.
- `NoCFeeder2.lean`: 46-state certificate, B=26; proves `blank_ne_feeder_2`, permanently excluding `(0,4,18)`.

All four files compile with Lean 4.36.0-rc2. Axiom audits report `propext`, `Classical.choice`, `Quot.sound`, without `sorryAx` or `native_decide`. Each `by decide` checks a finite bound in Lean's kernel. Compile the two foundational modules to `.olean` files, then compile the two individual certificates with their location in `LEAN_PATH`. No Mathlib or GitHub CI is required.

The remaining j>=3 feeders are open. Checking finitely many individual j cannot resolve the whole family. A parameterized symbolic reverse invariant, or a finite quotient separating the genuine blank trajectory from all feeders, is the next research objective. This repository work belongs in `im-results/`, not `results/`.

Related repository work: `im-results/agent8-rank-barriers/`, `im-results/agent10-c-funnel/`, `im-results/agent11-c-line/`.

## Source-verified cross-agent feeder consequence (new incarnation, 2026-11-02 14:18 UTC)

`EvenFeeder.lean` imports the **unmodified** Agent 3 arithmetic section and Agent 38 blank-orbit invariant. For every `t≥1`, it proves authentic blank-section nonreachability of `(8*t-1,4*t-1)` and `(1,8*t)`, by composing Agent 3's exact `(1,4*j)` predecessor equivalence with Agent 38's odd-second-coordinate modulo-four image exclusion. The shared [manual CI run 41460541649](https://github.com/FlareZ123/bb6/actions/runs/41460541649) compiled the proof against the original dependencies and passed with Lean 4.36.0-rc2. The latter exclusion is **already implied** by Agent 38's stronger `blank_section_no_one8`; the composition is a reproducibility check and may help future arithmetic analyses, but makes **no mathematical-frontier or holdout-decision claim**. The source filename was added to an existing shared manual workflow to avoid redundant CI proliferation.

## Fifth-stage, *new* infinite Machine C stopping-depth exclusion (14:40 UTC)

**Source-certified result:** [manual GitHub Actions CI run 41463963447](https://github.com/FlareZ123/bb6/actions/runs/41463963447), commit `8ff6d2579e1d96c0d9c52a2c179f8504a2e2019c`, successfully rebuilt all the original Agent 46 source modules, Agent 38's packed third and fourth-stage dependencies, and Agent 3's unmodified inverse-feeder source, then checked **[COneFiveDepth.lean](./COneFiveDepth.lean)** under Lean **4.36.0-rc2**. Final `#print axioms` for all three new theorems reports only ordinary `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or `native_decide`.

The new result is a **source-level, globally quantified**, all-time Machine C restriction beyond the existing fourth-stage halting-basin statement. It is obtained by composing *two already formally proved generic facts in a previously unused way*:

- Agent 3's exact `blank_one_four_iff_feeder`: reaching section `(1,4j)` is equivalent to reaching `(4j-1,2j-1)` for every `j≥1`.
- Agent 38's `blank_section_no_odd_special`: every odd-odd section state with `(a+k)%8=4` and `(a+3k)%16=14` is globally absent from the true blank orbit.

Taking **`j=8t+5`**, the exact affine feeder `(32t+19,16t+9)` meets the two Agent 38 restrictions for **every** `t:Nat`; therefore:

```lean
BB6.Agent6.blank_no_one_index_five_mod_eight (t : Nat) :
  ¬ BB6.Agent3.CReach 1 (4*(8*t+5))
```

From Agent 46's genuine exact halting-level identity `haltLevel 4 depth + 3*depth + 16 = 2^(depth+1)*8+5`, any one-left-counter halting input `(1,k)` with `2*k-3=haltLevel 4 depth` and **`depth % 64 = 48`** necessarily has **`k % 32 = 20`**. Such a `k` is `4*(8*t+5)`, which is permanently unreachable. The theorem `dyadic_one_depth_fortyeight_mod64_excluded` formalizes this for **all** depths, times and counters satisfying the stated conditions.

The final theorem **`blank_halts_iff_fifth_stage_residual`** imports the unchanged **`blank_halts_iff_four_stage_residual`** and strengthens its `a=1` branch by requiring `depth % 64 ≠ 48`, leaving all previous odd-`a≥3` restrictions untouched. This is an exact equivalence for the original halting predicate `BB6.CReachBridge.RunHalts`, not merely a necessary condition or a finite bounded trace.

Prior-art and scope: Agent 38 already proved the generic odd-special image restriction, and Agent 3 the generic feeder equivalence. This composition and its depth-48 exclusion are newly recorded here; they **do not solve Machine C, establish a BB(6) bound, or exclude remaining depth residues**. The result remains in `im-results/` pending stronger holistic closure or independent novelty review. Neither the one-left-counter family with other depths nor the odd-left-counter halting family has been decided.
