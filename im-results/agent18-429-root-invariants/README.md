# Genuine blank-root predecessor tower for BB429 (Agent 18, 2026-11-05)

This is a mathematical research intermediate for the unchanged source-equivalent BB429 accelerator, not a decision of machine #429 and not a BB(6) upper bound. The original raw six-state machine is `1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA`. All claims below concern the *actual blank accelerator root* `BB429.run n (0,0)`, using the exact `next` definition in `im-results/agent5-429-rank/BB429Rank.lean`.

## Three all-time congruence theorems

[BB429SevenStrong.lean](BB429SevenStrong.lean) proves, for every `n,a,b:Nat` and `BB429.run n (0,0)=some(a,b)`:

1. `a%8=7 → b%8∈{2,3}` (`rooted_seven_strong`).
2. `a%16=1 → b%8∈{1,2}` (`rooted_one_strong`).
3. `a%32=5 → b%8∈{2,4,5}` (`rooted_five_strong`).

This improves the older source-certified individual restrictions of Agent39, `a%8=7→b%8≠7`, `a%16=1→b%8≠6`, and `a%32=5→b%16≠1`, respectively. The first is combined with Agent39's earlier `rooted_positive_even_eight`: a true-root parent having positive even first counter has second counter 2 mod8.

Each strengthening has a standalone *exhaustive one-step* Lean theorem `incoming_{seven,one,five}_strong` and a derived all-time blank-root theorem by induction on the exact accelerator time. The proof relies on the genuine source step, not on any finite screen, heuristic simulation, or synthetic root.

### Why the tower works

The only possible incoming transitions to sufficiently large odd first counters are the first branch `(x,y)↦(2x+3,y-2x-3)` or the non-first odd-`y` branch `(x,y)↦(d+7,2y-4)`. This is also contained in Agent6's exhaustive `odd_inverse`. In the first branch, congruence `a%8=7` forces even `x`, and true-root even8 forces `y%8=2`, hence output `b%8=3`. In the non-first branch, the target residue and source guard require `b%8=2`; the alternative would force an impossible odd second counter at a positive even true-root parent. For `a%16=1`, the first branch reduces to the newly proved parent `x%8=7`, giving `b%8=1 or 2`; the non-first branch gives 2. For `a%32=5`, the first branch reduces to parent `x%16=1`, giving `b%8=4 or 5`; the non-first branch gives 2. The Lean one-step proofs split every original `BB429.next` branch and invoke `omega` on the complete nonlinear-guard cases.

The corollary `no_halt_five_mod32` proves `a%32≠5` for every genuine terminal `b+1=2a`, because that terminal would have `b%8=1`. **This complete terminal sector was already ruled out by earlier Agent6 work** and is included as a short demonstration of mathematical consumption, not a novel machine-decision claim. The other two new predicates have so far furnished stronger root structure without deciding a surviving original-source halting sector.

## Reproducibility and verification boundary

All seven new theorem declarations, including the three one-step lemmas and full-cylinder corollary, were locally checked in Lean **4.36.0-rc2** with axiom audit reporting only `[propext, Classical.choice, Quot.sound]`. We independently compiled exact local reproductions of the unchanged source `BB429.next/run`, `BB429Mod8.Allowed/all_blank_returns_allowed` and `BB429RootEven8.rooted_positive_even_eight`; there were no stubs, extra axioms, or untrusted proof declarations in this local test. Files under `/tmp/bb6research` were local only and may not survive future invocations.

A separate unchanged-*repository*-source check is prepared in the new **manual-only** [GitHub Actions workflow](../../.github/workflows/agent18-429-strong-root.yml), compiling the original checked-in source modules before our new file. Its dispatch was **blocked by the connector safety layer** during this invocation; do not cite a successful GitHub CI run until one actually executes and passes. A locally compiled exact source reproduction is weaker provenance than that direct source audit. Upstream pinned raw-machine certification of the new statement is also separate; prior agents already bridged this accelerator to that original machine, and we did not recompile the external original source for the new statement.

For a source audit, manually invoke `agent18-429-strong-root.yml` on `main`, inspect actual steps, and verify each printed axiom list. This workflow has no automatic per-commit trigger.

## Related work, limits, and next test

- Agent39: `im-results/agent39-429-1021/BB429RootEven8.lean`, `BB429RootMod16.lean`, `BB429RootMod32.lean`, and `BB429RootMod64R0.lean`, all weaker or different root restrictions.
- Agent33: `im-results/agent33-429-24/BB429InverseKernel.lean` is a generic *source-sound* affine inverse certificate. Adding the three new root predicates as new `Bad` leaf cases is a feasible next experiment; the existing `Bad` handles only the older narrower conditions.
- Local exploratory counterpart `cert7.py`, **not committed**, extended Agent33's affine inverse certificate heuristically with these predicates, comparing depths ≤14 over moduli 128 through 8192. Its additional excluded individual classes `{5,29,61,317,509}` modulo8192 were outside the current 24/2048 live-gate list, hence **no newly decided surviving terminal class** was found by this finite-depth probe. This is an exploratory overlap audit, never a proof of a complete unknown sector.
- The next valuable proof would derive a source-confirmed blank-root ancestry restriction for an entire *surviving* original machine terminal family, rather than extending finite congruence depth without an endgame.

All three new theorems are fully quantified over natural time and counters. Scientific priority relative to external published results remains unreviewed. The real #429 root and the global BB(6) problem remain open.
