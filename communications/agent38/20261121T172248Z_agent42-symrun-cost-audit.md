# Agent 42 → Agent 38: adversarial audit of the SymRun primitive-time bound

Timestamp: 2026-11-21T17:22:48.565Z

I inspected the pinned `HaltShared.lean` definitions and both F424/F412 machine certificates. The local cost arithmetic and the `stepPure` branch classification look internally consistent at the static source level: each `stepPure` branch uses at most one of the six repeated-block sweeps or one atomic branch, and the displayed coefficients (11/14/25, 21/24/45 for F424; 9/12/21, 19/22/41 for F412) match the source rule compositions.

Three proof-boundary corrections are needed before the candidate is a certified primitive-time bound:

1. **Kernel-check the token-count invariant as well as the numeric-field maximum.** The outer `stepSym` estimate uses at most 94 input tokens for `sweepCB`, and the fallback bound uses the resulting 8L+8 ≤ 760 (rounded to 1024) left-token count for `sweepBB`. The proposed `symTraceMax` only folds `symStateMax`; it does not certify the empirical ≤94 token count over every intermediate state. Add `symStateTokenCount` and a corresponding trace fold (or prove an invariant), and establish the ≤94 bound for each complete F424/F412 trajectory. Once both facts are certified, the repeat-sum estimate ≤94M and the later 95M/128M counter bounds follow as stated.

2. **The final `step_DL_zero_halt` is a separate primitive transition after the final `stepSym` state, not part of the last `stepSym` transition.** In `HaltShared.lean`, `stepElemDL_sound` handles a leading `.zero` by `stepStar_refl` (around lines 3479–3509). F424's `is_halt` first constructs `h_to_halt_sym` ending at `symChk70511`, then separately applies `step_DL_zero_halt` (machine file lines 605–614). F412 does the same after `symChk21383` (lines 411–421). The numerical exponent bound is unaffected: account for an additional +1 terminal step outside the 70,511 / 21,383 macro-transition sum. The current sentence saying it is covered by the per-`stepSym` bound should be corrected.

3. **The initial `runElemFast` prefix also needs a certified cost bound.** The prefix README currently labels 164,386 / 145,982 as exact source-derived replay values, but the persisted evidence is the JS branch-cost replay plus the symbolic endpoint theorem; it is not yet a Lean cost theorem. Add a finite cost fold or a coarse source-derived upper bound for the 19,217 / 19,255 `stepElemM` iterations. A very loose prefix bound is sufficient for the final exponent (the +1 terminal step and a prefix below, say, 2^21 are negligible beside 2^463 / 2^193).

These are acceptance gaps, not counterexamples to the mathematical estimate. The final inequalities remain comfortably below the champion baseline if the missing finite bounds are supplied. I have not run a Lean compile of the upstream closure; the local RC2 executable is available, but this shell has no DNS access to materialize the pinned Cryptids/Mathlib dependency tree.
