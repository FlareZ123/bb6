# F424/F412 outer stepSym composition audit

**Date:** 2026-11-21T23:35:42.714Z  
**Auditor:** Agent 38  
**Source:** `google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a`  
**Status:** source-level derivation and gap inventory; not exact-import Lean acceptance.

## Direct BB mode

The input left list has at most 94 tokens. The current `sweepBB_within` theorem gives a cost at most
`50 * (pilotListFieldMax L + 1) * (L.length + 1) ≤ 50(M+1)*95 < 2^13(M+1)`.
The repeat-block parameters are read from the left list, and the recursive calls use its suffixes; changes made by `eatB1/eatB2/eatB12R` are to the right list only.

## DL mode

The exact source `stepSym` branch is `stepElemThenBB .DL (peelL L) R`.

- `peelL` expands only the head token, by at most five net tokens (the largest case is `rep12 (m+2))); hence the peeled left list has length at most 99 when `T≤94`.
- A small field lemma is still needed in the costed wrapper: direct case analysis of `peelTok` gives `listFieldMax (peelTok t xs) ≤ listFieldMax (t::xs)`, hence `listFieldMax (peelL L) ≤ listFieldMax L`. The current `SymRunTraceStats.lean` has the length and numeric-sum facts but not this field-maximum lemma. It is straightforward: zero repeats are unchanged; counter-1 repeats expand only to run-0/run-1 tokens; larger repeats expose run-0/run-1 literals and decrement their counter.
- The only BB-producing `stepElemDL` branch is the left run-0 case. It removes that head and leaves a suffix of the peeled left list, so the BB sweep sees at most 99 tokens and left maximum at most M. The one atomic transition costs at most `25(M+1)`; the ensuing BB sweep costs at most `50(M+1)*100`. Total is below `2^13(M+1)`.
- The left run-2 / right run-`d` branch does **not** enter BB: source `stepElemDL` returns CB and prepends `d+1` zeros. Its atomic cost is `3d+22≤25(M+1)`, and it does not trigger `sweepBB`. The next CB state's token count may grow, so the per-step premise `T≤94` must come from the trace-specific `traceStats` folds, not from a generic one-step token invariant.
- Other DL branches remain DL/HALT or are unchanged and cost no more than the same atomic bound.

Thus the DL-mode cost is comfortably below the stated `2^13(M+1)` scale, provided the `peelL` field lemma is added to the costed wrapper.

## CB mode and macro/fallback split

The current draft bounds the outer CB sweep by `<2^13(M+1)`, and the new numeric-field-sum chain bounds its output maximum by `94M+282`. On the BB-producing fallback branch, the one `stepElemCB` transition adds at most 3 to numeric-field sum, so the BB-sweep input maximum is `≤94M+285`; its total token count is `≤570`.

Using exact BB costs (11/14/25 per repeat unit and at most 9 for an atomic BB item branch), the recursive sweep has at most 571 charged events including the terminal `stepElemBB`. Its cost is
`571*(25*(94M+285)+9)=1,341,850M+4,073,514 < 2^22(M+1)`.
Together with the CB sweep and the fallback atomic transition, the non-macro path is below `2^23(M+1)`.

For a recognized Rule A/B/C macro, the current draft has at most `64,512(M+1)` `stepPure` calls, initial field maximum at most `512(M+1)`, and one-step field growth at most one. The generic costed iteration theorem then gives the `2^38(M+1)^2` macro component; adding the outer CB sweep stays below `2^39(M+1)^2`.

## Concrete remaining proof work

1. Add and use `peelTok_fieldMax_le` / `peelL_fieldMax_le` for the DL-to-BB branch.
2. Add a costed 46-`stepPure` Rule A prelude (`stateA0 (k+1) (d+6) → stateA 0 k d)); the current pilot costs `ruleA_step` and `ruleA_iter` but omits this prefix.
3. Compose the exact `afterSweepCB`, `tryRuleA`, `tryRuleBC`, `tryRuleB`, `afterSplitB2`, and `stepElemThenBB` branches into a full `stepSym_within` theorem.
4. Compile the exact imported source closure under Lean 4.36.0-rc2. The traceStats folds already encode the `T≤94` and maximum-field bounds over every intermediate state of the named traces, but exact import-closure acceptance remains pending.
5. Certify the original `runElemFast` prefix and final `step_DL_zero_halt` transfer.

The source-level bounds are mutually compatible and leave a wide margin under the existing conditional `2^39(M+1)^2` estimate. No halting-time classification is claimed by this audit.
