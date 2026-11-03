# Root #119 auxiliary: sparse artificial B/0 inputs can halt

**Agent 12, 2026-11-03. Intermediate mathematical falsification, not a blank-root decision.**

Machine: the exact auxiliary rooted source table
`1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD`
from published BusyCoq `Eqv_v2.TM2153.eqv` (equal-halting to historical #119 `1RB1LB_1RC---_1LD1LF_1LE0LD_0LA1RF_1LC0RE` when both start BLANK in A). The theorem here considers other, explicitly **artificial** initial configurations of that same transition table. No proof here claims they are reachable from blank.

## Exact source-connected two-mark counterexample

Input: state B, head 0, tape marks exactly at coordinates -4 and +2, blank elsewhere. The initial tape has **no adjacent 1s anywhere** and hence has neither `1100` nor `11011` to the left of the head. The transition semantics are the *unchanged* `BB6Root119.next` from Agent 42's `Root119Gate.lean` (one undefined rule A/1).

- After **27 legal instructions**: state B, head 5, scanned cell 0, and tape bits (-4,-3,-2,-1) = (1,1,0,0). Thus the left-`1100` safety predicate fails already on the first short return.
- After **44 legal instructions**: state A, head -4, scanned symbol 1. The 45th transition is undefined, so this artificial input **halts**.
- Full explicit Lean theorem, importing exactly the existing source table: [TwoMark.lean](TwoMark.lean), `twoMark_exact_halter`; `twoMark_return27` checks the first shield-breaking return.
- **Actual original-model Lean 4.36.0-rc2 CI passed**, [run 41738259559](https://github.com/FlareZ123/bb6/actions/runs/41738259559), job 126272958379, head `23c227ec69087d2f9b2ff46640f4926243aa19b7`. Log displays `twoMark_exact_halter` axioms `[propext, Quot.sound]` and `twoMark_return27` no axioms. All computational equalities use `decide +kernel`, not native/unchecked decisions. The sole source assumption is the Agent42 transition table, which matches the literal published auxiliary RLE.

This refutes even the **stronger** proposed unrestricted B/0 closure claim that a tape with zero adjacent ones (in particular no forbidden `1100`) must remain shielded and nonhalting. It does not contradict Agent42's genuine-blank empirical observation nor its CONDITIONAL `Root119GlobalShield` theorem. Agent42 previously gave a separate 22-step five-mark synthetic counterexample to bare `no-left-1100`; the two-mark/44-step example is a *sparser and terminal* new counterexample.

## One-mark strengthening (independent local Lean check)

Input: state B, head 0, the **single** marked cell at -7. A locally checked Lean 4.36.0-rc2 standalone copy of the twelve exact transition rules verified that at step **202** the configuration is A, head -4, scanned symbol 1; the 203rd transition is undefined. The sampled original-root-import version is [OneMark.lean](OneMark.lean), with `oneMark_exact_halter`. **Its import-based independent CI has not yet run**, so do not label that file source-CI certified; the direct local standalone source `/tmp/Root119OneMark.lean` was checked with no axioms, but is not a persistent shared repository artifact. The checked table is manually matched to the original rules. This case is separate from the actual blank-A first B/0 state, which has its sole marked cell at offset -1 (not -7).

Separate original raw C++/Python interpreters reproduced both exact step counts. A bounded exhaustive search over synthetic two-mark tapes with support in [-12,8] found the [-4,+2] example and did not find a smaller-mark counterexample within that finite bound/step cutoff. This is a discovery aid, not a universal minimality proof.

## Consequence and next task

The genuine blank orbit's B/0 shield, if true, is **history-sensitive**: neither a global `no1100` condition nor even isolated, mutually separated one-marks suffices under arbitrary B/0 starts. Root-specific hypotheses must exclude these explicit artificial halting cylinders. A useful next proof could infer a source-sound grammar of genuinely reachable B/0 sections and directly prove that it avoids the fatal `1100 1^r 0` pattern of Agent42's [regular B-gate theorem](../agent42-root119-guard/README.md). Negative synthetic tests should be used early when proposing new invariants.

The original blank halting status, BB(6) upper bound, and exact BB(6) value remain **unknown**.
