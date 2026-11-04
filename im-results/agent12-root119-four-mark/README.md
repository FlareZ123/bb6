# Root #119 auxiliary: four-mark synthetic halter refutes a three-pattern B/0 shield

**Agent 12, 2026-11-04 00:02 UTC. Intermediate original-source model lemma, not a genuine blank-root decision.**

The auxiliary machine is the 12-rule `1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD`, published by BusyCoq as the blank-halting equivalent of historical #119 `1RB1LB_1RC---_1LD1LF_1LE0LD_0LA1RF_1LC0RE`. It uses the unchanged six-row `BB6Root119.next` from [Agent 42's source-table model](../agent42-root119-guard/Root119Gate.lean). All observations about the artificial tape below are deliberately separate from the *real blank A start*, which remains open.

## Precise counterexample

Take state **B**, head **0**, with exactly four marked cells **−6, −5, −3, −2**, blank elsewhere, so that the complete initial left word is `110110` on positions [−6,−1].

This configuration satisfies three stringent universal left-of-head exclusions:
- No `1000` four-cell factor ends strictly to the left of the head.
- No `1100` four-cell factor ends strictly to the left of the head.
- No `1110` four-cell factor ends strictly to the left of the head.

The source-import [Lean module](Root119FourMark.lean) proves all three as unrestricted quantified implications over `x : Int`, i.e. not only a finite window. Nonetheless:
- After **17 successful primitive steps**, the machine is at **B/0, head 3** with `1100` at [−6,−3], strictly left of the live head.
- After **34 successful primitive steps**, it is at **A/1, head −6**, the undefined rule. Thus the 35th step does not exist.
- `fourMark_exact_halter` includes a complete finite formal halting witness, `fourMark_bad17` asserts the earliest listed shield break, and `fourMark_none35` independently checks step35 fails.

**Original-model Lean 4.36.0-rc2 CI passed** [run **41743613012**](https://github.com/FlareZ123/bb6/actions/runs/41743613012), job **126290993461**, compiling the unmodified `im-results/agent42-root119-guard/Root119Gate.lean` followed by `Root119FourMark.lean`. Log shows `fourMark_exact_halter` and all three universal exclusion proofs depend only on `[propext, Quot.sound]`; executable finite checks use `decide +kernel`. No admits or custom axioms.

A separate independent Python literal-table simulation reproduced the 17/34 transitions. This synthetic input is not known to be reached from the actual blank-A start and does not contradict the observed absence of those three patterns at genuine B/0 checkpoints. The counterexample proves the **unrestricted three-pattern shield is not closed** under arbitrary B/0 starts.

## Important exploratory program correction

Before this counterexample, an exploratory finite C++ CEGAR harness accidentally supplied five rows to a `T[6][2]` transition table, silently zero-initializing the F row. Its earlier synthetic "no false positives in 54,272 tests" outcome was invalid and is withdrawn. The corrected complete six-row table has an explicit F0→B and F1→D row, and rerunning the same 54,272 synthetic test cases (up to 10,000 steps each) finds **10,019** shield violations, with 44,253 surviving the finite cap. A separate 501-case left-only test, up to 100,000 steps, finds **102** violations. These counts are finite exploratory evidence, not mathematical statements about true blank reachability. The certified Lean theorem above is independent of those harnesses.

## Connection to complementary uniform physical-run theorems

The [all-length odd-run D/F shuttle](../agent12-root119-shuttle/Root119Shuttle.lean) is independently source-CI certified [41742631333](https://github.com/FlareZ123/bb6/actions/runs/41742631333); the [even-run D0 boundary theorem](../agent12-root119-shuttle/Root119EvenSweep.lean) source-CI passed [41744002913](https://github.com/FlareZ123/bb6/actions/runs/41744002913). These exact physical macros can be applied when a true-root argument establishes their input hypotheses. The four-mark witness shows why the necessary rooted-input restrictions cannot be discarded.

The complete genuine blank-A nonhalting/halting decision of root119, the universal six-state machine classification, and the value of BB(6) remain unknown. Keep this dossier in `im-results/`; peer review and genuine-root application are needed before academic promotion.
