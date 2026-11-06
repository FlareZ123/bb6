# Historical rooted #119: auxiliary halting gate, complete conditional return laws and shield obstructions

**Research state (6 November 2026): exact conditional physical-machine theorems and a source-verified counterexample to a natural local invariant; no all-time authentic blank-start decision.** The detailed [historical research log](FULL_RESEARCH_LOG.md) gives equations, experimental transcripts, and complete proof provenance.

## Authentic source and stopping criterion

The historical #119 root `1RB1LB_1RC---_1LD1LF_1LE0LD_0LA1RF_1LC0RE` has a previously published BusyCoq halting equivalence to the auxiliary machine `1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD` ([source provenance](../agent12-r001-source/README.md)). Here all Lean statements refer directly to the **auxiliary** twelve-rule table, with a physical signed infinite tape.

[Root119Gate.lean](Root119Gate.lean) proves `blank_halts_iff_gate`: an auxiliary blank-origin halt is equivalent to an actually reached D/0 configuration whose two immediate left cells are both 1. [Root119BRegular.lean](Root119BRegular.lean) refines this to a genuinely reached B/0 with the left word `1100 1^r 0` ending under its head, for some natural `r`. This is an exact necessary-and-sufficient **reachable stopping configuration**, and still leaves its blank reachability undecided.

## Infinite conditional return laws

The source-derived Lean modules [Root119BShift.lean](Root119BShift.lean), [Root119BFull.lean](Root119BFull.lean), [Root119DFSweep.lean](Root119DFSweep.lean), [Root119FBSweep.lean](Root119FBSweep.lean), and [Root119WaveNormal.lean](Root119WaveNormal.lean) establish exact all-natural-length first-return or intermediate transition laws with arbitrary exterior tape. In particular, the F/1 forward-and-back wave with head `h`, a zero at `h−1`, odd-length rightward one-run and a terminal zero makes exactly `4n+5` primitive steps and returns to B at `h−1`, adding exactly one 1 at `h+2n+2`. The wave is a **conditional** transition theorem; blank-origin satisfaction across all sections is unknown. [Historic source CI](https://github.com/FlareZ123/bb6/actions/runs/41961744091) checked the F/B law; the historical log records verification scope for the other statements.

## Counterexample to a stronger local B/0 shield

[Root119DoubleShieldFalse.lean](Root119DoubleShieldFalse.lean) proves `double_shield_not_closed` over the unchanged auxiliary transition table. The synthetic B/0 configuration at head 0 with ones **exactly at −6, −3, −1** initially has neither physical left-to-right `1000` nor `1100` anywhere ending at or before the head. After exactly **23 successful primitive steps**, its first return to B/0 has head 3 and contains `1000` at positions −6 through −3, entirely left of the new head. Source-inclusive Lean workflow [42291842177](https://github.com/FlareZ123/bb6/actions/runs/42291842177) succeeded with `#print axioms` of the theorem limited to `[propext, Quot.sound]`; this is a **synthetic** all-tape counterexample and does not imply anything halts from a blank tape. The earlier [Root119FalseShield.lean](Root119FalseShield.lean) independently refutes unconditional B/0 preservation of `1100` alone by a 22-step synthetic return.

A finite original auxiliary blank run through ten million primitive steps has **22,984** B/0 sections, with 15,176 ten-step returns, 7,508 F/1-wave returns, and 299 other returns ([reproducible census](test-root119-return-census.cjs)). Those data constrain which branches a sound root-language proof must handle; they are not exhaustive certificates. Another bounded observation: all 7,359 recorded B/0 sections with immediate-left suffix `0101` had a 1 immediately **right** of the head. This is an unproved potential history-sensitive guard, and must be tested against longer true-root traces and synthetic counterexamples.

## Remaining mathematical obligation

Prove a phase-sensitive forward-closed **authentic blank-root** tape language or a genuinely reached terminal-gate witness, covering all exceptional B/0 returns and transient forbidden factors. The two source-verified synthetic counterexamples rule out simple unconditional word-avoidance induction; right-of-head information or stronger provenance may be essential. No BB(6) value, universal six-state upper bound, or #119 root decision follows from these conditional facts. External novelty of these local transition identities has not been established; they remain intermediate work in `im-results/`.

The [full research log](FULL_RESEARCH_LOG.md) retains the exact algebra, falsifiers and earlier verifications.
