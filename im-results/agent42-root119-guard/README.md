# Historical rooted #119: auxiliary halting gate, complete conditional return laws and shield obstructions

**Research state (6 November 2026): exact conditional physical-machine theorems and a source-verified counterexample to a natural local invariant; no all-time authentic blank-start decision.** The detailed [historical research log](FULL_RESEARCH_LOG.md) gives equations, experimental transcripts, and complete proof provenance.

## Authentic source and stopping criterion

The historical #119 root `1RB1LB_1RC---_1LD1LF_1LE0LD_0LA1RF_1LC0RE` has a previously published BusyCoq halting equivalence to the auxiliary machine `1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD` ([source provenance](../agent12-r001-source/README.md)). Here all Lean statements refer directly to the **auxiliary** twelve-rule table, with a physical signed infinite tape.

[Root119Gate.lean](Root119Gate.lean) proves `blank_halts_iff_gate`: an auxiliary blank-origin halt is equivalent to an actually reached D/0 configuration whose two immediate left cells are both 1. [Root119BRegular.lean](Root119BRegular.lean) refines this to a genuinely reached B/0 with the left word `1100 1^r 0` ending under its head, for some natural `r`. This is an exact necessary-and-sufficient **reachable stopping configuration**, and still leaves its blank reachability undecided.

## Infinite conditional return laws

The source-derived Lean modules [Root119BShift.lean](Root119BShift.lean), [Root119BFull.lean](Root119BFull.lean), [Root119DFSweep.lean](Root119DFSweep.lean), [Root119FBSweep.lean](Root119FBSweep.lean), and [Root119WaveNormal.lean](Root119WaveNormal.lean) establish exact all-natural-length return or intermediate transition laws with arbitrary exterior tape. The established F/1 wave with head `h`, a zero at `h−1`, odd-length rightward one-run and a terminal zero makes exactly `4n+5` primitive steps and returns to B at `h−1`, adding exactly one 1 at `h+2n+2`.

**Complementary two-bit wave, verified 6 November:** The new [Root119LeftOneWave.lean.xz.b64](Root119LeftOneWave.lean.xz.b64) is an XZ-compressed, base64-encoded, self-contained Lean import module, pinning its decoded SHA-256 to `658d8fd90fd4c4fdffc3b4b0d0206b55dea69312cc9b71d16823a3d91ba8d6f4`. The theorem `leftOne_wave_explicit` says: if state F reads 1 at `h`, the tape has `t(h−1)=1` and `t(h−2)=0`, all cells `h+1,…,h+2n+1` read 1, and the sentinel `t(h+2n+2)=0`, then after **exactly `4n+7` original primitive instructions** the full configuration is
```text
B, head=h−3, tape=setBit (setBit oldTape (h+2n+2) 1) (h−2) 1
```
with arbitrary untouched exterior. In particular, when the earlier bit at `h−3` was 0 the result is a genuine B/0; the `leftOne_result_zero` theorem proves this. The `leftOne_wave_preserves_noLeft4` theorem preserves **every** left-of-head four-word exclusion of the form `p q r 0` across the entire phase, and `leftOne_wave_reached_shield` also transports genuine blank-auxiliary reachability of the conditional endpoint. Source-original Lean 4.36.0-rc2 workflow [42294786877](https://github.com/FlareZ123/bb6/actions/runs/42294786877) succeeded and printed axiom audits limited to the standard Lean axioms `propext`, `Classical.choice` where used, and `Quot.sound`, without `sorryAx`.

These are exact *conditional* machine laws, not proofs that every blank-root phase meets their hypotheses. The two waves can be composed only when actual tape conditions are established.

## Counterexample to a stronger local B/0 shield

[Root119DoubleShieldFalse.lean](Root119DoubleShieldFalse.lean) proves `double_shield_not_closed` over the unchanged auxiliary transition table. The synthetic B/0 configuration at head 0 with ones **exactly at −6, −3, −1** initially has neither physical left-to-right `1000` nor `1100` anywhere ending at or before the head. After exactly **23 successful primitive steps**, its first return to B/0 has head 3 and contains `1000` at positions −6 through −3, entirely left of the new head. Source-inclusive Lean workflow [42291842177](https://github.com/FlareZ123/bb6/actions/runs/42291842177) succeeded with `#print axioms` of the theorem limited to `[propext, Quot.sound]`; this is a **synthetic** all-tape counterexample and does not imply anything halts from a blank tape. The earlier [Root119FalseShield.lean](Root119FalseShield.lean) independently refutes unconditional B/0 preservation of `1100` alone by a 22-step synthetic return.

A finite original auxiliary blank run through ten million primitive steps has **22,984** B/0 sections. The independently reproducible [two-wave first-return census](test-root119-two-wave-census.cjs) classifies the 22,983 completed consecutive B/0 intervals as **15,176** ten-step returns, **7,508** original one-bit waves, **177** newly covered two-bit waves, and **122** unclassified intervals. Earlier [single-wave census](test-root119-return-census.cjs) classified 299 as other. The 177 new matches are a finite count of actually encountered conditional theorem instances, not a proof covering every future B/0 return. Another bounded observation: all 7,359 recorded B/0 sections with immediate-left suffix `0101` had a 1 immediately **right** of the head. This unproved potential history-sensitive guard still requires an all-time authentic-source proof.

## Remaining mathematical obligation

Prove a phase-sensitive forward-closed **authentic blank-root** tape language or a genuinely reached terminal-gate witness, covering all exceptional B/0 returns and transient forbidden factors. The two source-verified synthetic counterexamples rule out simple unconditional word-avoidance induction; right-of-head information or stronger provenance may be essential. No BB(6) value, universal six-state upper bound, or #119 root decision follows from these conditional facts. External novelty of these local transition identities has not been established; they remain intermediate work in `im-results/`.

The [full research log](FULL_RESEARCH_LOG.md) retains the exact algebra, falsifiers and earlier verifications.
