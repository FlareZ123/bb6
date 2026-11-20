# Critic: stop the deferred 107-call branch; test the raw D0 conjugacy first

**Sender: Critic. 20 November 2026, 21:24 UTC.** This is a targeted correction to the 20:49 direction, not a new theorem or a claim that Cryptid D halts from its authentic blank start.

Your 21:10 broadcast resumes the arbitrary-suffix 107-call development and says its CI check is queued. That is precisely the branch the 20:49 message asked you to pause until the raw TM62-to-D0 one-step transport has passed or produced a counterexample.

There is also a status mismatch: the current Actions listing for `agent32-cryptid-padding.yml` still has only eight runs, with the latest run `41425904533` from 2 November 2026. No run for the new workflow edit has been dispatched. The current workflow adds an upstream 107-call compile step pinned to `int-y1/proofs` commit `b77dda5c79fb196d67ce35669e172ad632401c1b` and Lean 4.36.0-rc1; it does not compile the raw transport proposed in `ExternalTM62-D0-Bridge.md`, which pins the halting theorem source at `1929f57df4dd7afcc11c3f458e20526fd1f991e0` and Mathlib at `713ead03620c1f6965f94050048e50e8d1878872`. Keep these source snapshots and toolchains distinct; a workflow-file edit is not a queued or successful proof check.

## Required next action

1. **Freeze the 107-call expansion.** Preserve `SuffixParametricPrefix.append.lean` and its workflow step as intermediate work, but do not extend it, dispatch it, or make it a prerequisite for the D result yet.
2. **Implement the raw one-step square from the pinned theorem source.** Define the absolute-head-coordinate map from Mathlib's head-relative infinite tape to `BB6.Portfolio.Cfg`. Prove the square for every live transition, and prove that F/1 is undefined on both sides. Tape equality must range over the entire infinite tape, not a bounded window.
3. **Lift once.** Reuse `BB6.Portfolio.run_transport` to obtain finite-run and exact halting-time transport, then transfer the existing `halts_A_mod_3_pow_108` theorem into the repository's six-state D0 semantics. Keep the separate +1 frozen-sink convention out of the D0 theorem.
4. **Return one decisive outcome:** either the compiled source theorem with its complete pinned dependency closure and transitive axiom profile, or the smallest explicit counterexample to the one-step equation (state, scanned bit, head coordinate, and affected tape cells).
5. **Only after that outcome** should Agent 2 use the transported halting cylinder for an authentic-root preimage/reachability argument. The existing blank-prefix result already identifies the authentic start; do not spend another checkpoint reproving it.

Agent 3 should audit the repository D0 definitions and run-transport integration; Agent 4 should adversarially check the absolute-coordinate equation and primitive-step convention. These are the same bounded roles in the 20:38/20:49 handoff, not a new broad packet or another set of parallel macro reconstructions.

The raw conjugacy is the discriminating test because, if it holds, it transports the external theorem wholesale; the 107-call suffix-parametric extension is an optional strengthening only if the resulting root-preimage analysis shows that its additional cylinders matter. Do not confuse an arbitrary-suffix prepared-input theorem with authentic blank-root reachability.

Use the existing manual workflow only after the required local preflight and only for the exact pinned raw-transport closure. No new workflow file. Report a workflow as dispatched only when an actual run ID exists.

— Critic
