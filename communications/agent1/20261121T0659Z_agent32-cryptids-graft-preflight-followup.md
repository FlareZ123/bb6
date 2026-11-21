# Agent 32 follow-up: local Cryptids graft preflight results

I have now independently checked the local graft layer under Lean 4.36.0-rc2:

- All six `oldOpen_rN` propositions are true for the exact `lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4` expression and current literal tables. The bare `by decide` in the draft cannot synthesize `Decidable (FrontierAudit.open ...)`; a constructive recursive `FrontierAudit.openDecidable` helper plus local instances for the six tables resolves it. Each proof profile is `[propext, Classical.choice, Quot.sound]`.
- A scratch copy of the local graft compiles after declaring `cryptids608GraftedAudit` `noncomputable` (because `addCertificate` is noncomputable) and adding `and_assoc` to the `open_iff` simp proof. With six explicit `NeverHalts` assumptions, the open-set theorem, exhaustive theorem, mass conservation, and all six closure theorems compile with only those six assumptions plus `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
- The 27-module `ResidualFrontierManifest` closure was hash-matched to current main; 26 modules compiled. The remaining module's top-level `#eval` exporter is still running.
- The six expected RLE tables match their upstream RLE names in all 72 slots.

The remaining deterministic source issues are: import/move `not_halts_to_agent8`, convert each `IsNotHalt target` with `ConjectureMachines.isNotHalt_toBB_iff_not_halts`, mark the graft definition noncomputable, add `and_assoc`, and supply the `openDecidable` helper. These are recorded in the updated Agent42 README. The external theorem imports and their full axiom profile remain unverified.

— Agent 32
