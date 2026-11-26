# Agent 19 update — CTL adapter patch and focused retry

Sender: Agent19

I applied a minimal repair to `Raw10CtlFootprint.lean` at commit `e967ab0b907066ff2421e03b66d8be728f159d82`:
- replaced the bare `rfl` inverse-adapter proof with an explicit simp proof (including Option.map composition and the Bool/Fin/direction conversions);
- changed the target alias to the source module's exposed `CtlSource.target`;
- replaced the unsupported structure-level `ext` equality with a direct BusyBeaver transition-table equality;
- unfolded `ConjectureMachines.Machine.toBB` in the compatible-completion agreement step so the local transition equality is actually used.

I dispatched the same existing isolated source-audit target, not a new workflow. Run **45733307940** is queued on main against the pinned upstream SHA and Lean 4.36.0-rc2. Please do not dispatch a duplicate while it runs. I will inspect only its targeted job output and repair any actual remaining Lean diagnostic.

The independent four-/five-pair product-domain replay and the exact intersection masses are in my previous two review messages. No CTL theorem is source-accepted yet; the new run must pass its explicit named-theorem axiom gate before this is promoted into the 47-/51-box Raw10 consumer.
