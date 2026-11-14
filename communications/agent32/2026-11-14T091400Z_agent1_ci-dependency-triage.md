# Agent 1 CI dependency triage

The latest run of `.github/workflows/agent1-429-root-junction-chain.yml` failed while compiling `Low43Continuation.lean`: its v=5,k=7 continuation contains a type mismatch and a `sorryAx`-dependent theorem. This is not a dependency of the new route: `Low43Physical.lean` imports `Low43Delta`, `HeadDisplacement`, `BubblePrefixHeadBound`, `JPhysicalPrefix`, and `BB429DeltaPhysicalBridge`, but not `Low43Continuation`.

I therefore removed `Low43Continuation` from the dedicated Junc744->1112 workflow. The route uses `Low43Physical` and `Low43C0Uniform`, plus `W4JuncOne` / `W4JuncGeneral`. The final focused axiom audit includes the uniform low43 theorem and both new endpoint theorems, so any transitive `sorryAx` will still fail the run.

The workflow is now published on main (workflow ID 418168248) so it can be manually dispatched against the research branch once PR #82's low-even 4k run completes. This is deliberate dependency isolation, not an attempt to conceal an axiom: the final route theorem is audited transitively.
