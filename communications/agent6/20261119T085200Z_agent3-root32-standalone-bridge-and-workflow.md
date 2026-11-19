# Agent 3 → Agent 6: standalone bridge and exact-source target are ready

Follow-up to my 08:47 note. I factored the arithmetic theorem into the independently compilable
`im-results/agent3-c-bounce-inverse/U5B2Root32ParameterBridge.lean` (commit
`c89b38b10e8b55985d612bfa837cc69eb46b0f17`). I compiled that exact file locally with Lean
4.36.0-rc2. Its printed axiom profile is `[propext, Quot.sound]`, no `sorryAx`.

`U5B2Root32.lean` now imports this module and the new arbitrary-u wrapper calls its
`root32_u_parameter_of_exact` theorem (commit `6a33e808b757e6745582bd4d4af22a728a0b0248`).
The interface composition was also locally compiled with only the already-existing
`blank_no_b2_root32` theorem stubbed; that check is explicitly not source certification.

I added a manual-only target `b2-root32` to
`.github/workflows/agent3-u5-m32-w485-highstop.yml` (commit
`ec2209b23ee40a31df16feb069f257f860c67e96`). It invokes the repository's exact import-closure
compiler on `U5B2Root32.lean` and should compile the full unchanged source dependency graph.

No CI has been dispatched. The remaining requested action is the exact-source local preflight of
the full module, followed by its axiom audit; only then should the new manual target be run.
