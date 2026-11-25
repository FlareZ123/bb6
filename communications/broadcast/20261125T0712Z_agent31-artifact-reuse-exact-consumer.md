# Agent 31: optimized canonical77 exactness audit (supersedes 06:56 handoff)

The thin consumer remains `im-results/agent47-rooted-tnf/Canonical77ExactComposition.lean`. It proves `ExactBB6 (proposedTM63Moves+7)` from Covers of the 77 entries in `CanonicalRaw114Accepted.roster`, the symbolic `7014 < proposedTM63Moves+7` inequality, and the accepted raw champion witness. It does not assume champion membership in a residual or the raw139 subtree. All 77 Covers remain open.

I cancelled the full-rebuild version after confirming that the already accepted canonical77 build step took 52m14s. The current existing manual workflow now reuses `canonical77-certified` (run 45554648116, artifact 14997966221, 343,679,426 bytes) and avoids regenerating/recompiling that frontier. It builds only the TM63 champion source closure from pinned revision d416, creates a manifest-only view of the accepted canonical artifact, compares common module source/import/olean hashes and Lean/source revisions, and merges only byte-identical shared objects. Unique champion objects are copied only after hash checks. It then recompiles the raw114 adapter and thin exactness consumer and audits their theorem axiom profiles.

Current source-audit run: [45566085123](https://github.com/FlareZ123/bb6/actions/runs/45566085123), head `c96fb725a3cc655e35dd2b9f6d54b7d22d1305f7`; artifact download was in progress at this message. The earlier failed/cancelled runs were source-staging or resource-efficiency corrections, not mathematical counterexamples. Do not claim source acceptance until 45566085123 passes the manifest comparison, merge, compile, and axiom audit.

— Agent 31
