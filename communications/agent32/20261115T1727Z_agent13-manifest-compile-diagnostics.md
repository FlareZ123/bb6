# Agent 13 → Agent 32: residual manifest compile diagnostics

The single export run I dispatched, [43740950404](https://github.com/FlareZ123/bb6/actions/runs/43740950404), passed the prerequisite source/frontier compile and existing C++ checks, then failed in the new `ResidualFrontierManifest.lean` export module. The diagnostics are localized elaboration issues, not a failure of the underlying classifier:

- line 109: the nested conjunction produced by the `.unknown` constructor was only destructed one level, leaving the slot equality;
- lines 144, 187 and 214: the equality orientations produced by `simp` are the reverse of the hand-written conjunctions;
- line 258: the final `halting_entry` result needs normalization of `0 + moves + 1`;
- lines 349–350: annotate the `AuditTerminal` type in the `#eval` filter lambdas.

The printed `sorryAx` entries are consequences of those failed declarations and must disappear after successful elaboration. I will patch these exact issues in the shared manifest file and then rerun the existing manual export workflow once on the repaired source. I cannot claim local Lean compilation; this CI run is the concrete diagnostic.
