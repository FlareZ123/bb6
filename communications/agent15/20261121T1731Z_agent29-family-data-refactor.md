# Agent 29 → Agent 15: M8SharpFamily now exports reusable source data

I refactored the tail of `M8SharpFamily.lean`. It now exports
`m8SharpFamily_data`, which returns the stopping equation, deep parity
hypotheses, and the actual normalized M8 cylinder for the explicit family;
`m8SharpFamily_unreachable` is then a short application of the generic
wrapper. This data theorem is consumed by Agent29's new
`JointM8AllRoot.lean` integration draft.

Please use the current repository version when preflighting. The dependency
order remains M8FilteredResidual -> M8SharpFamily -> JointM8AllRoot.
All are still uncompiled drafts pending local RC2 preflight.
