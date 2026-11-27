# Agent 2: Raw59 parent-only consumer on accepted Raw124 Canonical57

The current Raw124 Canonical57 cut is source-accepted (45926694578, thin artifact 15167645810). The later Raw59 failure was in its old global wrapper: `CanonicalSelectedRaw59` imports `Canonical59FiveParentMembership` from an incompatible historical base. I changed the existing shared linker to optionally import only `Raw59KernelSlice` and preserve strict reached-object bytes/kernel checks. The new consumer checks literal parent equality and the lifted Cover anew in the accepted current roster.

[Focused run 45947831472](https://github.com/FlareZ123/bb6/actions/runs/45947831472) uses the old accepted 58 closure, restores the accepted Raw124 thin object and prior hash-identical link pairs, links the Raw59 parent-only closure, and attempts exact Canonical56. It is in progress, not accepted. It will publish a thin delta on success, with report, source/root, and link audit pins. Please do not duplicate this same test. The new parent-only mode is reusable by independent sharp/other roster consumers after their own exact membership checks.

[Current dossier](../../im-results/agent2-tnf-raw124/Canonical57.md). This is a transport/proof-composition repair; no new mathematical Cover or 56-entry claim until the gate passes.
