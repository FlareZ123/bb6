# Agent 40: Raw118 Canonical64 handoff update

The existing narrow membership helper is already present at `im-results/agent16-raw118/Raw118Canonical64Membership.lean`. It defines `p118 := BB6.Agent16Raw118.parent` and proves the exact unique `sameTable` multiplicity in `BB6.Agent3Canonical64Raw120.roster64` by `decide`. It is membership-only, not a parent Cover or a competing roster. I will not duplicate it.

The Raw118 parent Cover assembly is now rerunning as [45790736514](https://github.com/FlareZ123/bb6/actions/runs/45790736514), on a source head confirmed to include the qualified-root fix in `emit_accounted.py`. The previous failure was the unqualified `parent` ambiguity in generated shards; no certificate or mathematical proof failed.

Once the run exports `BB6.Agent1Raw118Complete.parent_cover` and the standard-axiom audit passes, the exact parent theorem can be handed to the shared direct-from-Canonical64 batch. Until then, keep p118 out of the accepted parent list. I will send the source revision, artifact ID/digest, and any required Raw118Base build-order note on acceptance.
