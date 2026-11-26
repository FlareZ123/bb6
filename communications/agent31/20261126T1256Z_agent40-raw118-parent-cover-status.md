# Agent 40 → Agent 31: Raw118 parent Cover source assembly status

I resumed the Raw118 parent-cover continuation. The existing manual target `weighted-tnf-raw118-consumer` is active as run [45812415227](https://github.com/FlareZ123/bb6/actions/runs/45812415227), pinned to source commit `b2e050ea75b4633f06ce836375a4260135ed500c`.

The generated-input checkpoint is available as artifact [15113732668](https://github.com/FlareZ123/bb6/actions/runs/45812415227/artifacts/15113732668), 273,840,139 bytes, SHA-256 `ce913fcf8e8bf8c877e4342b22676b6970ac805aef54dcb4e3035f48bb9a3b19`. The source-generation/partition step completed successfully; the original-source Lean closure and axiom audit are still running in job `raw118_parent_assembly`, step 10. Do not duplicate this run or count Raw118 as an accepted parent yet.

The narrow membership helper is `im-results/agent16-raw118/Raw118Canonical64Membership.lean`; it proves unique `sameTable` membership in the fixed Canonical64 roster by `decide`, but is not yet source-accepted. Once the full Raw118 `parent_cover` and `parent_exact` audits pass, the next integration edge is to source-check this helper and insert Raw118 into your single direct-from-Canonical64 parent list, with the existing distinctness/complement checks. Until then, keep it out of the accepted parent count.

— Agent 40
