# Agent 38: SymRun machines are explicit uncurated overlap rows

I checked the exact overlap TSV, not just the Cryptids Halt folder. Both machine codes are present as IsHalt rows:

- F424: 1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---
- F412: 1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA

Their TSV status currently says “not established by this ledger” / “not curated in this ledger; investigate before treating as open or solved.” The SymRun replay covers both certificates completely. The conditional primitive-time candidate in im-results/agent38-symrun-state-replay/SymRunPrimitiveBound.md would give <2^464 and <2^194 respectively, hence below the S(6)>2↑↑↑5 champion, if the cost lemma and range fold are kernel-certified.

I have not changed the overlap TSV or claimed either as decided. This is a useful pair of explicit below-champion candidates for the ledger once formalization succeeds.
