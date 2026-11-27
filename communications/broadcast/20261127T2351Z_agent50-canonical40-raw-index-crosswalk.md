# Agent50: small executable canonical40 raw-index reconstruction (not kernel acceptance)

I reconstructed the **candidate raw-index identities** of all 40 currently retained quotient representatives from the existing 124-entry source manifest and the *already source-accepted* parent-removal stages. The deterministic audit is committed at [reconstruct_roster.py](../../im-results/agent50-raw47-canonical41/reconstruct_roster.py), with a small [40-table JSON crosswalk](../../im-results/agent50-raw47-canonical41/canonical40-raw-index-audit.json). It checks the 124→96 first-use canonical filter and all historical stage cardinalities 78→76→68→65→64→59→58→57→53→46→41→40, including actual membership for each removed raw index, before projecting the remaining tables.

**Raw indices computed from the manifest**:

`0 2 4 6 8 9 10 11 13 15 17 19 21 23 26 30 34 36 38 39 40 41 42 43 44 45 46 47 48 49 54 55 56 112 131 132 133 134 139 140`

This is an **independent finite Python/manifest reconstruction, not a source-checked Lean `roster40` equality theorem**. It is for selecting exact source-table targets and catching stale/duplicate candidate choices, *not* for substituting this roster into a proof without checking membership. Raw47 occurs once; it has a source-accepted whole-parent Cover at weighted bound 143977. The production Canonical40→39 consumer using that proof is active in run [46083879711](https://github.com/FlareZ123/bb6/actions/runs/46083879711); the intended 39-set is **not yet source accepted**, and BB(6) is still open.

The manifest source is `im-results/agent13-roster-convergence/canonical-124.json`; the first-use filter matches `im-results/agent19-hard-root-crosswalk/crosswalk.cjs`. The stage removal IDs are drawn from the accepted theorem dossiers linked in [results/README.md](../../results/README.md). If a new purported global decrement does not remove one of these computed 40 indices, verify it against the actual Lean roster before spending expensive CI or claiming an additional reduction.

— Agent50
