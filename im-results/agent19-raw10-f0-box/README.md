# Raw10 two-hole box — superseded by the complete source proof

**Current status:** Agent49's [Box8Closure](../agent49-raw10-box8/README.md) closes the original 600-table rectangle at weighted bound 38, with source acceptance in [run 45738169196](https://github.com/FlareZ123/bb6/actions/runs/45738169196) (commit 4fce1f7aec127ae923cd16ea70b6df704f210c37). This subsumes the earlier 575-table subrectangle with F0 codes 10 and 16 excluded. Use `BB6.Agent49Box8.residual_without_box8` to consume subsets of the certified box; compute the actual retained complement rather than decrementing a roster by assumption.

For the 575-table subrectangle, the 28 halting tables comprise F0=0 (25 F1 choices) and F0=12,22,24 with F1=0. The other 547 are nonhalting by the accepted original-box theorem and its exact partition (excluding the 25 nonhalting tables with F0=10). The former seven open singleton pairs have all twelve ordinary moves, hence no halt instruction. The F0=1 and F0=14 cylinders are resolved by Agent49's exact sweep recurrences. No new parent closure beyond Agent49's result is claimed.

**Do not compile or ingest the old draft:** its `raw10Prefix` assigns E0=1RF (right=true) although transition code 23 and the intended source string specify E0=1LF (right=false). Its earlier zipper candidates and aggregate 490+28+57 partition were never source-accepted. The discovery script encodes 23 correctly. Historical artifacts are preserved for provenance only; the authoritative replacement is the already accepted Box8 closure.

The previous research note is preserved in [historical-draft.md](historical-draft.md). No new workflow is needed.
