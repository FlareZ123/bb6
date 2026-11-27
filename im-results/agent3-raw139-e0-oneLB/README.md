# Raw139 E0=1LB: exact C1 subcovers

The normalized depth-two E0=1LB parent is `[7,24,11,24,14,24,24,16,6,11,24,24]` (ordinary transition code (4q+2w+r), 24 unknown). Its first unknown slot is C1 at primitive time 9. The full weighted Cover is **not yet proved**. The C1=0LC child is accepted in original-source Lean; C1=1LC is computationally complete; its first source gate was interrupted and the long replay is now chunked. Neither constitutes a global roster cut.

## Established child covers and open obligations

| C1 code | Exact child table | Bound | Status |
|---|---|---:|---|
| 8 (0LC) | [7,24,11,24,14,8,24,16,6,11,24,24] | 574 | Original-source Lean accepted, [run 45934344615](https://github.com/FlareZ123/bb6/actions/runs/45934344615), [artifact 15169732599](https://github.com/FlareZ123/bb6/actions/runs/45934344615/artifacts/15169732599), pinned source 227a5454ea2bc0c3ce765c0ca7fc6cb1c43e7d98 |
| 10 (1LC) | [7,24,11,24,14,10,24,16,6,11,24,24] | 61185 | Computational discovery complete; source [run 45934601426](https://github.com/FlareZ123/bb6/actions/runs/45934601426) interrupted by runner shutdown, no parent theorem, pinned source 7467766e7062b6e44e7de95d20e5fcf10c4f31ff |

Accepted theorem for code 8: `BB6.Agent3E0OneLBC1ZeroLC.weighted : Cover (WeightedBound 574) parent`. Its checker uses the original FastThreeHoleAudit and BlockFAR2/BlockFAR and the standard-axiom gate. This is an exact child cylinder, not an entire parent. The intended code-10 theorem is `BB6.Agent3E0OneLBC1OneLC.weighted : Cover (WeightedBound 61185) parent`.

Six other C1 ordinary choices immediately enter a translated cycle; candidate witnesses are (start,period,direction,boundary): 11:(2,8,false,2); 12:(6,4,false,0); 14:(6,4,false,0); 16:(4,6,false,1); 17:(14,3,true,2); 18:(9,2,true,-2).
The other 16 choices remain to be closed. The original C1 halt alternative must also be covered.

## Exact first-query partitions

| Certificate | C1=0LC | C1=1LC |
|---|---:|---:|
| Ordinary split nodes | 561 | 685 |
| Translated cycles | 10708 | 11340 |
| Initial final-hole leaves | 2110 | 3209 |
| FAR (at most 2 DFA states) | 58 | 969 |
| Additional block invariants | 27 | 233 |
| Extended final-hole executions | 1 | 5 |
| Total ordinary leaves | 12904 | 15756 |

Both children first read D0 at time 12. The 450-step full-history replay checks translated half-tape equality and FAR fixed-point saturation; the leaf count is exactly (1+23s) for (s) ordinary split nodes. Halt alternatives at splits are separately covered by the weighted source checker. A final-hole cylinder is exhausted by possible halt there or a total ordinary-transition table, which cannot halt.

The code-8 late table `[7,24,11,5,14,8,21,16,6,11,1,15]` reaches its final hole A1 at 568. Code-10's hardest late table `[7,3,11,21,14,10,1,16,6,11,24,13]` reaches F0 at 61179, head +27; all other late queries are at most 2727. Adding one halt step and maximum five incoming blank-delay steps gives the stated weighted bounds. The first source run compiled block-FAR modules and many branch modules, but the runner shut down (exit 143) before parent completion. The revised reproduce-oneLC.sh uses the existing emit_late.py (4,000-step checked packed replay chunks) and WeightedAudit/transform-graft.py for the 61,179-step leaf. All generated module names are renamed to prevent collision with the OneLA parent artifacts. No new simulator assumption or repeated discovery campaign.

## Reproduction and parent strategy

`reproduce.sh` for code 8 (recipes.json and discover.py); `reproduce-oneLC.sh` for code 10 (discover-oneLC.py). Both generate Lean source from the shared replay.cpp and package6.py. The recipes were found with an exact JavaScript port of the same untrusted candidate algorithm; the Python generator and original source checker validate them independently. Use existing manual workflow agent48-raw139-f1-siblings.yml, kind e0parent, sibling OneLBC1ZeroLC or OneLBC1OneLC, pinned source revision. Local shell/Python tool calls returned ClientError before execution; the existing focused CI is the source gate. No new trusted checker.

`discover-rest.py` and `search-rest.sh` preserve the exact partitions, deterministic short block recipes, bounded deeper block search, final-hole witnesses and explicit residuals of the other 16 C1 siblings, excluding the two completed discoveries and six immediate cycles. This is untrusted discovery only, with an explicit unresolved list and no Lean/certified claim. Existing manual workflow kind e0search, sibling OneLB. It uses one runner and two worker processes; no repeated scans of the accepted children. A completed child can be fed directly into package6.py from the saved partition and spec. This is a targeted route to a full parent closure, not a new global scan.

Close the residual leaves, then combine all 24 ordinary branches and the halt alternative at the original C1 first query. Ingest accepted child artifacts rather than recompile them. Only a fully compiled parent consumer can support a roster change.
