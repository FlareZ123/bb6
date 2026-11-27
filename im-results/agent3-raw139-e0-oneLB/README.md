# Raw139 E0=1LB: exact C1 subcovers

The normalized depth-two E0=1LB parent is `[7,24,11,24,14,24,24,16,6,11,24,24]` (ordinary transition code (4q+2w+r), 24 unknown). Its first unknown slot is C1 at primitive time 9. **Full weighted Cover accepted** at 187672026. All 18 ordinary child banks, six immediate cycles and the halt branch are composed by `BB6.Agent3OneLBParent.parent_cover` in ParentAssembly.lean. `all_completions_weighted` and `cover_at` are exported. [Run 45969459350](https://github.com/FlareZ123/bb6/actions/runs/45969459350), source 794534babcb9293934d58262bf45bec6dc220f71, [artifact 15184626370](https://github.com/FlareZ123/bb6/actions/runs/45969459350/artifacts/15184626370). No global roster cut claimed.

## Established child covers and open obligations

| C1 code | Exact child table | Bound | Status |
|---|---|---:|---|
| 8 (0LC) | [7,24,11,24,14,8,24,16,6,11,24,24] | 574 | Original-source Lean accepted, [run 45934344615](https://github.com/FlareZ123/bb6/actions/runs/45934344615), [artifact 15169732599](https://github.com/FlareZ123/bb6/actions/runs/45934344615/artifacts/15169732599), pinned source 227a5454ea2bc0c3ce765c0ca7fc6cb1c43e7d98 |
| 10 (1LC) | [7,24,11,24,14,10,24,16,6,11,24,24] | 61185 | Original-source Lean accepted [run 45936450670](https://github.com/FlareZ123/bb6/actions/runs/45936450670), [artifact 15170359046](https://github.com/FlareZ123/bb6/actions/runs/45936450670/artifacts/15170359046), pinned source 735a50566c1b6c61cc35371cc2b55333b17566b7 |

Accepted theorem for code 8: `BB6.Agent3E0OneLBC1ZeroLC.weighted : Cover (WeightedBound 574) parent`. Its checker uses the original FastThreeHoleAudit and BlockFAR2/BlockFAR and the standard-axiom gate. This is an exact child cylinder, not an entire parent. The accepted code-10 theorem is `BB6.Agent3E0OneLBC1OneLC.weighted : Cover (WeightedBound 61185) parent`.

Six other C1 ordinary choices immediately enter a translated cycle; candidate witnesses are (start,period,direction,boundary): 11:(2,8,false,2); 12:(6,4,false,0); 14:(6,4,false,0); 16:(4,6,false,1); 17:(14,3,true,2); 18:(9,2,true,-2).
The remaining long-query certificates are source-kernel checked in [Agent12 A1](../agent12-raw139-oneLB-lateA1/README.md) (Agent3 return map) and [Agent12 repeated replay](../agent12-raw139-oneLB-repeat-replay/README.md). The original exact leaf 286 [nonhalting proof](../agent12-raw139-oneLB-c1-286/README.md) is now integrated into the code-1 child, accepted [run 45945087056](https://github.com/FlareZ123/bb6/actions/runs/45945087056), [artifact 15175093456](https://github.com/FlareZ123/bb6/actions/runs/45945087056/artifacts/15175093456). A conditional 25-way parent consumer has been dispatched (run45947260278) with explicit hypotheses for codes 1,9,21; code1 can now discharge its hypothesis.

The [matrix run 45936586801](https://github.com/FlareZ123/bb6/actions/runs/45936586801) accepted these twelve other code-specific weighted children; overall run failure is confined to code 22. Each artifact is independent and must be checked against its exact parent and bound at composition.

| Code | Certified artifact ID |
|---:|---:|
| 0 | 15170943998 |
| 2 | 15171268674 |
| 3 | 15172491119 |
| 4 | 15171717416 |
| 5 | 15171918583 |
| 6 | 15172092832 |
| 7 | 15173066637 |
| 13 | 15172995676 |
| 15 | 15173005981 |
| 19 | 15172323659 |
| 20 | 15173086029 |
| 23 | 15174465692 |

Code 22 failed `rangeCheck ... cert.fastRowsAt machine` for reflected width-2/3 certificates, not their machine-table equality. The untrusted narrow-width emitter reused radix A=2^w for pair packing of control keys 2q+d, whose range is 0..11. For A=4 or 8 this corrupts the key and its value. The repair uses K=max(A,16) for packed pairs only, leaving symbol/edge/predecessor radices A unchanged; pair bit capacity increases accordingly. The existing width-4+ results are unaffected. The two original recipes are retained; no repeated discovery. The corrected code-22 child passed [run 45945231170](https://github.com/FlareZ123/bb6/actions/runs/45945231170), artifact [15174950775](https://github.com/FlareZ123/bb6/actions/runs/45945231170/artifacts/15174950775).

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

The four long candidates are imported by exact table identity into `WeightedAudit` using Agent12's proved `weighted`/`all_completions_weighted` families. `compressed.py` bypasses only the redundant untrusted primitive candidate replay for those exact tables; the proof still checks full table equality and the weighted bound. The original c9/c21 partitions and narrow/wide witnesses are unchanged. The `ParentCore.lean`, `emit-parent.py`, `merge-bank.py`, and manual `agent3-onelb-compose.yml` target prove the exact 25-way parent from accepted banks, using dependency identities to avoid recompiling shared modules. Codes9/21 accepted in runs45956599760/45956606017 (artifacts15180610248/15181930573). Full parent accepted after selecting top-level producer manifests rather than nested reuse manifests. No global roster change until accepted parent and exact normalized-root consumer. Independent Agent3 RLE/sweep implementations are exploratory alternatives, superseded as the critical path by Agent12's local original-semantics proofs; duplicate checks were cancelled where possible.
