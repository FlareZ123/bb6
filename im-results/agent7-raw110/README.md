# Raw110: two late-halting leaves and complete-parent proof

**Status (2026-11-25 10:35 UTC): exact parent partition source-accepted; final late-trace composition pending.** The six-hole canonical raw110 table is `1RB---_1RC---_0RD---_1LD1RE_---0LC_------`. Its authentic blank run first queries C1 after seven defined moves. All 24 ordinary C1 children are represented; the early halt child is included in the weighted cutoff 7014. The source-checked partition has exactly two retained one-hole leaves.

## Final two leaves: computational resolution

| Child/open index | Exact partial table | Defined moves before A1 | Halt score |
|---|---|---:|---:|
| 5/161 | `1RB---_1RC0RA_0RD0LF_1LD1RE_0RB0LC_1LC0LF` | 6659486 | 6659487 |
| 5/790 | `1RB---_1RC0RA_0RD0LF_1LD1RE_0RB0LC_1LC1RD` | 6766858 | 6766859 |

Each has only A1 unassigned. Its 24 ordinary completions are total and never halt. The halting completion has the displayed score; there is no incoming zero delay because A0=1RB. The primitive simulator and independently derived exact paired sweep recurrence agree on 19203 sweeps and the two step counts. These concrete counts remain computational pending final source replay acceptance.

## Proof architecture and current evidence

- The seven accepted partition artifacts from [45557356900](https://github.com/FlareZ123/bb6/actions/runs/45557356900) contain all sixteen nontrivial ordinary children. The eight remaining children have immediate translated-cycle certificates. The global consumer in that run failed due to runner shutdown while compiling unrelated dependencies; it is not acceptance of the complete parent.
- [45593652030](https://github.com/FlareZ123/bb6/actions/runs/45593652030) **passed** the exact parent cut, including `Raw110ParentResidualMatch` matching the two leaves to the exact partial tables. Artifact `raw110-parent-cut`.
- `Raw110WordSweep.lean` derives the exact B-return evaluator from Agent13's block/carry macros. `Raw110WordSource.lean` transfers these finite runs to original `BB6Coverage` semantics and supplies weighted coverage of all compatible completions. The original-source bridge job passed in [45592977146](https://github.com/FlareZ123/bb6/actions/runs/45592977146); several uncompressed trace jobs were terminated by runner shutdown, and that workflow was superseded.
- `Raw110RunSweep.lean` compresses the right word's repeated A-pair and the left word's bit runs. Its exact cost-preserving replay equivalence was kernel-checked locally using Lean 4.36.0-rc2 and the actual relevant macro definitions. `gen_late_trace.py --compressed` generates compact trace shards. [45595393696](https://github.com/FlareZ123/bb6/actions/runs/45595393696) checks their concrete claims and source bridge.
- `Raw110ParentLateCover.lean` composes the accepted partition and late covers into `raw110_cover B` for B≥6766859. The end-to-end theorem is **not yet source-accepted**. After the compressed late workflow succeeds, dispatch `agent7-raw110-parent.yml` with parent_run=45593652030, late_run=45595393696. The final artifact is `raw110-complete-parent`.

This bound is far below the established champion. Once the final source proof is accepted, graft the full parent Cover into the actual canonical quotient roster using a mixed-bound consumer. No unconditional BB(6) maximality claim follows.

## Reproduction

`generate_partial.py --block-far` generates each nontrivial ordinary child from the shared raw99 classifier and deterministic SHA-pinned candidate bank. Every candidate is checked by the established Lean audit; no search verdict is trusted. `assemble_partial.py --block-far --parent-only` composes the 24 children. The 16 previously remaining nonhalters use Agent13's exact table-matched block-FAR wrappers; their inclusion is covered by the accepted partition. The two remaining leaves cannot be proved nonhalting and must not be passed to FAR search again.
