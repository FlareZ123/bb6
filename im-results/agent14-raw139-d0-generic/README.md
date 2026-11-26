# Raw139 normalized p0 decomposition and accepted E0 parents

This dossier concerns the exact local Raw139 parent `p0` in [Raw139Normalized.lean](../agent6-raw139-normalized/Raw139Normalized.lean), a single Canonical64 parent cylinder. It is not the global six-state upper bound.

## Current accepted facts and missing proof edge

The normalized p0 theorem gives 67 remaining table hypotheses (depth counts [19,22,18,0,4,2,2]) conditional on 43 source sibling Covers, the two exceptional continuation implications and the terminal champion p7 Cover. Four E0 parent Covers are now source-accepted:

| Parent | Exact table | Bound | Accepted run / artifact |
|---|---|---:|---|
| E0=0RA | [7,24,11,24,14,24,24,16,1,11,24,24] | 321796 | [45778885358](https://github.com/FlareZ123/bb6/actions/runs/45778885358) / 15100202529 |
| E0=0RE | [7,24,11,24,14,24,24,16,17,11,24,24] | 852 | [45799738861](https://github.com/FlareZ123/bb6/actions/runs/45799738861) / 15110025526 |
| E0=0RB | [7,24,11,24,14,24,24,16,5,11,24,24] | 1217 | [45824379594](https://github.com/FlareZ123/bb6/actions/runs/45824379594) / 15123260113 |
| E0=0RD | [7,24,11,24,14,24,24,16,13,11,24,24] | 806 | [45824386626](https://github.com/FlareZ123/bb6/actions/runs/45824386626) / 15127060543 |

The 0RB/0RD audits were pinned at source `3a02d387bbd5850260b8f4634aba48053c34001d`; artifact digests are respectively `f5c010855d63bc736f11dff35e76a2d66a08be02019a642444b6a0293cdb1bda` and `1ad8c50ebaec5ec139971e0d46b13c3319f4b1dc3a513b4b5a21599abda10150`. The accepted E0=0RA match and 67→66 integration are in [run 45797137615](https://github.com/FlareZ123/bb6/actions/runs/45797137615). The independent finite module [Raw139NormalizedE0ParentRows.lean](Raw139NormalizedE0ParentRows.lean) proves exact unique normalized membership of the other three rows and count 63 after removal. It passed [run 45828809314](https://github.com/FlareZ123/bb6/actions/runs/45828809314), artifact 15122426249, digest `0c3b38cd9979392dea561775cd0d70df48e25c63239e3563b4fb7841e8a1266b`.

The preferred direct consumer [Canonical64Raw139NormalizedDirect.lean](Canonical64Raw139NormalizedDirect.lean) reuses [Raw139NormalizedAcceptedCovers.lean](Raw139NormalizedAcceptedCovers.lean), which transports all 43 sibling Covers, the two continuation lifts and p7 into the normalized theorem. It then supplies the four E0 Covers and the exact p0/championResidual identity. Its intended conditional exactness interface has 63 other Canonical64 Covers and 63 normalized Raw139 Covers; **it is not yet compiled**, because the 43-sibling shared-core/consumer artifact is missing. The separate active-80→79 crosswalk and [E0-parent crosswalk](Canonical64Raw139NormalizedE0ParentCrosswalk.lean) remain diagnostics; the direct route avoids their additional active complement.

## Reproduction and next missing edge

The existing manual `.github/workflows/agent3-raw120-complete.yml` mode `integrate-65` has inputs for the accepted 63-row artifact and both newly accepted parent artifacts. It verifies overlapping object identities. Once a successful Agent6 core/43-sibling run provides `Raw139NormalizedAcceptedCovers.olean`, dispatch with `raw139_subcover_run_id=<that run>`, `raw139_e0_integrated_run_id=45828809314`, `raw139_e0_rb_run_id=45824379594`, and `raw139_e0_rd_run_id=45824386626`. Inspect the direct module's exact source compile and transitive axiom audit before any global claim.

Agent6 core predecessor 45793950237 failed on missing CostRecurrence namespace and unavailable le_rfl; complete repair commit 106c489391efc8bbef8fbe1d3d56f46e9df945b1. Run 45805343184 was cancelled; run 45806157593 ended in runner shutdown / exit 143 without artifacts. No successful replacement core is known here. Avoid a full duplicate rebuild if the Canonical73 shared-core artifact 45647053824 can be reused with strict source/object/import identity verification; compatibility is not established. Agent6 owns the E0=0LC/0RC research.

The older 80/79-count route, failed attempts, and conditional interface history are preserved in the previous README Git blob `862063a52776fb434d16916a9744343e3d99524c`. The active crosswalk modules remain in this directory. The E0=0LF investigation is separate: [new candidate partition and mathematical holdout decision](../agent14-raw139-e0-zeroLF/README.md). The source-accepted F1=0LD bound 124 and its existing [normalized row adapter](../agent6-raw139-normalized/Raw139NormalizedZeroLD.lean) are another useful graft, subject to a coherent consuming compile. None of these local row reductions alone determines BB(6).
