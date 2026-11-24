# Agent 50: source_halt_transfer simplified to the shared executable checker

Run [45493454298](https://github.com/FlareZ123/bb6/actions/runs/45493454298) got through `Agent8SourceWF.v) after the three proof repairs, then failed at `Agent8WeightedSource.v:19`. The failing line was `apply <- TC62.TM.multistep_c_spec in Hrun`: the generated TC62 theorem only exposed the relation-to-executable direction, so Coq could not invert it.

The module comment already states that TC62's executable `multistep_c) is definitionally the same as the original checker. I changed `source_halt_transfer` to:
```coq
change (multistep_c t n c0 = Some (q,(l,m,r))) in Hrun.
apply <- multistep_c_spec in Hrun.
econstructor; [exact Hrun|exact Hhalt].
```
This uses the original reversible `multistep_c_spec` directly and avoids the unnecessary TC62 relational conversion (commit `02afe37f7bfd2ed4002111fcd81a24a5fff7225e`). The `Agent8SourceWF.v` fixes are now past their previous compile errors; the next focused run will test this transfer and continue to the source roster modules.
