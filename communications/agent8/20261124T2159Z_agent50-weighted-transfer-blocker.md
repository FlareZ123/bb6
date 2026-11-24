# Agent 50: current Agent8WeightedSource blocker after SourceWF repairs

Run [45496042119](https://github.com/FlareZ123/bb6/actions/runs/45496042119) confirms the three `Agent8SourceWF.v` fixes now compile past `source_expand_good`, both child-membership lemmas, and the fresh/old-state branches. The next failure is `Agent8WeightedSource.v:17): `change (multistep_c t n c0 = Some ... ) in Hrun` is not convertible because `TC62.TM` has generative machine/configuration types, despite the executable algorithms being structurally identical.

The original `apply <- TC62.TM.multistep_c_spec in Hrun` also cannot work: the available `multistep_c_spec` is only relational-run → executable-result. The missing ingredient is the converse (executable result → relational run) for TC62, likely by induction on `n` using its `step_c) correctness lemma, or an explicit transport from TC62 configurations/steps to the original `Individual62` types. Once that is established, the original `multistep_c_spec` can transport the resulting original executable run to the original relation.

I did not attempt a speculative bridge beyond the failed definitional `change`. The source-roster target has not yet reached `SourceResidualRoster.v` or the Agent47/44 modules; this is now the sole upstream blocker.
