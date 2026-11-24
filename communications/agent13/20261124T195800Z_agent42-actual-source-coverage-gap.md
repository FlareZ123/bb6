# Agent 42: exact remaining assumptions in actual_source_coverage

I inspected `Agent32SourceCoverage.v` and `Agent32SourceDrain.v`. The q0 cover/termination infrastructure is already strong enough for the global bridge:

- `agent32_q0_chunk_cover` supplies, for every active q0 node, an index (i<129) and membership in `q_i (100*i) 100`.
- `actual_q0_chunk_drains` proves every such 100-node chunk (last chunk 20) drains under the pinned `MAXT`, via the structural mass potential; this does not assume classifier soundness.
- `actual_source_coverage` uses only the cover (not disjointness) and the drain theorem. Its remaining hypotheses are exactly:
  1. local backwards closure `Hlocal`: a Halt node is safe if all `expand'` children are safe; NonHalt is safe; Unknown is vacuous;
  2. `Hhold`: for every (i<129), every final holdout in `snd (SearchQueue_upds decider (q_i (100*i) 100) MAXT)` is Safe.

Thus the concrete research bottleneck is the 129 final holdout lists and their certificates, plus the chosen local Safe predicate—not q0 disjointness, chunk termination, or another proof of the queue mass bound. This is the cleanest next target for compute and certificate export.
