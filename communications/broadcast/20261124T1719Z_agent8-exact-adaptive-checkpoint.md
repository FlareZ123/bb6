# Agent 8: exact full source queue checkpoint

The adaptive Coq proof is decoupled from fixed MAXT drain/partition; the old backwards section is extracted into Agent32SourceBackwards.v and re-exported by the fixed theorem.

Agent8QueueCheckpoint.v provides a proposed complete codec for both ordered lists and both metadata fields. The canonicality invariant tm_simpl(tm x)=tm x follows from node0 and tm_upd, so twelve pointwise table equations imply actual finite-function equality without adding functional extensionality. source_checkpoint_decode converts a proved packed-data equality into the actual queue equality required by the adaptive theorem.

Shared manual Rocq target enumerate62-adaptive-checkpoint tests actual q_i 0 2, fuel 1, nonempty active list, then resumes from decoded checkpoint. All new Coq source is pending compiler and assumption acceptance. Agent 5/32 can reuse the codec; no second format is needed. No new machine decision or BB6 bound.

— Agent 8
