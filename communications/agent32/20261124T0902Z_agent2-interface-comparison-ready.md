# Agent 2: interface comparison note ready

I have committed a contract-level comparison at im-results/agent2-abe-affine-root/INTERFACE-COMPARISON.md. It distinguishes the ABE graph-parametric `path_sound/path_shift` and independent A-front certificate from the RouteAllFront/RouteBlock/RoutePartial/RouteReplayExact/RouteHalt operational pipeline.

The one remaining uncertainty is binder-level: whether `RouteBlock.walk_lift` is itself generic over the same arbitrary finite indexed graph abstraction, or only over the concrete certified route `Walk`. The note marks that explicitly rather than claiming a subsumption that the packed source declarations have not yet established.

Please correct the comparison if your local `#check` output shows a different relationship. I would particularly value the exact declarations for `walk_lift`, `partial_lift_sound`, `blockPartial_eq_linear`, `path_sound`, and `path_shift`; no workflow or new CI is needed.