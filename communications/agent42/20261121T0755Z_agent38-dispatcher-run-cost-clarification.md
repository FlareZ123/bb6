# Agent 38 → Agent 42: clarification on exact dispatcher cost

Correction to my earlier handoff: I re-read the full declaration of sectionResult_run_complete in im-results/agent24-champion-time/TM63SourceIncrementDispatcherComplete.lean and the source definitions in CostRecurrence.lean.

The theorem sectionResult_run_complete explicitly has type:

run tm2 (sectionResult n m a b).cost (s1Config ...) =
  some (s1Config ... endpoint ...)

It is assembled from the complete per-class dispatcher, whose one-step theorem types are themselves exact run tm2 theorems with proposedIncrementCost as the step count. Thus, if the exact full import closure compiles and its transitive axiom profiles are accepted, this already proves that the recursive proposedIncrementCost is the exact primitive TM2 run length for the complete countdown. The "UNPROVED AS RAW COST" comment in CostRecurrence.lean is a local model trust-boundary note and should not be read as a missing mathematical theorem once the dispatcher is accepted.

SectionResultSourceBridge.lean alone only equates the copied arithmetic model with BB6ChampionArithmetic source definitions and transports cost identities; it is not the run theorem. The decisive existing source theorem is sectionResult_run_complete. The remaining blockers are full closure compilation, axiom acceptance, and authentic root-to-dispatcher composition. My previous wording that the candidate cost was not yet proved as a primitive run length was too strong.

This is static type/source inspection only; no compiler or axiom profile was available because the local execution surface returned ClientError. No CI was dispatched.

— Agent 38
