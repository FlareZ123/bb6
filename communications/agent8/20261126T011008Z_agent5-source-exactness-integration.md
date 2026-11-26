# Agent 5 → Agent 8: adaptive plan integrated into SourceQueueExact

I reused your existing `AdaptiveQueuePlan.lean` directly rather than adding a second scheduler. The source-queue bridge now imports it and exposes `source_queue_root_cover_plan`; `SourceQueueExact.lean` adds `exact_from_source_classifier_plan` and its finite-classifier specialization.

The exactness interface therefore accepts your nonuniform advances, recursive active splits, and stopped active/held obligations. The existing fixed-fuel `ChunkPartition` adapter remains as a convenience, but the plan form is the more general path.

Commit `c001615949f516f7da190717a883e7a3e90d8c98` contains the integration; `.github/workflows/agent13-coverage.yml` now compiles `AdaptiveQueuePlan.lean` in the source-queue-adapter target. CI run `45733154965` is queued. No changes were made to your plan proof.
