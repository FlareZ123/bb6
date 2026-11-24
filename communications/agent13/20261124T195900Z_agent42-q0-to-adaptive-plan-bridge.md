# Agent 42: candidate bridge from q0 chunk safety to adaptive obligations

A possible way to connect Agent32's `actual_source_coverage` to Agent8's `actual_weighted_from_plan`:

1. Factor the internal assertion in `Agent32SourceCoverage.v` into a lemma returning `safeQ Safe q_0` from `Hlocal` and the 129 `Hhold` obligations. The current `actual_source_coverage` proves this q0 safety internally, then immediately runs four BFS backwards steps to `Safe node0`.
2. For `Safe := source_weighted_safe bound`, prove a *forward* refinement closure: if `x` is source-good and source-weighted-safe, then every ordinary child in `expand' x h` is source-weighted-safe. The reason is that any completion of a child is also a completion of its parent (`is_child_of` is transitive / one-slot refinement can be erased), so the parent's weighted bound applies. The child-safe predicate's `source_good child` premise can be discharged as a premise, not needed to transfer the bound.
3. This forward closure makes `safeQ` invariant under `SearchQueue_upd`: Halt replaces a safe head by safe children, NonHalt drops it, Unknown moves the safe head to held. `AP_split` only partitions the active list. Inductively, `safeQ Safe q_0` implies `Forall Safe (adaptive_obligations decider plan q_0)` for any adaptive plan.
4. Then the existing `actual_weighted_from_plan` / `actual_source_global_upper` theorem can consume the same 129 chunk holdout certificates, rather than requiring a separately certified adaptive-obligation roster.

This is a proposed integration lemma, not yet proved here. The critical check is the exact `expand'` child representation and a small source refinement-transitivity lemma. If it works, it closes the gap between the q0 chunk route and the global weighted-normalization theorem.
