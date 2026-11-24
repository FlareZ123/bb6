# Adaptive source queue coverage with explicit partial-run obligations

The fixed 100-node/MAXT chunk schedule is not mathematically necessary for exhaustive weighted TNF coverage. An arbitrary finite tree of source queue advances and active-list splits suffices: prove every residual node of the resulting tree safe and the original four-pass root is safe. In particular, a chunk may be stopped after a finite fuel limit and resumed or subdivided, without discarding the unprocessed active nodes or claiming that it drained.

## Exact scheduling contract

A plan has three constructors:

- Stop: output the concatenation of the remaining active and held nodes.
- Advance(fuel, next): execute the actual queue update function for that finite fuel, then execute the continuation plan on the returned queue.
- Split(n, left, right): preserve the existing held list once; run the left plan on the first n active entries and the right plan on the remaining active entries. Both child held lists initially are empty.

The split is an exact list partition for every n, even if a queue is empty or n exceeds its length. Fuel and split size can differ at each node. This avoids assuming equality of output order between one large and many small source jobs; no fixed global fuel, disjoint-range arithmetic, or completed-drain premise is needed. A stopped node remains a proof obligation, including if it is still active.

[AdaptiveQueuePlan.lean](AdaptiveQueuePlan.lean) extends the existing Agent13 queue and Agent32 local closure, rather than introducing a second queue evaluator. `plan_preserves_instance` proves that a completion represented by the input queue is either good or represented by an output obligation. `q0_safe_of_plan` instantiates the implication-based closure so that fresh-label renaming remains inside the existing LocalClosure proof. `split_obligations_safe` allows independently checked branch results to be assembled.

**Exact Lean source verification:** the complete local dependency closure compiled with Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a). The two imported files were byte-for-byte reconstructed from current repository blobs `16b14bcf66193ff9414dbf70dee840fae6868c70` (QueueCoverageContract.lean) and `776678cec157868c5bff2ec88400d41ca5435427` (QueueImplication.lean), checked by git hash-object before compiling. The exported axioms are [propext, Quot.sound] for plan_preserves_instance, [propext, Classical.choice, Quot.sound] for plan_safe and q0_safe_of_plan, and [propext] for split_obligations_safe. No sorryAx or native_decide.

## Direct pinned Coq source integration

[Agent8AdaptiveSource.v](Agent8AdaptiveSource.v) is a candidate importing Agent32SourceCoverage, not a replacement for the source decider. Its adaptive_obligations invokes actual SearchQueue_upds and firstn/skipn on the source SearchQueue. The intended theorem actual_source_adaptive_coverage closes actual q_0 back to node0 through all four BFS passes. The checkpoint lemma permits exact queue-result equations to be verified and reused separately. **This Coq file has not compiled yet**: no Coq/Rocq executable is available locally, and the imported direct source-coverage chain has an existing compiler blocker. Use the maintained shared Rocq workflow after the owning agent resolves the first compiler diagnostic; no new workflow is warranted. The Lean theorem is independently accepted against its exact existing Lean imports.

## Practical use and remaining obligations

Split the 12,820 actual q0 entries at any desired indices, then run limited-fuel source jobs on both inexpensive and expensive ranges. Preserve the full returned active and held lists, the exact range or parent checkpoint, source revision and fuel. A completed job can use Stop; a partial job can use Advance or Split on its actual returned active list. A timeout with no captured exact checkpoint contributes no processed evidence. A hash or a count alone does not certify a queue-result equality. To resume modularly, prove exact output equality for each advance and assemble via the checkpoint and split rules; independent runs need not have the same ordering as the old 100-node schedule.

This removes a fixed-schedule proof restriction. It does not establish any additional machine decision, produce the full residual roster, evaluate a new source chunk, prove the cross-language classifier transfer, or establish a BB(6) upper bound. All actual output nodes still require source-connected certificates. The source acceptance and measured throughput of the adaptive runs remain the next concrete tests. The other queue agents are already pursuing export and source closure; coordinate rather than duplicate those jobs.
