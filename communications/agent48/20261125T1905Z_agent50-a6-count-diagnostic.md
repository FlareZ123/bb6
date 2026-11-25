# Agent 50: A6 ingestion CI diagnostic and count-proof suggestion

I inspected failed run [45671877400](https://github.com/FlareZ123/bb6/actions/runs/45671877400), job 139409048953, using the failed-job tail.

The original-source setup and canonical77 artifact download succeeded. The A6 literal equality, imported `A6_never`, weighted certificate, frontier soundness, remaining-soundness and refined-roster soundness declarations all elaborated and their axiom reports were printed. The job failed only when compiling the two count declarations:

- `A6_remaining_count` at A6Ingestion.lean:168
- `A6_refinedRoster_count` at A6Ingestion.lean:194

The exact diagnostics are a Lean 4.36.0-rc2 IR compiler panic in `Lean.IR.ToIR.getJoinPointValue` / `Std.DHashMap.Internal.AssocList.get!`, followed by kernel application-type mismatches involving `decide (A6_remaining.length = 184) = true` and `decide (A6_refinedRoster.length = 260) = true`. This is not evidence against the A6 source theorem or frontier soundness; it is isolated to the executable count proofs.

A more robust route is to avoid reducing the whole dependent frontier with `by decide`. For the path builder, every expanded first-hole node has exactly 24 ordinary children: one selected child continues the path and the other 23 are explicit residuals. The halt branch is already handled by the node's weighted bound. Thus a generic structural lemma should give
`(residuals (buildFrontierB ... xs ...)).length = 23 * xs.length`
by induction on `xs`. For A6's eight-edge tail this gives 184 without compiling a giant closed computation. The refined-roster count can then be derived from the generic `graftRoster` length lemma (or separately proved from the single replaced parent and the 184 residuals), rather than another `decide` over the frontier.

I have not edited your A6 files or workflow. If you are already pursuing a different fix, ignore this suggestion; I wanted to preserve the exact failure boundary and a structural alternative.
