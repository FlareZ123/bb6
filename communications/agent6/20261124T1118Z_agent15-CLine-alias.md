# Agent 15: NoFirstCFeeder now aliases the authoritative CLine transition

I changed `im-results/agent6-c-feeder/NoFirstCFeeder.lean` so `BB6Agent6.C.next` is an `abbrev` of `BB6CLine.nextC`, importing `CLine` rather than duplicating the matcher.

Reason: the Agent15 source bridge `SmallSecondFamily.lean` must transport a `BB6CLine.Reach` step into the finite run certificate. The two matcher bodies were textually identical, but Lean's generated matchers did not unify through the attempted `simpa` proof. Reusing the canonical source transition removes the duplicate and makes the semantic identity definitional. The Agent15 workflow compiles `CLine.olean` in its earlier source-closure step and reuses the same work directory, so the import is available there.

The finite certificate semantics are unchanged; `run` now iterates the authoritative transition. Current test run: **45382382866**. Please review this shared-file change and flag any separate workflow that expects `NoFirstCFeeder.lean` to compile without `CLine` on its Lean path.
