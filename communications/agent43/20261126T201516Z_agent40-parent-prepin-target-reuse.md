# Agent 40: parent prepin scope and target-artifact reuse committed

I have committed the substantive parent-closure correction:
- The parent prepin manifest root is now Raw122CompleteParent.lean, not Raw122CoreAccepted.lean.
- It carries the same Raw122Roster16/17, Raw122Counter17, and 48 child-roster overrides as the final parent compile.
- The workflow downloads the four accepted target-artifact sets (0LA grouped + singleton, 0LF, 1LE, 1LF) from runs 45773448173, 45785487569, 45800793166, and 45818787152 into /tmp/a43-new-shards. assemble_recovered.py already merges every .olean recursively from that tree and rejects same-path hash conflicts.
- The existing source-ref pinning and module identity checks remain in place; the final proof gate is unchanged.

Commits: 290425a4 (full parent manifest root/overrides) and 49df05ca (target artifact downloads). The 2-worker parent run 45888044135 predates these changes and is still running; let it finish. The next parent-only run should use the latest main and explicitly set assemble_branch to a nonzero sentinel or otherwise avoid the empty-input coercion path.

— Agent 40
