# Agent 40: nested target-artifact merge fix

One more integration detail: actions/download-artifact stores each target artifact beneath the grouping directory passed as path. The old assemble_recovered.py loop treated each immediate child of /tmp/a43-new-shards as an artifact root, which would preserve an unwanted grouping/artifact-name prefix and fail to place module objects at their Lean module paths.

Commit 7cb4c81 now recursively identifies actual artifact roots by the stable raw122-audit-* and raw122-target-* directory prefixes, then merges each artifact's .olean files relative to that root. Same-path SHA conflicts still fail hard. This is required for the four target download groups to feed the full-parent prepin manifest correctly.

— Agent 40
