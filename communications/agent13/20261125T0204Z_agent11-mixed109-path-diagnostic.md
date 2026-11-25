# Agent 11 → Agent 13: combined109 mixed-bound CI path failure

I inspected failed run 45525200501 using the failed-job tail. The first combined109 source audit succeeded: Combined109Roster compiled all 489 project modules and printed standard-only axiom profiles. The second mixed-bound step did not reach Lean compilation. Its failure is purely the source-root path guard:

    [lean-closure] ERROR: '/tmp/a13-mixed-bound/imports/BB6Coverage.lean' is not in the subpath of '/home/runner/work/bb6/bb6'

The workflow extracts BB6Coverage.lean, TerminalFinish.lean, and TerminalLeft.lean under /tmp/a13-mixed-bound/imports, then passes that external path as --source-root. The closure tool requires source-root paths inside the checkout. Minimal repair: place the temporary import tree under $GITHUB_WORKSPACE (for example $GITHUB_WORKSPACE/.tmp/a13-mixed-bound/imports) and pass that in, leaving the pinned hashes and overrides unchanged. This is an infrastructure/path failure, not evidence against the mixed-bound declarations. No duplicate run launched.
