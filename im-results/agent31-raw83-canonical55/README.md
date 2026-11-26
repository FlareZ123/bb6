# Raw83 → Canonical55 conditional reduction (prepared)

**Status:** integration draft only. No Canonical55 theorem or new global upper bound is claimed.

## Mathematical input

The exact four-hole parent is

\`1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RA\`

with 25^4 = 390,625 compatible completions. The source-accepted parent theorem is \`BB6.Agent10Raw83.all_completions\`, with weighted bound 514 (run [45755362807](https://github.com/FlareZ123/bb6/actions/runs/45755362807), artifact 15087730774). The exact table and original-source Cover are already established; this project does not repeat its child search.

## Intended proof edge

The accepted chain is currently:

1. Canonical59: five parent Covers, 59 retained representatives (run 45880290680).
2. Canonical58: add Raw113, leaving 58 (run 45891227622, artifact 15151767938).
3. Canonical57: Raw112 after Raw113, owned by Agent17; parent recovery run 45890012441 is still in progress and not yet accepted.
4. Canonical56: Raw59 after Canonical57, owned by Agent32; source parent Cover is accepted (run 45786187618), but the relocation/integration is not yet accepted.
5. **This project:** add Raw83 after the accepted Canonical56, yielding 55 retained representatives.

The planned final theorem has exactly 55 Cover hypotheses at the champion score. It must explicitly preserve the three earlier removals (Raw113, Raw112, Raw59), prove Raw83 is a unique member of the actual Canonical56 roster and distinct from those parents, lift its source Cover to the common weighted floor 6,766,859, and compile the exact complement/soundness/fixed-score consumer with the permitted standard axiom profile.

## Files and acceptance

- \`Canonical56Raw83Membership.lean\`: membership/distinctness and source-Cover lift.
- \`Canonical55Raw83Graft.lean\`: the 56→55 exact parent-removal theorem.
- \`assemble_canonical56_raw83_graft.py\`: pins and verifies the Canonical56 run/artifact, imports the Raw83 source closure, compiles the membership chain and final consumer, and emits a digest-bearing report.
- \`Canonical58Raw83Membership.lean\`: existing current-chain preflight, including the corrected \`p83_distinct_from_p113\` axiom audit name.
- Shared manual workflow target: \`canonical55-raw83-graft\` in \`.github/workflows/agent31-canonical71-raw109.yml\`.

No per-commit workflow is introduced. The next action is to wait for the accepted Canonical56 artifact, then dispatch the existing shared workflow target with its run ID. Until the final Lean/source/axiom gate passes, this remains an intermediate proof-integration plan, not a publishable result or BB(6) solution.
