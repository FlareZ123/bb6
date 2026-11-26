# F421: one-hole Raw139 holdout

## Exact target

The standard blank-start table is

\`1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---\`

with initial state A and the single unassigned instruction F1. The held-out family ledger identifies this rooted member as F421; its canonical representative is recorded in \`im-results/agent8-coverage-contract/LedgerTextRows.lean\` with state order \`FDAEBC\`, canonical root C, and no tape reflection.

This is the unresolved \`E0=1LD, A1=0LC\` branch of the seven-hole Raw139 parent in \`im-results/agent41-raw139-small/Raw139SmallPair.lean\`. It is distinct from the already source-proved \`E0=1LD, A1=0LE\` upstream neighbor and from the \`E0=1LA\` sweep closure.

## What is established

A deterministic blank-start simulation of the exact table has completed **2,000,000,000 transitions without reading F1**. Checkpoints preserve the complete finite tape as its set of one-positions:

- \`state-1b.json\`: step 1,000,000,000; state D; head 88,184; visited interval [-69, 89,969]; 45,013 ones.
- \`state-2b.json\`: step 2,000,000,000; state B; head 119,870; visited interval [-69, 124,107]; 62,084 ones.

The tape is nearly alternating over its visited interval, with a small number of equal-adjacency defects (38 at 1B; 44 at 2B). This is an empirical structural observation, not an invariant proof.

If the missing F1 instruction is completed by a halting transition and is eventually read, the resulting six-state machine has a score **greater than 2 billion**. If F1 is never read, that completion is nonhalting. Neither eventual reachability nor permanent avoidance has been established. The 2B simulation is therefore not yet a BB(6) lower-bound theorem.

The earlier \`generate.mjs\` audit only explored this leaf for 500 steps and left it open. An exhaustive search of the repository's existing FAR certificate scheme found no witness with DFA sizes 1 through 5. Those negative searches are finite and do not imply that a larger FAR invariant is impossible.

## Current research action

\`search_far.cpp\` enumerates every canonical six-state DFA of size 6 for the existing \`FAR.Data\` certificate scheme, in both tape orientations. It independently checks the synthesized masks against the exact \`fastValid\` conditions before emitting a candidate. Any emitted certificate must still be checked by Lean's \`FAR.Data.fastValid_sound\` and the original-machine bridge; a search result alone is not a proof.

The existing manual workflow \`.github/workflows/agent41-raw139-small.yml\` has an optional \`f421-far-search\` target. This reuses the family's workflow rather than adding another workflow file.

## Remaining mathematical question

Prove either:

1. F1 is never read, using an all-time stack, defect-word, or finite-automaton invariant; or
2. F1 is first read at a finite time, then source-certify the exact halting completion and its primitive-transition score.

Do not promote finite traces, an unverified automaton search, or the observed alternating tape pattern to a proof.
