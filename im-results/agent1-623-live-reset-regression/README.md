# Agent 1 — live reset-product regression for machine #623

**Status: intermediate reproducibility correction, not a BB(6) theorem.**

This dossier records a concrete incompatibility among the current checked-in #623 finite-diagnostic artifacts. It matters because the all-time reset-language program should not build on the maintained claim that every correction-only S-window in the 9,968-transition prefix is accepted until this regression is reconciled.

## Current-file replay

Using the source-faithful `evalA` / `drainB` / `highLevelNext` recurrence from the maintained #623 scripts, the correction-only S-window

[
B=34\ell_S+122,qquad
(3^{\ell_S}-1)/2\ge S+3,
]

and the current 263-state `ResetPatternDFA.json`, a fresh replay of source transitions `D33 -> D34` through `D10000 -> D10001` gives:

- 9,968 transitions tested;
- **one target word with no reset acceptance**, at source transition **n=652**, target state **D653**;
- among the remaining accepted windows, 80 post-reset suffixes have universal paired-carry image rank > 1 under the current 211-state subset DFA;
- 26 accepted suffixes end in the current B1 recurrent component.

These numbers do **not** reproduce the maintained 9,968/9,968 acceptance and 84 nonsynchronizing-suffix census.

The exact failing target word is the D653 correction-only window with `k=8`, `j=24`:

[
[3,7,5,3,1,5,6,6,7,5,5,5].
]

Running the current 263-state DFA from its initial state gives states

[
18,102,105,103,140,11,82,177,34,105,87,164,
]

never reaching its sole accepting state 3. Running the current `ResetPostStateDFA.post_reset_pair` on the same word ends with null output.

The separately materialized current `SWindowEdgeRecords.json` independently records target index 653 with source/target window indices `(8,24)->(8,24)`, so the window-index mismatch is not coming from this audit's recomputation.

## Current artifact identities

At the audit point:

- `ResetPatternDFA.json`: blob `0ea1573f535c746a6a52516a6feb76e97559267c`;
- `PairCarrySynchronizingSubsetDFA.json`: blob `cd93181cce839c06e71eb43955d8ee660a261c85`;
- `ResetPostStateDFA.json`: blob `b06d8aee727a2e33c8f93dbe7528762a4b0c4159`;
- `SWindowEdgeRecords.json`: blob `3591d3fb893ddefd355eee09ac098a4ee5702c36`.

The replay script is `audit_current_reset_product.js`.

## Interpretation

This is **not** a counterexample to the source machine's nonhalting, nor to the correctness of the reset DFA as an automaton for its stated language. It is a counterexample to the current repository-level finite claim that the exact correction-only S-window replay is accepted on all 9,968 transitions under the currently checked-in recurrence/window convention and currently checked-in DFA.

The earlier exact-seed table and B1/B2 exception census should therefore be treated as version-sensitive historical diagnostics until regenerated against one coherent artifact set. In particular, do not use the old 84-row table as a proof premise for an all-time induction.

## Mathematical lead retained

For every freshly recomputed accepted suffix ending in B1, the B1 identity `x_{i+1}=y_i` holds after entry into B1. The corresponding left dangerous residual is still

[
X-3Y = 2(g-9q)-\gamma_s.
]

On all 26 current-prefix B1 cases, the least absolute residue of `X-3Y` modulo the modulus supplied by the surviving B1 tail exceeds the sector-specific terminal-strip upper bound by a large margin. This is finite evidence only, but it preserves the useful arithmetic interpretation of B1. The priority is now to derive a source-level reset/root-language statement that survives D653, rather than assuming universal reset acceptance of the present S-window.

## Reproduce

From repository root:

```bash
node im-results/agent1-623-live-reset-regression/audit_current_reset_product.js
```

The script throws if the source recurrence halts before the tested prefix or if the current D653 word no longer matches the stated regression; otherwise it prints the current counts and the failing windows.
