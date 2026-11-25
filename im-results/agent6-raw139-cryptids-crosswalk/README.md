# Raw139 small-frontier crosswalk against Cryptids BB(6) proofs

**Status: intermediate source-catalogue crosswalk.** This is not a new nonhalting theorem and does not certify the Raw139SmallAudit parent contract. It belongs in \`im-results/\`.

## Inputs and exact scope

- Local candidate set: \`im-results/agent41-raw139-small/witness-data.json\`, cross-checked against the draft Lean source \`Raw139SmallAudit.lean\` (\`residual_count = 81\`, \`e0_count = 6\`). The current JSON contains 81 residuals: 75 prefix-open leaves and 6 E0 one-hole leaves. Older prose in the parent README/memory saying 83 total or eight one-hole leaves is stale relative to these committed source files.
- Upstream source snapshot: \`google-deepmind/cryptids\` commit \`3647718b5df22e1a61462dec0376bd204526285a\`. Its BB(6) proof tree contains 191 modules: 159 \`NonHalt\` and 32 \`Halt\`. The complete path/RLE/blob inventory is pinned in \`cryptids-191-manifest.tsv\`.
- Each source filename encodes its full 12-slot table with exactly one \`HHH\` row. The local residual RLE uses \`---\` for each unassigned row.

## Search performed

For every one of the 81 partial residual tables, compare every assigned transition against each of the 191 source tables under all 120 permutations of states B–F that fix the blank initial state A, and both tape-direction orientations. This is 240 transformations per source table, or 3,713,040 source/table/orientation comparisons. A source match requires exact equality at every assigned local slot; all erased local slots are wildcards.

The search finds **exactly three compatibility matches**, all in upstream \`NonHalt\` modules and all under the identity state map with no reflection:

| Local partial residual | Address | Holes | Upstream full source table |
|---|---:|---:|---|
| \`1RB---_1RC---_1LD---_---0LE_---1LF_0LD---\` | \`0LD\` | 6 | \`1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_0LD---\` |
| \`1RB---_1RC---_1LD---_---0LE_---1LF_1LA---\` | \`1LA\` | 6 | \`1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LA---\` |
| \`1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---\` | \`1LD>1LA>0RC>0RB>1LD>0LE\` | 1 | \`1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---\` |

The pinned source module paths and blob hashes, as well as first-erased-query diagnostics, are in \`matches.tsv\`.

## Transfer assessment

Only the third match is a direct all-completions nonhalting transfer: its sole erased row is F1, exactly the upstream source's \`HHH\` row. The source theorem \`is_not_halt\` rules out ever querying F1, so the source run is unchanged by every possible completion of that row. This is the already-known Cryptids leaf used in Agent41's separate \`Raw139CryptidsLeafPilot.lean\`; this crosswalk adds no new proof for it.

The two six-hole matches are **not** direct transfers. Their upstream source runs query other rows erased in the local partial tables:
- address \`0LD\`: first erased query is D0 at time 6 (the source move is \`1LA\`);
- address \`1LA\`: first erased query is B1 at time 7 (the source move is \`0RB\`).

Thus the upstream nonhalting theorems certify only the particular full source completions, not all completions of those six-hole partial tables. These two matches may guide a source-following refinement, but no local Cover is claimed and no residual is removed.

No other one of the 81 current residual tables matches any of the 191 source modules under the 240 rooted symmetries tested. This rules out additional direct filename-table transfers from this pinned source set under those transformations; it does not rule out other proof methods, future upstream modules, or non-isomorphic reductions.

## Reproduction

From the repository root, run:

\`\`\`sh
node im-results/agent6-raw139-cryptids-crosswalk/crosswalk.cjs
\`\`\`

The script uses only Node built-ins, the committed Raw139SmallAudit JSON, and the pinned module manifest. It asserts the 191/159/32 source inventory, 120 state permutations, 81 residual count, and the three-match outcome.

## Evidence limits

- This is an exact filename-RLE and partial-table compatibility crosswalk, not a source theorem compilation.
- The source files for the three matched modules were inspected at the pinned commit; each exports \`is_not_halt\`. The exact one-hole source is already used by Agent41's integration draft. Local RC2 source integration remains subject to that workflow's CI acceptance.
- The parent Raw139 finite audit is itself still a draft pending its source build and axiom audit. Its 81 count is the current committed Lean/JSON count, not an accepted BB(6) frontier result.
- No global BB(6) upper bound or exact value is established here.
