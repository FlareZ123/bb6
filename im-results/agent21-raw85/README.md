# raw85/F1=1RA four-hole FAR frontier

Status: **intermediate; not yet a Lean theorem for the complete parent tree.**

## Target and tree

Parent partial table:

`1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1RA`

The current dynamic-split sibling generator's blank-run classifier gives a first hole at the root, then a 24-way split. A JS reproduction of its classifier and dynamic split-slot recursion produced 5,881 unique partial tables: 3,774 cycle leaves, 1,761 last-hole leaves, 245 split nodes, and 101 open leaves.

## FAR candidates

The existing 121-entry DFA bank finds 101 candidates under the Python mask routine. However, one bank DFA has `dfa[0]=1`; `FAR.Data.fastValid` requires `push start false = start`, so the Python mask routine is missing a necessary condition. Enforcing `dfa[0]=0` leaves 79 open leaves covered and 22 without a candidate in the existing bank.

Canonical restricted-growth DFA enumeration matching `FAR.dfaList` through 5 states found valid start-preserving candidates for 14 of those 22 leaves (sizes 4 or 5). Candidate lookup keys and DFAs are in `dfa-candidates.txt`. These are search outputs only: they still need exact Lean `Data.fastValid` checks.

The eight remaining tables are listed in `smt-frontier.txt`. Eight targeted Agent7 composed-SMT workflow runs completed successfully; for each run, the shard-0 steps “Install Lean if there is a candidate” and “Independently check every hit against infinite-tape semantics” both succeeded. However, a direct comparison of the first artifact's HIT row with the first `smt-frontier.txt` entry exposed a target-code mismatch. Therefore these eight artifacts must be treated as candidate sources, not as certificates for the eight listed frontier tables. The updated recovery workflow preserves each artifact's actual source table and DFA in `smt-candidates-provenance.md`, then tests the DFA against the actual raw85 destination leaves. Run IDs:

- `45498610882`
- `45498649689`
- `45498658720`
- `45498667128`
- `45498673310`
- `45498681222`
- `45498691122`
- `45498700780`

The SMT hits are workflow-validated for their own source tables, but the artifact target mismatch means they do not automatically close the eight `smt-frontier.txt` tables. Their DFA strings are now recovered as untrusted cross-key candidates; the generated parent-tree Lean audit must establish which actual raw85 leaves they cover.

## Next actions

1. Run the updated artifact-recovery workflow and preserve the eight actual source-table/DFA records; do not equate them with the eight `smt-frontier.txt` entries.
2. Try all 14 canonical and eight SMT DFAs as untrusted candidates against each actual raw85 open destination table.
3. Compile the generated 24-child parent tree with Lean; any accepted `.far` leaf must pass the actual `Data.fastValid` check.
4. If any of the eight listed frontier tables remain uncovered, synthesize candidates specifically for those destination tables rather than assuming the old run IDs cover them.
5. Only after the full audit compiles, integrate the resulting theorem into the 124-table roster and update the human-readable research synthesis.

Do not move this file into `results/` until the full source-checked parent-tree theorem exists.

## Destination-table reuse and validation (24 November 2026)

The four-token keys in dfa-candidates.txt are search metadata, not proof premises. A direct comparison of all 14 DFA strings with C00–C13 in Raw85FARCertificates.lean confirms that every candidate DFA is present in a Lean Data object for its actual destination table, while none of the matching historical keys equals that destination table's key (p[5], p[1], p[8], p[10]). The old exact-key-only wrapper was therefore removed. The current wrapper tries the 14 canonical candidates and eight workflow-validated SMT candidates against every actual open destination table, recomputes masks, and relies on the generated Lean Audit/Data.fastValid checks for acceptance.

The shared start-zero filter correction is committed in the two four-hole generators and the three active FAR emitters. The raw85 validation workflow now retrieves the eight original shard-0 artifacts, extracts only their DFA/orientation records into smt-candidates.txt, preserves that file in the repository, runs the complete dynamic-split generator, and compiles the generated FourHoleSiblingData.lean alongside the 14 standalone Data certificates. The workflow is a 60-minute manual validation job because it includes the full 24-child parent-tree compilation.

**Not yet claimed:** the full parent-tree theorem is not established until this updated workflow completes successfully. The 101-leaf census and the 79+14+8 partition remain intermediate evidence until the generated tree compiles and is integrated into the 124-table roster.
