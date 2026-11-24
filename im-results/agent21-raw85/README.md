# raw85/F1=1RA four-hole FAR frontier

Status: **intermediate; not yet a Lean theorem for the complete parent tree.**

## Target and tree

Parent partial table:

`1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1RA`

The current dynamic-split sibling generator's blank-run classifier gives a first hole at the root, then a 24-way split. A JS reproduction of its classifier and dynamic split-slot recursion produced 5,881 unique partial tables: 3,774 cycle leaves, 1,761 last-hole leaves, 245 split nodes, and 101 open leaves.

## FAR candidates

The existing 121-entry DFA bank finds 101 candidates under the Python mask routine. However, one bank DFA has `dfa[0]=1`; `FAR.Data.fastValid` requires `push start false = start`, so the Python mask routine is missing a necessary condition. Enforcing `dfa[0]=0` leaves 79 open leaves covered and 22 without a candidate in the existing bank.

Canonical restricted-growth DFA enumeration matching `FAR.dfaList` through 5 states found valid start-preserving candidates for 14 of those 22 leaves (sizes 4 or 5). Candidate lookup keys and DFAs are in `dfa-candidates.txt`. These are search outputs only: they still need exact Lean `Data.fastValid` checks.

The eight remaining tables are listed in `smt-frontier.txt`. Eight targeted Agent7 composed-SMT workflow runs completed successfully; for each run, the shard-0 steps “Install Lean if there is a candidate” and “Independently check every hit against infinite-tape semantics” both succeeded. Run IDs, in table order:

- `45498610882`
- `45498649689`
- `45498658720`
- `45498667128`
- `45498673310`
- `45498681222`
- `45498691122`
- `45498700780`

The SMT hits are workflow-validated, but their DFA data still needs to be committed or transferred from the artifacts before the full tree can be generated.

## Next actions

1. Obtain the eight hit DFAs from Agent7's workflow artifacts.
2. Add the 14 canonical candidates and eight SMT hits to a dedicated raw85 DFA data set.
3. Add the missing `dfa[0]=0` check to the Python mask candidate filter; keep Lean `Data.fastValid` as the trust boundary.
4. Run the repaired dynamic-split generator over all 24 first-hole children and compile the entire audit with Lean.
5. Only after the full audit compiles, integrate the resulting theorem into the 124-table roster and update the human-readable research synthesis.

Do not move this file into `results/` until the full source-checked parent-tree theorem exists.

## Destination-table reuse and validation (24 November 2026)

The four-token keys in dfa-candidates.txt are search metadata, not proof premises. A direct comparison of all 14 DFA strings with C00–C13 in Raw85FARCertificates.lean confirms that every candidate DFA is present in a Lean Data object for its actual destination table, while none of the matching historical keys equals that destination table's key (p[5], p[1], p[8], p[10]). The old exact-key-only wrapper was therefore removed. The current wrapper tries the 14 canonical candidates and eight workflow-validated SMT candidates against every actual open destination table, recomputes masks, and relies on the generated Lean Audit/Data.fastValid checks for acceptance.

The shared start-zero filter correction is committed in the two four-hole generators and the three active FAR emitters. The raw85 validation workflow now retrieves the eight original shard-0 artifacts, extracts only their DFA/orientation records into smt-candidates.txt, preserves that file in the repository, runs the complete dynamic-split generator, and compiles the generated FourHoleSiblingData.lean alongside the 14 standalone Data certificates. The workflow is a 60-minute manual validation job because it includes the full 24-child parent-tree compilation.

**Not yet claimed:** the full parent-tree theorem is not established until this updated workflow completes successfully. The 101-leaf census and the 79+14+8 partition remain intermediate evidence until the generated tree compiles and is integrated into the 124-table roster.
