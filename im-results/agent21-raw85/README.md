# raw85/F1=1RA four-hole FAR frontier

Status: **intermediate; not yet a Lean theorem for the complete parent tree.**

## Target and tree

Parent partial table:

`1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1RA`

The current dynamic-split sibling generator's blank-run classifier gives a first hole at the root, then a 24-way split. A JS reproduction of its classifier and dynamic split-slot recursion produced 5,881 unique partial tables: 3,774 cycle leaves, 1,761 last-hole leaves, 245 split nodes, and 101 open leaves.

## FAR candidates

The existing 121-entry DFA bank finds 101 candidates under the Python mask routine. However, one bank DFA has `dfa[0]=1`; `FAR.Data.fastValid` requires `push start false = start`, so the Python mask routine is missing a necessary condition. Enforcing `dfa[0]=0` leaves 79 open leaves covered and 22 without a candidate in the existing bank.

Canonical restricted-growth DFA enumeration matching `FAR.dfaList` through 5 states found valid start-preserving candidates for 14 of those 22 leaves (sizes 4 or 5). Candidate lookup keys and DFAs are in `dfa-candidates.txt`. These are search outputs only: they still need exact Lean `Data.fastValid` checks.

The eight remaining tables are listed in `smt-frontier.txt`. The eight run IDs previously listed below are now **superseded**: the first artifact's HIT table did not match the first current frontier entry, and at least one of the eight artifacts contained no HIT record. They must not be used as certificates for this frontier.

The current exact-target solver runs are dispatched from `.github/workflows/agent7-far-hard-root.yml` with the full table code in the workflow run name (`Agent 7 FAR SMT: <code>`). Each target uses the composed encoding, DFA sizes 6–8, and a 120-second per-size/orientation timeout. The raw85 recovery workflow discovers completed successful runs by exact display title, downloads their shard-0 artifacts, checks that each HIT row matches its target code, and preserves the DFA/orientation records plus source-table provenance in `smt-candidates.txt` and `smt-candidates-provenance.md`.

Superseded historical run IDs (retained only to explain the earlier mismatch):

- `45498610882`
- `45498649689`
- `45498658720`
- `45498667128`
- `45498673310`
- `45498681222`
- `45498691122`
- `45498700780`

No exact-target SMT certificate is claimed until its artifact code is checked against the corresponding frontier entry. The 14 canonical candidate strings are mirrored by C00–C13 in Raw85FARCertificates.lean, but that file is an invalid scratch module: CI run 45503416279 found every Cxx.fastValid pxx assertion false. These strings remain untrusted candidate suggestions only; the generator recomputes masks for each actual destination table and Lean must validate the generated parent tree.

## Next actions

1. Wait for the eight exact-target solver runs named `Agent 7 FAR SMT: <table code>` to complete; confirm each successful run contains exactly one HIT for its target.
2. Run the artifact-recovery workflow to preserve the eight target-matched DFA/orientation records and their run provenance.
3. Try all 14 canonical and eight exact-target SMT DFAs as untrusted candidates against each actual raw85 open destination table, recomputing masks.
4. Compile the generated 24-child parent tree with Lean; any accepted `.far` leaf must pass the actual `Data.fastValid` check.
5. If any exact frontier target has no SMT hit or any open leaf remains uncovered, synthesize additional candidates specifically for that destination table.
6. Only after the full audit compiles, integrate the resulting theorem into the 124-table roster and update the human-readable research synthesis.

Do not move this file into `results/` until the full source-checked parent-tree theorem exists.

## Destination-table reuse and validation (24 November 2026)

The four-token keys in dfa-candidates.txt are search metadata, not proof premises. A direct comparison of all 14 DFA strings with C00–C13 in Raw85FARCertificates.lean confirms that every candidate DFA is present in a Lean Data object for its actual destination table, while none of the matching historical keys equals that destination table's key (p[5], p[1], p[8], p[10]). The old exact-key-only wrapper was therefore removed. The current wrapper tries the 14 canonical candidates and the eight exact-target SMT candidates (once recovered) against every actual open destination table, recomputes masks, and relies on the generated Lean Audit/Data.fastValid checks for acceptance.

The shared start-zero filter correction is committed in the two four-hole generators and the three active FAR emitters. The raw85 validation workflow now discovers the eight exact-target solver runs by their run names, downloads their shard-0 artifacts, checks each HIT table against smt-frontier.txt, extracts DFA/orientation records into smt-candidates.txt, preserves candidate and provenance files, runs the complete dynamic-split generator, and compiles the generated FourHoleSiblingData.lean. The known-invalid Raw85FARCertificates.lean scratch module is deliberately excluded from the proof workflow. The workflow is a 60-minute manual validation job because it includes the full 24-child parent-tree compilation.

**Not yet claimed:** the full parent-tree theorem is not established until this updated workflow completes successfully. The 101-leaf census and the 79+14+8 partition remain intermediate evidence until the generated tree compiles and is integrated into the 124-table roster.
