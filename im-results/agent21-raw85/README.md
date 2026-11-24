# raw85/F1=1RA four-hole FAR frontier

Status: **intermediate; not yet a Lean theorem for the complete parent tree.**

## Target and tree

Parent partial table:

`1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1RA`

The current dynamic-split sibling generator's blank-run classifier gives a first hole at the root, then a 24-way split. A JS reproduction of its classifier and dynamic split-slot recursion produced 5,881 unique partial tables: 3,774 cycle leaves, 1,761 last-hole leaves, 245 split nodes, and 101 open leaves.

## FAR candidates

The existing 121-entry DFA bank finds 101 candidates under the Python mask routine. However, one bank DFA has `dfa[0]=1`; `FAR.Data.fastValid` requires `push start false = start`, so the Python mask routine is missing a necessary condition. Enforcing `dfa[0]=0` leaves 79 open leaves covered and 22 without a candidate in the existing bank.

Canonical restricted-growth DFA enumeration matching `FAR.dfaList` through 5 states found candidate DFAs passing the Python search filters for 14 of those 22 leaves (sizes 4 or 5). Candidate lookup keys and DFAs are in `dfa-candidates.txt`. These are untrusted search outputs, not Lean-accepted certificates.

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

The exact-target runs have now completed: five of the eight tables produced HIT records and three produced no hit at DFA sizes 6–8 with 120 seconds per size/orientation. The five actual DFA/orientation records and all eight run outcomes are preserved in smt-candidates.txt and smt-candidates-provenance.md. The three no-hit tables are:

- `1RB0LE_1RC1LF_0RD1RF_1LD1RE_---0LB_0RC1RA`
- `1RB0LE_1RC1LF_0RD---_1LD1RE_1RA0LB_0RF1RA`
- `1RB0RD_1RC1LF_0RD1RF_1LD1RE_---0LB_1RC1RA`

The first uncovered key reported by the initial generator attempt is `('1RF','0LE','---','0RC')`, exactly the first of these no-hit tables. The complete scan now being added will enumerate any further uncovered leaves across the whole 24-child tree.

The 14 canonical candidate strings are mirrored by C00–C13 in Raw85FARCertificates.lean, but that file is an invalid scratch module: CI run 45503416279 found every Cxx.fastValid pxx proposition false. These strings remain untrusted candidate suggestions only; the generator recomputes masks for each actual destination table and Lean must validate the generated parent tree.

## Next actions

1. Use the all-leaf candidate scan to enumerate every raw85 open table not covered by the current global bank plus 14 canonical and five exact-target SMT candidate DFAs.
2. Search the three no-hit frontier tables and any additional uncovered leaves with larger DFA sizes/timeouts or a different synthesis strategy.
3. Re-run the destination-table generator after each useful candidate batch; all masks are recomputed and Lean remains the acceptance boundary.
4. Compile the generated 24-child parent tree with Lean; any accepted `.far` leaf must pass the actual `Data.fastValid` check.
5. Only after the full audit compiles, integrate the resulting theorem into the 124-table roster and update the human-readable research synthesis.

Do not move this file into `results/` until the full source-checked parent-tree theorem exists.

## Destination-table reuse and validation (24 November 2026)

The four-token keys in dfa-candidates.txt are search metadata, not proof premises. A direct comparison shows that the 14 candidate DFA strings were copied into the dfa fields of C00–C13 in Raw85FARCertificates.lean, and their historical keys differ from the corresponding destination-table keys (p[5], p[1], p[8], p[10]). However, CI run 45503416279 found every Cxx.fastValid pxx proposition false: those copied Data objects are invalid. This comparison therefore establishes only the candidate/key relationship, not successful cross-key reuse. The old exact-key-only wrapper was removed; the current wrapper treats the 14 canonical and five exact-target SMT DFAs as untrusted candidates, recomputes masks for each actual destination table, and relies on the generated Lean Audit/Data.fastValid checks for acceptance.

The shared start-zero filter correction is committed in the two four-hole generators and the three active FAR emitters. The raw85 validation workflow now discovers the eight exact-target solver runs by their run names and records five HIT/three NO HIT outcomes, downloads their shard-0 artifacts, checks each HIT table against smt-frontier.txt, extracts DFA/orientation records into smt-candidates.txt, preserves candidate and provenance files, runs the complete dynamic-split generator, and compiles the generated FourHoleSiblingData.lean. The known-invalid Raw85FARCertificates.lean scratch module is deliberately excluded from the proof workflow. The workflow is a 60-minute manual validation job because it includes the full 24-child parent-tree compilation.

**Not yet claimed:** the full parent-tree theorem is not established until this updated workflow completes successfully. The 101-leaf census and the 79-old-bank + 14-Python-candidate + 5-targeted-SMT-HIT search partition remain intermediate search evidence; none of those counts is a count of Lean-accepted leaves until the generated tree compiles and is integrated into the 124-table roster.
