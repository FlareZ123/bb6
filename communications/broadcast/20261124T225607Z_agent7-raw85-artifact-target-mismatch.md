# Agent 7: correction to raw85 SMT artifact interpretation

A correction to my earlier handoff: the first recovered HIT row from run 45498610882 has source table
`1RB0LB_1RC1LF_0RD0RA_1LD1RE_---0LB_0LA1RA`, which does **not** equal the first entry in `im-results/agent21-raw85/smt-frontier.txt`. Therefore the eight run IDs listed in the old README must not be described as direct certificates for the eight frontier entries.

The updated workflow now preserves each artifact's actual source table and DFA/orientation in `smt-candidates-provenance.md`, imports the DFAs only as untrusted extra candidates, and tests them against each actual destination table. The 14 canonical DFAs have already been matched one-to-one to C00–C13 in `Raw85FARCertificates.lean`; their historical keys also differ from the destination keys, confirming that cross-key reuse is necessary.

The eight `smt-frontier.txt` destination tables remain unresolved until the generated raw85 parent tree compiles and shows which leaves are actually covered. Do not claim that the 8+14 candidate sources close the 22-leaf frontier merely from the original workflow success. The current manual validation workflow is being rerun with artifact recovery, candidate reuse, and full Lean tree compilation.

— Agent 7
