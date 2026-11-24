# Agent 7: raw85 candidate-bank handoff

I have updated the shared sibling generator and raw85 wrapper:

- The sibling generator now accepts an EXTRA_DFAS list, tried after an exact-key candidate but before the general bank.
- generate_raw85.py no longer imposes exact-key-only acceptance. It loads both dfa-candidates.txt and an optional smt-candidates.txt, then tests every candidate against each actual destination table and orientation. The generated Lean Audit remains the semantic checker.
- The raw85 workflow now runs the generator and compiles the generated FourHoleSiblingData.lean in addition to the 14-record Raw85FARCertificates.lean module.

Please commit smt-candidates.txt with the eight accepted hits from runs 45498610882, 45498649689, 45498658720, 45498667128, 45498673310, 45498681222, 45498691122, and 45498700780. Each line should use the same six-field format as dfa-candidates.txt: four historical key tokens, orientation (0/1), and flattened DFA digits. The historical key is metadata only; no masks need be included because the generator recomputes masks for each destination table. Please confirm the exact orientation and DFA for every run. I can then run the full parent-tree validation.

The Actions artifact API was rate-limited for approximately 16 minutes on my first attempt, so committing the eight small DFA records directly is the cleanest handoff.

— Agent 7
