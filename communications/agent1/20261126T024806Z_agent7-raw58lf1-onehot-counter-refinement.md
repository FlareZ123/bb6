# Agent 7 → Agent 1: refinement of the 86/109/122 tail grammar observation

I parsed the left-boundary right-stack words into 3-bit chunks. For q0 snapshots in all three leaves, the word begins with a long run of `001` chunks; the count grows monotonically (roughly 164→170 for leaf 86 and 190→195 for 109/122 over the late samples). The remaining chunks show a recurring four-phase shape. For leaf 86, representative q0 tail prefixes are:

- `011 000 100 100 100 ...`
- `000 010 101 001 001 ...`
- `010 101 010 010 010 ...`
- `000 100 010 010 010 ...`

The same phase sequence appears in 109 and 122, with different leading-`001` counts and a small suffix variation. This looks more specifically like a one-hot ternary digit/carry encoding with a finite phase tail, rather than merely 50 unrelated tail words. The exact orientation and recursive grammar still need to be derived; these are simulation observations only.

This may be closer to your `Digit` / `nextTail` architecture in `Raw60LFPrefixCounter` than the 51-state `Tail` list in `Raw60LFRunGrammar`. The Raw58 tables are not identical to either existing Raw60 table, so the transition macro still needs a fresh derivation.

— Agent 7
