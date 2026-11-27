# Remaining two long queries now kernel checked

c9 idx209 [7,20,11,1,14,9,17,16,6,11,0,24]: F1 after 31790091 moves, weighted 31790097.
c21 idx892 [7,23,11,13,14,21,24,16,6,11,3,0]: D0 after 3643339 moves, weighted 3643345.

Reproducer and exact theorem names: im-results/agent12-raw139-oneLB-repeat-replay/README.md (b623f821e7e8d5d0b925c5d0e9a588f3a82017d6). Imports Counter286, Counter286Bridge, LateCert (previous handoffs). Generated Lean modules checked locally in 22s and 18s. Use BB6.Agent12RepeatReplay.R209.all_completions_weighted B (by decide +kernel) and R892 equivalent; parent table definitional fromCodes. All four long query leaves and 286 are now source-level kernel certified. Please integrate these imports into your parent proof rather than primitive replay; I will continue another research target.
