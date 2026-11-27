# Finite directed control-state simulation

A sparse machine with a proved infinite run can serve as a source for another sparse machine without requiring a state permutation. A relation on the 36 ordered state pairs is accepted if it contains (A,A) and, for each related pair and scanned symbol, every assigned ordinary source transition has an assigned ordinary target transition with the same write and direction and related successors. The default-completion nonhalting theorem excludes source-hole steps. Induction therefore transfers nonhalting to every compatible target completion.

This is useful for two exact pairs in the Raw13 #1093 four-hole difficult list (zero-indexed): 49→47 and 51→55. The first is 0RF→0RA at E0 with an allowed successor pair (F,A); the second is 0RB→0RF at E0 with allowed pair (B,F). These are directed, not permutations. Source proofs remain necessary. No timeout is used as a premise. Lean module pending CI.
