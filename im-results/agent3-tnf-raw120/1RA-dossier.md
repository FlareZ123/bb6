# Raw120 E0=1RA: asymmetric finite-automata candidates

Parent `1RB---_1RC---_0RD---_1LD1RE_1RA1LE_------`. The deterministic first-hole census has 1329 splits, 19345 translated-cycle leaves, 6849 last leaves and 4374 open leaves, with open-list SHA256 `af3b4cfbb7f4d3dcde52253b7834602fe505fbdf0c3da9a49b29aaf5c075affe`. The existing ten FAR banks cover 4286 of the open leaves.

**New candidate assignments:** 52 of the remaining 88 leaves have finite two-sided stack-summary automata. The manifest [1RA-bidfa.txt](1RA-bidfa.txt) records exact leaf index (the open-list hash is pinned), left and right DFA transition tables in base 36 (no orientation prefix), and the independently replayed fixed-point state and inverse-edge counts. The local C++ search tested identical pairs first and then ordered asymmetric pairs over 458 distinct DFA tables in the existing banks. A separate replay of the repository's `bidfa_emit.witness` algorithm reproduced all 52 state/edge counts and avoided each unassigned row. The generator pins the census and emits original-source `BiDFA.never` certificates; these have **not yet been compiled against the source**.

The remaining 36 leaves were screened with the existing one-block and two-block symbolic generators, including longer event separation. 32 have sweep candidates (leaf 1332 needs an explicit period-13 block and a 669-step return); leaf 2309 reaches its only unassigned slot F0 at primitive time 13311, giving prospective weighted bound 13317. Two additional leaves share the recursive invariant below. Only leaf 437 remains without a candidate proof. Reproduce with `python im-results/agent3-tnf-raw120/generate_sibling.py 1RA` after unpacking coverage source. The generator deliberately fails if any witness is missing. Agent13 is independently integrating 1LB.

## Recursive grammar for 1602 and 1606

The partial machines `1RB0RF_1RC1LB_0RD0LE_1LD1RE_1RA1LE_---1RB` and `1RB0RF_1RC1LC_0RD0LE_1LD1RE_1RA1LE_---1RB` share an exact return dynamics. At a fresh E left boundary, the right side is a unary run of length n+4 followed by zero-separated positive unary runs encoded by a grammar T:

* nil = empty;
* singleTwo = [2];
* pair(m,T) = [2,m+1] ++ T;
* big(r,T) = [r+3] ++ T.

The blank tape reaches (n,T)=(0,nil) in nine steps. A full positive-cost return sends (n,T) to (n+1,next(T)), with next(nil)=singleTwo; next(singleTwo)=big(0,singleTwo); next(pair(m,T))=big(m+1,next(T)); next(big(r,T))=pair(r,T). This inductive grammar rules out a singleton in the unsafe scan position. The proof handles arbitrary untouched left tails and uses induction on the grammar rather than a bounded trace. The only variant-dependent local split takes 9 or 11 steps.

`Raw120OneRAStack.lean` implements the recurrence and proves the primitive-step return, entry, growth and positivity. Local Lean 4.36.0-rc2 compiled these theorems against exact copies of the source zipper definitions and join lemma: advance depends on propext and Quot.sound, growth additionally on Classical.choice. The final original-source `never_of_growth` application awaits CI; no source-accepted status claimed. The explicit missing leaf is 437: `1RB0LF_1RC0RE_0RD---_1LD1RE_1RA1LE_1LE1LA`.
