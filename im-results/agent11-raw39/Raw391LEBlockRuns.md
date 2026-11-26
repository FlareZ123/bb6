# Raw39 1LE block-run invariant: 6270 and 16538

Literal machines:
```
6270  1RB1LE_1RC1LA_0RD0RD_1LD0RA_0LB0LF_---0LA
16538 1RB1LE_1RC1LA_0RD0RD_1LD0RA_1LB0LF_---0LA
```
All completions of F0 never halt. Use blocks X=101 or 111 and Y=001; x is 101 in 6270 and 111 in 16538. At A with empty left word and right (including scan) 1 W 1, W is either one X, or a sequence of X-runs separated by nonempty Y-runs, possibly preceded by Y, with internal X-runs >=3 and terminal X-run >=2. The initial section occurs after 11 steps.

In synchronized S mode the right word is W 1, in T mode it is 1 W 1. Reading k X blocks creates a left run 00 1^(3k+1); a singleton Y consumes the next X and saves the old run, beginning another. Saved runs have k>=3 except the optional bottom k=0. The exact primitive-to-macro rules are verified by run0 with arbitrary finite tails and lifted to the original raw run at every head.

If the right word ends, the current run is incremented to 3k+2 and swept left, emitting Y^k xx. Each remaining saved run is incremented to 3j+2 and, using the first two Y blocks, swept to emit Y^j xxX0 before the residual suffix (X0=101). Each non-bottom saved j>=3 permits the next switch; bottom j=0 terminates. If a gap of >=2 Y is met, the left active run loses its first zero and enters T; a 3k+1 run with k>=3 emits Y^(k-1) x, leaves a fresh run 0011 and decreases the next gap. A second YY switch consumes the new two-one run and produces three X before the residual Y^(k-3) and x, preserving Core. The bottom k=0 pops with one X. Both cases end with empty left and a grammatical right word. The proof includes the singleton initial word and possible initial Y-run.

Lean 4.36.0-rc2 compiled firstReturn and never against the accepted artifact 15036330602 dependency objects. Axiom report both [propext, Quot.sound]. SHA256 decoded source 3cfb05edb3242a7eae387db247eaf12428dc0f9bb0ed1e72a247b48a8269be44. The theorem BB6.Agent11Raw391LEBlockRuns.never v m hm is dispatched for .a and .b. Neither complete LE semantic partition nor global parent Cover is claimed.
