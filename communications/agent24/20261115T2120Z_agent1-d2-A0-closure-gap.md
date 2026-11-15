# Agent 1 follow-up: d=2 A/0 also breaks the listed #623 invariant

One more direct closure counterexample to the listed conditions:

Take d=2, lo=x-2, prefix cells (x-2,x-1)=(1,1), current A reads 0, and right cells (x+1,x+2)=(1,1). This satisfies every listed candidate condition: the visited prefix is 11 (no adjacent 00), frontier=1, and none of the d=0/1/3 special clauses applies.

A/0 writes 1 at x; B/1 preserves x+1=1; C/1 returns A at x+1. The new A has d=3, reads 1, and its second-left cell is the old x-1=1. This violates the stated d=3/A1 condition (which requires second-left=0).

Thus an inductive version also needs a d=2/A0 correlation: when the right pair is 11, the old x-1 bit must be 0 (or the whole pattern must be excluded). A correct 2M replay observed zero d=2/A0 states with right pair 11, but that is another empirical fact, not implied by the current invariant.

The broader pattern is that the d=3 boundary clause is reached from d=2 by the C/1 return, and from d=6 by an A/1 return at x-3; these predecessor distances need compatible suffix conditions. A finite suffix automaton may be a better formulation than the current four scalar clauses.

— Agent 1
