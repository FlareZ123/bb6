# #623 A-state macro invariant: closure audit and finite counterexamples

**Status:** intermediate analysis only. This is not a proof about the blank-root orbit. It checks whether the candidate A-state conditions circulated on 2026-11-15 are closed under the exact macro transitions.

## Exact A-to-A macro transitions

Using the table in Machine623Path.lean (in particular C/1 = 1LA, directly returning to A):

For A/0 at head x:
- C/1 returns A at x+1.
- C/0 followed by D/1 at x+3 returns A at x+2.
- C/0,D/0,D/1 at x+1 returns A at x.
- C/0,D/0,D/0,D/1 at x returns A at x-1.

For A/1 at x, let the left context be (tape(x-1),tape(x-2)):
- 00 halts through E/0,F/0.
- 01 returns A at x-3 through E/0,F/1.
- 10 returns A at x-2 through E/1,C/0,D/1; the new current bit is 0.
- 11 returns A at x-3 through E/1,C/1.

These positions and writes were checked against the source transition table. The C/1 branch is not a D scan.

## Candidate conditions under review

The circulated candidate was:
1. At d=0, A reads 0 and the three cells immediately right are not 100.
2. At d>0, tape(lo)=1 and the visited prefix [lo,x-1] has no adjacent 00.
3. At d=1, if A reads 1 then x-1=1; if A reads 0 then the right triple is not 000.
4. At d=3, if A reads 1 then x-2=0.

The following configurations satisfy these conditions but their next A state violates one of them. Therefore these conditions alone are not inductive over all locally admissible states.

| Old state | Exact macro | New state violating condition |
|---|---|---|
| d=2, prefix 11, A/0, right pair 11 | C/1 returns A at x+1 | d=3 A/1 with second-left=1 |
| d=3, prefix 101, A/1, x+1=0 | E/1,C/0,D/1 returns A at x-2 | d=1 A/0 with right triple 000 |
| d=3, prefix 111, A/0, right triple 100 | C/0,D/0,D/1 returns A at x | d=3 A/1 with second-left=1 |
| d=4, prefix 1111, A/0, right triple 000 | C/0,D/0,D/0,D/1 returns A at x-1 | d=3 A/1 with second-left=1 |
| d=6, prefix 111111, A/1, left context 11 | E/1,C/1 returns A at x-3 | d=3 A/1 with second-left=1 |

For the d=6 row, the new A is at distance 3; its current bit is the old x-3 bit (=1) and its second-left bit is old x-5 (=1). This is a genuine local counterexample to closure, even though the actual root replay did not exhibit it.

The dangerous d=1/A0/right-000 state is itself a finite halting cylinder: its A/0 D sweep returns A/1 at the left frontier, after which E/0,F/0 halts. Likewise, a d=3/A1 state with second-left=1 returns A/1 at d=0 (whether the left context is 01 or 11), then halts.

## Exact 2,000,000-step replay (empirical only)

I re-ran the blank-root machine with C/1 -> A and the exact table. The summary matched the stored context counts:
- 2,000,000 primitive steps, no halt.
- 598,971 A visits; 199,617 A/1 and 399,354 A/0.
- A/1 left contexts: 11 = 197,699; 10 = 1,465; 01 = 453; no 00.
- Exactly one d=3 A/1, and its x+1 bit was 1.
- Zero d=2 A/0 states with right pair 11.
- Zero d=3 A/0 states with right triple 100.
- Zero d=1 A/0 states with right triple 000.
- There were two d=4 A/0/right-000 states, but neither had old x-1=1 (so neither caused the d=3/A1 failure).
- Among 516 d=6 A/1 states with left context 01 or 11, only one had old x-3=1; in that case old x-5=0, so the new d=3/A1 state satisfied the special condition.

These observations suggest the missing information is a correlation between the prefix suffix, d, and the local right context. A finite suffix automaton with exact distance classes through at least d=6 (and a saturated larger-distance state) may be a more natural invariant than the four scalar clauses. The d=3 condition has predecessors at d=2 (A/0,C/1), d=4 (A/0,D sweep), and d=6 (A/1,C/1), so all three predecessor families need compatible suffix constraints.

No source file or formal theorem was changed by this audit.
