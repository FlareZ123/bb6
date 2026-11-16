# #623 boundary-correlation replay

**Evidence type: independent exact raw-tape simulation, not a proof.**

After identifying the missing d=3/A1 correlation in `BoundaryCounterexample.md`, I replayed the original six-state transition table from the blank tape for 2,000,000 primitive steps, tracking the left frontier `lo=min(head positions so far)` and checking the candidate A-state clauses before each A transition.

Observed:
- 598,971 A-state visits;
- zero violations of the listed candidate invariant;
- 524 visits with d=1 and A/0, zero with right-three `000`;
- exactly 1 visit with d=3 and A/1;
- that one visit had second-left bit 0 and right1 bit 1;
- zero visits to the problematic d=3/A1 / second-left-0 / right1-0 combination.

The missing condition exposed by the synthetic macro counterexample is therefore consistent with the blank-root replay for 2,000,000 primitive steps:

`d=3 ∧ A/1 ∧ tape(head-2)=0  ->  tape(head+1)=1`.

This is only a finite empirical check. It does not prove the extra condition for all time, nor that the original candidate invariant is inductive. It identifies a plausible strengthening that the next formal macro proof must establish from earlier history.

## Exact transition table

States A–F; each entry is `(write, direction, next)` with R=+1 and L=-1:

| State | read 0 | read 1 |
|---|---|---|
| A | (1,R,B) | (0,L,E) |
| B | (0,R,C) | (1,R,C) |
| C | (0,R,D) | (1,L,A) |
| D | (1,L,D) | (0,L,A) |
| E | (1,L,F) | (1,L,C) |
| F | halt | (0,L,A) |

The replay used a sparse set of 1-positions, blank elsewhere, starting with state A at head 0 and `lo=0`; after each move it updated `lo=min(lo,newHead)`. No randomness or sampling was involved.