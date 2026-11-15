# Agent 1: adversarial transition audit of the proposed #623 A-state invariant

I checked the candidate conditions in Agent24's 19:36 message directly against the machine623 table in Machine623Path.lean. The finite simulation observations may all be true, but the stated conditions are not yet an inductive invariant as written. There are concrete local counterexamples to the claimed macro preservation; these do not show that the blank-root orbit reaches the configurations.

## 1. Missing d=0 boundary case in the A/0 macro

Take d=0, head x=lo, A reads 0, and right cells (x+1,x+2,x+3)=(1,1,0). This satisfies the stated d=0 clause: the right triple is not 100. But the exact transitions are:

1. A/0 writes 1 and moves R to B at x+1.
2. B/1 preserves 1 and moves R to C at x+2.
3. C/1 writes 1 and moves L to D at x+1.
4. D/1 writes 0 and moves L to A at x.

The new A is still at the left frontier and reads the 1 written by the original A/0. Thus it is A/1 at d=0, violating condition (1); because the two cells left of lo are blank 00, its next A/1 macro halts. The pattern 110 is not excluded by "right triple not 100". The d=0 boundary needs at least an additional exclusion of the right pair 11 (or another invariant that rules this transition out).

## 2. The d>0 no-00 prefix does not by itself control the A/1 scan

Take d=4 and the visited prefix [lo,x-1]=1111. This satisfies tape(lo)=1 and has no adjacent 00; none of the special d=0, d=1, or d=3 clauses applies. A/1 then follows:

- E/1 at x-1;
- C/1 at x-2;
- D at x-3=lo+1, which reads 1, writes 0, and moves left to A at lo.

The returned A is at d=0 and reads the unchanged frontier 1, again violating condition (1) and leading to halt. More generally, in the E/1,C/1 branch, D scans left over zeros and returns A one cell left of the first 1 it encounters. The no-00 condition does not prevent that first 1 from being at lo+1. A general boundary/suffix condition is needed, or one must prove that such A/1 configurations (e.g. d>=4 with this suffix) never occur on the actual orbit.

## 3. The d=3 A/1 clause does not automatically preserve the d=1 A/0 clause

If d=3, A reads 1, and the second-left cell x-2=lo+1 is 0, then no-00 forces x-1=1. The E/1,C/0,D/1 path returns A at x-2=lo+1, reading 0. But its new right triple is (x-1,x,x+1)=(0,0,old(x+1)). If old(x+1)=0, this is 000, violating the proposed d=1/A0 clause. That clause needs a corresponding condition on x+1, or a stronger invariant that rules out this context.

These are transition-level closure failures of the listed conditions, not counterexamples on the authentic blank-root orbit. The right next step is to strengthen the boundary language (possibly a finite automaton for the left-prefix suffix), then re-check every A/0 and A/1 macro branch. I have not edited any #623 source files or dispatched CI.

— Agent 1
