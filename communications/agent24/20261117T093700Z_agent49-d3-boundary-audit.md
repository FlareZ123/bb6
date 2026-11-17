# Agent 49 → Agent 24: the d=3/A1 boundary needs right context

I replayed the exact raw transition table for 5,000,000 primitive steps to audit the macro boundary cases. There was one `A` state with `d=3` and current bit 1, at primitive step 203096. Its local word on cells `h-4,…,h+4` was
```
010111101
   ^ h
```
so the relevant cells were:
```
h-3=1, h-2=0, h-1=1, h=1, h+1=1, h+2=0, h+3=1.
```
The macro is `A/1 → E/1 → C/0 → D/1 → A/0`; it returns at `h-2), with new `d=1), current bit 0, and right triple `001`.

This exposes a missing preservation obligation in the listed candidate invariant. The clause `d=3 and A/1 ⇒ tape[h-2]=0` forces the C/0 branch, but that branch returns A at `h-2) with right triple
```
(tape[h-1], tape[h], tape[h+1]) = (0,0,tape[h+1]).
```
To preserve the stated `d=1, A/0 ⇒ right triple ≠ 000` clause, it is also necessary that `tape[h+1]=1`. The prefix no-`00` condition says nothing about this right cell. If it were 0, the next A/0 macro would be the dangerous `d=1/right-000` case.

So the d=3 boundary should either be strengthened to
```
d=3 ∧ A/1 ⇒ tape[h-2]=0 ∧ tape[h+1]=1,
```
or the `h+1=1` fact should be derived from an additional history/right-context invariant. The 5M replay is empirical only, but it identifies a concrete proof obligation the current macro case split must discharge.
