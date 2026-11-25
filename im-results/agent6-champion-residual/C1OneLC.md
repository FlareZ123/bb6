# raw139 C1=1LC: exact growing sweep and remaining search frontier

2026-11-25, Agent 6. Distinct from C1=0LC and Agent 48's F1 work.

## Exact new recurrence

Partial table in A0,A1,...,F0,F1 order, codes 4q+2w+d with d=1 right and 24 unknown:
`[7,2,11,21,14,10,3,16,12,11,24,3]`.
Only F0 is unassigned. In the head-inclusive left zipper, set C(m)=(F,10·1^m,empty).
Blank reaches C(6) in 46 transitions. For every m>=2,
`C(m) -> C(m+13)` in exactly `16*m+123` live transitions.
The proof uses two E sweeps (3 transitions per mark), two F sweeps (5 per mark), and explicit fixed turns, all proved for arbitrary tails. Thus F0 is never queried on the blank orbit; all compatible completions are nonhalting. Source `C1OneLCSweep.lean` contains the `never_of_growth` and weighted cover bridge. The recurrence, entry and family growth compiled in local Lean 4.36.0-rc2 against copied computational definitions; axiom sets [propext, Quot.sound]. Full original-import audit and integration are still required. This is not a complete C1=1LC cover.

## Computational search

Parent `[7,24,11,24,14,10,3,16,12,11,24,24]`. First-hole split at cap 250 yielded 71 internal splits, 1160 cycle candidates, 315 last-hole candidates, and 159 undecided leaves. One-sided FAR search up to 5 states reduced the undecided list to 16; deeper bounded simulation up to 5000 transitions identified 2 more cycle and 2 last-hole candidates. All census and FAR claims are heuristic search data until replayed in Lean. Twelve remaining entries before the new sweep (F0 or B1 unknown):

```
[7,2,11,21,14,10,3,16,12,11,24,3]   # solved recurrence above, full import audit pending
[7,7,11,21,14,10,3,16,12,11,24,17]
[7,20,11,21,14,10,3,16,12,11,24,17]
[7,21,11,24,14,10,3,16,12,11,9,3]
[7,21,11,24,14,10,3,16,12,11,1,9]
[7,21,11,24,14,10,3,16,12,11,3,9]
[7,21,11,24,14,10,3,16,12,11,5,9]
[7,21,11,24,14,10,3,16,12,11,7,9]
[7,21,11,24,14,10,3,16,12,11,13,9]
[7,21,11,24,14,10,3,16,12,11,17,9]
[7,21,11,24,14,10,3,16,12,11,7,14]
[7,22,11,24,14,10,3,16,12,11,23,1]
```

The second and third entries show a common +14 even-width counter in bounded tests, with respective costs 19m+156 and 25m+208, but no formal result yet. Next goal is to prove both using shared E sweep and paired F sweeps, then close the rest; do not infer a global bound from these candidates.
