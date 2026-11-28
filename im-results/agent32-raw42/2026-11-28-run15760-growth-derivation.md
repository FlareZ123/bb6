# Raw42 0LE / Run15760 two-sweep analytic growth model (pending Lean)

The original 0LE heavy leaf `Raw420LERun15760` is the eleven-transition partial machine
`A0=1RB, A1=0RA, B0=1RC, B1=0LE, C0=0RD, C1=0LA, D0=1LD, D1=0LB, E0=1LF, E1=1RD, F0=0RA`; only `F1` is undefined.

A local exact zipper simulation found a simple regular-growth family at the moments the machine is in state E reading zero. `Z0` uses `l.headD false` as the head bit, with right tape `r` ordered away from the head and `rep P n` denoting n concatenations of word P.

```lean
A n := ⟨E, [0], [0,0,1,1,1] ++ rep [1,1] n ++ [0,1,1]⟩
B n := ⟨E, [0,0], [0,0] ++ rep [1,0] (n+1) ++ [1,1,1,1]⟩
run0 p 83 start = some (A 0)
run0 p (10*n+28) (A n) = some (B n)
run0 p (16*n+59) (B n) = some (A (n+1))
run0 p (26*n+87) (A n) = some (A (n+1))
```

All finite symbolic transfer laws were checked for arbitrary tails of lengths 0–7 in a separate JS zipper simulator, and the recurrence was checked for n=0,1,3 with exact zipper words. For example E0 visits occur at steps 83 (A0), 111 (B0), 170 (A1), 208 (B1), 283 (A2), 331 (B2), 422 (A3), etc. This is **computational evidence, not a Lean-accepted theorem yet**.

The [candidate source](Raw420LERun15760Growth.lean) encodes 10 finite local identities as literal `by rfl`, two `sweepR/sweepL` inductions via `SweepPumping`, two bit-word rotation lemmas, and `never_of_growth`. Its intended `Cover (WeightedBound B)` is universally quantified over all completions of this eleven-transition partial table; if proven and matched to the original generated Run15760 table, it can replace a large 78×67-state BiDFA certificate leaf with a short analytic proof. CI source check is [run 46160179628](https://github.com/FlareZ123/bb6/actions/runs/46160179628), **pending** at 2026-11-28T15:30:59.176Z. No published theorem or global bound decrement is claimed until source acceptance.

Because original g0p2 proof was killed during `Raw420LERun15760` in split run 46156341083, a separate exact original-certificate row repair remains running in [run 46158197180](https://github.com/FlareZ123/bb6/actions/runs/46158197180). The analytic proof is independent, not a reason to cancel the original-source repair.
