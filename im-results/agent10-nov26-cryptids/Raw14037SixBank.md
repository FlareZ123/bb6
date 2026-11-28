# Six-bank conversion for Raw140 siblings 37/40/44/83

## Proved transition

In the common partial table (A1,F0,F1 undefined), write F(u,v,w,s;X) for ER with left list 1 (133)^u 22 6^v 7 3^w X, right list tail(s), and arbitrary left suffix X. The six cyclic tails have ranks 0..5 in the order 542, 152, 1121, 5215, 1155, 11511; rho advances the rank, and e(s)=1 exactly at rank 5.

For all u,v,w natural:
F(u+2,v,w+3,s;X) -> F(u+e(s),v+9,w,rho(s);X)
in exactly 66u+66v+C(s) primitive steps, with C=(684,708,722,694,750,817).

The inner conversion EL(22 6^v 7 3 X, 1^k 5 Y) -> DR(62 6^(v+k+2) 7 X,Y) takes 22(v+k+2)+3k+38 steps for arbitrary X,Y. Three inner conversions, two 9-step turn1 bridges and one 9-step turn5 give the common core. The six prep rules, carry, tripLoop, pump and erMany then produce the F recurrence.

## Closed-form drain

Let z=6u+rank(s). Each conversion subtracts 11 from z, adds 9 to v, and subtracts 3 from w. If w >= 3N with N=floor(max(z-1,0)/11), exactly N applications are possible before u<2. The terminal z is z-11N, v'=v+9N, w'=w-3N. The formal drain theorem provides finite primitive reachability to that terminal with u'<2. It does not require a scan, a conjectured orbit bound, or the variant-specific rows. Any extension of the common table inherits the result through run_ext.

## Status

Raw14037SixBank.lean: local Lean 4.36.0-rc2 check against the restored Raw140 source closure from artifact 15220415544 (with the already-upstream ERExit simp repair). The printed axioms of inner, advance, drainN and drain are [propext, Quot.sound]. This is a conditional macro reachability result, not a decision of any sibling or a Cover. CI source closure and end-to-end invariant remain outstanding. The four sibling paths share this phase; the outstanding work is the finite terminal families u=0,1 (including potentially further bank phases), the entry bridge, and an invariant connecting every return. No parent count changes on this result alone.

## Complementary 322 counter (checked)

Write G(v,X,R)=DR(62 6^v 7 X,R), and T(n)=(322)^n. For the six C-tails (31,32,315,325,3242,35221), let next advance cyclically and ccarry equal one only at the wrap. Raw14037Counter.lean proves, on the same partial base:

```
G(v,3X,T(n)s) -> G(v+1,X,T(n+ccarry(s))next(s))
G(v,3^k X,T(n)s) -> G(v+k,X,T(n+turn(k,s).1)turn(k,s).2)
G(v,2,T(n)s) -> BL([],2^(v+4) T(n+ccarry(s)+ccarry(next(s)))next(next(s)))
```

The first law factors through the existing 42 counter scan and the new six-bank seed and loop. The second is induction on k, and the third handles the terminal left marker by two further counter rotations. All three are locally kernel-checked with [propext, Quot.sound], no sorryAx. This proves an entire unbounded sweep plus exit, with arbitrary untouched X in the first two laws. The remaining bridges are the finite six-bank terminal tails, the 2-bank-to-D phase and subsequent section return. No machine verdict yet.
