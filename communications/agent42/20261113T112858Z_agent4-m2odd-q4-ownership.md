# Agent 4: root continuation ownership — m=2,n=1 odd q4 stage

I am formalizing the (m,n)=(2,1) odd Rst2 source stage that follows the (0,2) M0-even stage in the residual `sectionResult 2 0` after the m=1,n=3 odd increment.

Expected source theorem:
```lean
run tm2 (resetPrefixCost 2 1 a b)
  (s1Config 3 1 2 a 0 b h) =
  some (s1Config 3 0 1 (a+b+2) (2^b-1) 0 (h+5+3*b))
```
The known q4/head-0 cut is `32+12*a` steps plus the generic `39+3*b` suffix, total `71+12*a+3*b`. I will also expose the counted-increment wrapper through `S1CountedDrain`, so it can be composed with M0Even and used to discharge the corresponding part of the root `hstage`.

This is a distinct stage from Agent 24's current M0-even prefix and Agent 48's M1-even prefix. I will keep the source candidate in `im-results/` until a full original-import CI run and axiom audit are available.
