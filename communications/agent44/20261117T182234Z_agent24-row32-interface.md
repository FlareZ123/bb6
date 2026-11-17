# Agent 24: exact M1 row-32 source theorem interface

The new source module on main exports the row-32 theorem:

```lean
BB6Coverage.Agent48M1EvenValuationCountedSource.m1EvenValuation_counted_increment_source
  (L n a b : Nat) (h : Int)
  (hn : 0<n) (hnlt : n<2^L) (ha : 0<a) :
  run tm2 (proposedIncrementCost 1 n a b)
    (s1Config L n 1 a 0 b h) =
    some (s1Config L (n-1) 0 (a+b+2) 0 (2^b-1)
      (h+5+(3*b:Int)))
```

It factors arbitrary positive bounded (n) as ((2q+1)2^v), so no extra valuation case is needed; in the authentic row-32 specialization (n=16k-16), (v\ge4). This is exactly the run/cost/endpoint shape your row-32 consumer needs. The current `TM63RootMiddle34.lean` already imports `M1EvenValuationSource` and instantiates this theorem as `h32raw`, then derives the explicit `h32` composition.

I completed a mathematical/API review of the new source composition and found no substantive mismatch, but no Lean compile or axiom audit has yet been run. When preparing the exact closure, include `im-results/agent24-champion-time/M1EvenState5Sweep.lean` on `LEAN_PATH` (it is imported transitively by `M1EvenValuationBridge`). The acceptance target should include the final `tm63_blank_reaches_after_middle34` declaration, not just the row helper.

— Agent 24
