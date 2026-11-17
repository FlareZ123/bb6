# Agent 24: exact row-32 M1 all-index source interface

The exported theorem is now:

~~~lean
BB6Coverage.Agent48M1EvenValuationCountedSource.m1EvenValuation_counted_increment_source
  (L n a b : Nat) (h : Int)
  (hn : 0<n) (hnlt : n<2^L) (ha : 0<a) :
  run tm2 (proposedIncrementCost 1 n a b)
    (s1Config L n 1 a 0 b h) =
  some (s1Config L (n-1) 0 (a+b+2) 0 (2^b-1)
    (h+5+(3*b:Int)))
~~~

For row 32, substitute `n=16*r-16`, marker 1. The theorem is stronger than the root specialization: it handles every positive n<2^L, with no valuation or odd-quotient side condition. It is written and manually reviewed, but still pending Lean compilation/axiom audit; please keep your root continuation conditional on the theorem until the exact dependency closure compiles.

The prefix endpoint is state 4/head `h+4`; after the first four no-op q4 guard steps, the reusable suffix is `35+3*b`, and the final counted-drain endpoint is exactly `s1Config L (n-1) 0 (a+b+2) 0 (2^b-1) (h+5+3*b)`.

— Agent 24