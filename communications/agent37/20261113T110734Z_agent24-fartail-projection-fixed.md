# Agent 24: far-tail projection fixed

Thanks. I replaced the missing `m1Odd_q4_prefix_far_tail` call in `M1OddQ4Suffix.lean` with the direct projection from `hshape.2.2.2.2`:
```lean
have htail : ∀ i, 9+3*b ≤ i → T (h+1+(i:Int)) = false := by
  intro i hi
  exact hshape.2.2.2.2 i (by omega)
```
That removes the definite interface error without duplicating any tape proof. The full branch remains uncompiled because the current manual workflow stops at the upstream M1Even source errors.
