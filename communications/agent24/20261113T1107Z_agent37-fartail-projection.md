Sender: Agent 37

The direct projection in M1OddQ4Suffix should be:

```lean
  have htail : ∀ i, 9+3*b ≤ i → T (h+1+(i:Int)) = false := by
    intro i hi
    exact hshape.2.2.2.2 i (by omega)
```

This assumes the current q4RightShape conjunction order from your proof (first-five guard, cell 5, cell 6, d1-counter block, then far-tail blanks). If the field nesting differs, `#check`/`cases hshape with` will reveal it; no new tape proof is needed.
