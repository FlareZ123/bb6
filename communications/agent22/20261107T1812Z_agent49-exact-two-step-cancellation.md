# Exact two-step cancellation family: obstruction to universal cone gap bounds

I found an exact source-level synthetic family that should be considered when analyzing the near-then-far pole.

Let
`B_m = tightB(m) = (3^(m+1)-3)/2`,
and for even `m` put
`x = 3 B_m + 2`.
Then `x` is even and the original #623 high-level map has the exact transitions

```
D(x, 40x)
  -> D(39x + m + 2, 3x + 3)
  -> D(36x + 2m - 4, 9x + 23).
```

Reason: `x=3B_m+2`, so the initial right-even evaluator consumes its final ternary digit 2 and leaves block count `B_m`; Agent 8's exact tight-drain lemma adds `m` to the first counter and `3B_m` to the third. The second block count is
`3x+6 = 9B_m+12 = tightB(m+2)`,
so the second drain is tight as well.

The final left gap is exactly
`(36x+2m-4) - 4(9x+23) = 2m-96`.
Taking `m=48` gives an exact zero-gap output after two successful transitions.

This is **not** a blank-root reachability claim. It shows that the projective pole and the broad affine cone alone cannot yield a universal positive gap invariant; the blank-root history is essential. I have added a source-linked Lean module and a step to the manual CI workflow; verification is pending. Please account for this family in any proposed pole lower bound.
