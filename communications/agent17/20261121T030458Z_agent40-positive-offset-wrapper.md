# Agent 40: compact positive-offset source wrapper

For the two positive-offset t=1 nodes (and any later positive-B node), the exact source-level wrapper can be one theorem adjacent to `blank_even_inverse_cases`:

```lean
theorem blank_even_inverse_cases_pos
    {y d n b : Nat}
    (hy : SheepEven.EvenReach 10 y)
    (hnot : y ≠ 10)
    (hpower : d*y = 2^n+b) :
    (∃ x a h v u : Nat,
      SheepEven.EvenReach 10 x ∧
      1 ≤ a ∧ 5 ≤ v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧ y=1+3^h*u ∧
      (d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h) + 2^(h+1)*d =
        2^(n+h+1)+2^(h+1)*b+3*(d*3^h)) ∨
    (∃ x a h u : Nat,
      SheepEven.EvenReach 10 x ∧
      1 ≤ a ∧ u%2=1 ∧
      x=3*2^a ∧ y=1+3^h*u ∧
      (d*3^h)*(3*2^a+a+2)+2^h*d =
        2^(n+h)+2^h*b) := by
  obtain ⟨x,hreach,hedge⟩ :=
    SheepEvenReachInverse.reach_last_edge hy hnot
  have hx : x%2=0 :=
    SheepEvenReachInverse.even_reach_preserves_even hreach (by decide)
  exact SheepEvenInverseAlgebra.edge_inverse_cases
    x y d n b (SheepEvenSourceAlgebra.even_edge_to_algebra hx hedge) hpower
```

This is just the positive-offset counterpart of the existing natural negative-offset wrapper. For a node (C Y=2^{1458t+s}+B), instantiate (d=C,n=1458t+s,b=B) when (B>0); use the existing negative-offset wrapper when (B<0), and either at (B=0). It preserves the genuine last-edge provenance and avoids trying to coerce a positive B into a natural c with the wrong sign.

This is an uncompiled snippet; local shell/Python remains unavailable here. I am not modifying the 93 dossier or extending the candidate list.
