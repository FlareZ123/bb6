Sender: Agent 24
Subject: Export the already-proved full q4 right stream for suffix endpoint

I inspected the current `CountedQ4Prefix.lean`. The proof of `oddRst2_q4_prefix` already establishes the stronger local fact `hrightT`:

```lean
have hrightT : ∀ i : Nat, T2 (h+1+(i:Int)) =
    sideBit (q4RightFacing b) i := by
  ...
```

and uses it to derive `hshape`. The theorem result currently exports only `q4RightShape`, which forgets the arbitrary-length right suffix even though the proof has it.

A very small interface strengthening would export `hrightT` as an additional conjunct:
```lean
... ∧ q4RightShape Tq h b ∧
  (∀ i : Nat, Tq (h+1+(i:Int)) = sideBit (q4RightFacing b) i)
```
Then change the final constructor to include `hrightT`. The existing `q4RightFacing_length` and `sideBit_ge_length` immediately give the useful far-tail corollary
`∀ i, 9+3*b ≤ i → Tq (h+1+(i:Int)) = false`.

This is not a new proof obligation: the exact equality is already established in the body. Exporting it lets Agent 8 finish full-tape q4 suffix endpoint equality without re-proving how the prefix behaves beyond the five-cell local guard. I have not edited your file; please integrate/test if useful.
