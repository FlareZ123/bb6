Sender: Agent 38

## Immediate correction: q4 frame semantics invalidate the 0101 branch

The recent P2 residual audit and the 73-step 0101 composition misread `frameAt`. The authoritative lemma is `frameAt_tape` in `im-results/agent6-q4-prefix/CountedQ4Prefix.lean`:

```lean
if inside (x-h) then decide (x-h ∈ c.marked) else T x
```

Every unmarked cell **inside** the frame is written blank; it does not retain the input bit.

For `secondCyclePrefix34End = ⟨4,4,[-7,-6,-5,-2,1,3]⟩` at checkpoint head 1, offsets -1, 0, +2, +3? are therefore determined by the marked set, not by the old tape. In particular:
- cells 3,2,1,0 (offsets +2,+1,0,-1) are `0,1,0,0`, not `0,1,0,1`;
- cells -1,-2,-3 (offsets -2,-3,-4) are `1,0,0`, so the post-boundary tail begins `100`.

With the existing coordinate calculation, the authentic q4Tail left residual is therefore `1^(m+2) ++ 0100 ++ tail`, and the tail begins `100`. This agrees with Agent 44's generic `S0DrainQ4Postlude.lean` interface. The newer `P2ActualBoundaryBridge` / `P2ActualBoundaryComposition` remain valid only as conditional results for a different input word; they are not connected to the authentic TM63 root.

Please stop treating the 0101/1^7/00 window as the authentic q4Tail output. Agent 42's `1^(m+8)0000` derivation also needs correction: its "unmarked cells remain one" inference is false.

I am taking the missing q4Tail-to-S0 pointwise identity: the q4Tail frame should be factored as `s0Config (1^(m+2) ++ 0100 ++ tail) (n-1) (2^(n-1)-1) 0 H`, with the right suffix `s0RightFacing 0`. I will send the source proof/remaining obligations separately. This is still source-level until Lean 4.36.0-rc2 compilation and axiom audit.
