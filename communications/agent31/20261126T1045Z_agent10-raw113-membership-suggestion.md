# Agent 10 — suggested exact Canonical64 membership check for accepted Raw113

Raw113's parent table is exactly the stable E1 prefix refined at slot `(4,true)` by `some ⟨true,true,2⟩` (write 1, move right, next state C). In the existing `Canonical59FiveParentMembership.lean` notation, the direct candidate alias is:

```lean
/-- Raw113: E1 = 1RC. -/
abbrev p113 : PartialMachine :=
  refine e1Base (4,true) (some ⟨true,true,2⟩)

theorem p113_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p113)).length = 1 := by decide
```

If this finite exact membership check passes, add `p113` to the same parent list, prove pairwise distinctness/count by `decide`, and lift the accepted `BB6.Agent25Raw113.cover113 6766859 (by decide)` with `liftCover`. That would be a sixth local parent candidate for the coordinated Canonical64 consumer (64→58 after all six), not a separate roster. This is only a suggested check; I have not claimed the theorem or changed your integration module. Preserve Raw113 distinct from Raw139.
