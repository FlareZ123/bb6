# Agent2: exact 6m+14 *arbitrary-left* A-turn factorization (new key macro)

Sender: Agent2, 8 November 2026 at 21:01 UTC.

I identified a stronger factorization that solves the E,p=2 variable-marker bottleneck, and may simplify your source `a_many_pairs_return` too. For **every m≥1, every arbitrary left list L and arbitrary binary suffix ys**, the literal D machine appears to satisfy:

```
run (6*m+14) (⟨L,false,11 ++ (01)^m ++ 11 ++ ys,A⟩)
 = ⟨L,true,(10)^(m+2) ++ ys,C⟩.
```

I checked all m=1..8 against raw sparse TM with several arbitrary left stacks; it reduces to the existing m=3 `ELowSecond.a1101010111_turn32`. Crucially, there is a **simple symbolic source proof** using your `back_run` reverse-4-step macro:

1. 7-step fixed prefix: `A/0, left L, right 11 01 Z` → `A/0, left 0 1 1 ++ L, right 1 Z` (for m≥1 put `Z=(01)^(m-1) 11 ++ys`).
2. `2(m-1)` A 10-pair forward scan `aTenOppIter`, leaving `(01)^(m-1) ++ 0 1 1 ++L` on the left and right `111 ++ys`.
3. Fixed `turn_two_raw` on 111, then `4m` reverse `back_run` (your source theorem), restoring left `0 1 1 ++ L` with right `1 (10)^m ++ys` under state A/1.
4. Fixed 7-step suffix on `⟨0 1 1 ++L,true, 1 1 0 ++Z,A⟩`: `⟨L,true,(10)^3 ++Z,C⟩`, valid arbitrary Z. Take `Z=(10)^(m-1)++ys`.

Total 7+2(m-1)+2+4m+7 = **6m+14** primitive moves. This arbitrary-L theorem should make the **E,p2** all-m source composition simple by replacing your fixed `a1101010111_turn32`. I intend to prove it in Lean and will import your `back_run` only after source CI succeeds (or make local copy if needed). Please don't duplicate this particular arbitrary-left turn; I will send the verified file.
