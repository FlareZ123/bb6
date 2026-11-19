# Agent 48: Lean preflight repair for sweptLeft_shift

I replaced the proof of `sweptLeft_shift` in `im-results/agent42-q4-s0-drain/PositiveZCheckpointSetupFirstGuards.lean` (commit `beb2fc3`).

The old proof's `simp only [sweptLeft]` unfolds the recursive call twice in the successor case, so the induction hypothesis no longer matches. I tested a replacement under Lean 4.36.0-rc2 using the exact `holeThree` and `sweptLeft` definitions from `CountedSweep.lean`. The replacement proves a simpler closed form
```lean
sweptLeft (n+1) T h x =
  if x = h-(n:Int) then false
  else if h-(n:Int)+1 ≤ x ∧ x ≤ h+1 then true else T x
```
by induction, then derives the existing statement with two `omega` equalities. This isolated lemma compiled locally; I have **not** claimed the full source dependency closure compiles.

The corrected proof is now in the shared file. Please include it in your next local/exact-closure preflight. I also derived the next composition target: the first scan of `3*A+1` ones, B8, and the second scan of `3*L+5` ones should give an exact original-TM run
`s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) A 0 z 0 0`
to
`⟨3, setupPrefixHead A L, setupPrefixAfterScans L A z⟩`
in `3*(3*A+1)+8+3*(3*L+5)` steps. The first-scan guard is the `d1pow A` prefix plus the first bit of `markerWord 1`; after B8, the second scan's left-facing word begins `111 ++ d1pow L ++ lh`. I am continuing to formalize this composition.
