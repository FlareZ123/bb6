# Raw39 exact whole-parent bound: 28,311

**28 November 2026 — source-accepted exact weighted bound for one retained Canonical40 parent. BB(6) itself remains open.**

## Theorem

For the six-hole partial machine

```
1RB---_1RC---_0RD---_1LD0RA_------_------
```

the original-source Lean development now proves the complete all-completion parent theorem

```lean
BB6.Agent11Raw39Closed.parent_bound   : Bound 28311 p39
BB6.Agent11Raw39Closed.parent_cover   : Cover (WeightedBound 28311) p39
BB6.Agent11Raw39Closed.parent_exact   : ∀ B, Bound B p39 ↔ 28311 ≤ B
BB6.Agent11Raw39Closed.parent_attained :
  ∃ m k d, compatible p39 m ∧ HaltsAfter m k ∧
    d ∈ delays (zeroNext m) 0 ∧ d+k+1 = 28311
```

Thus 28,311 is the exact weighted threshold of this entire partial-machine cylinder, not merely an observed completion score or a finite search cutoff.

## Final missing child and source acceptance

Ten child branches had already been source-certified. The last local obligation was the A1=1LE child. Recovery run **46114235329** compiled the missing g5b dependency group independently, merged it with the four previously accepted groups, and source-checked

```lean
BB6.Agent11Raw391LE.all1LE : Bound 28311 (child ⟨true,false,4⟩)
```

from 2,490 project modules. Its axiom profile is exactly a subset of `propext`, `Classical.choice`, and `Quot.sound`. The complete 1LE artifact is **15252869930**, zip SHA-256

```
9adb41eeb258b1bdb96a10611bb8efacb82edd6b15d61d3220ab48a6d82d7fed
```

The eleven-child parent join then succeeded in **run 46120215128**, artifact **15253795457**, zip SHA-256

```
f0e5193bfd30cbcb13318cdfb61da3aed8dbee4fb806cf2dfdd92a88f34740f8
```

It authenticated the eleven independent child artifacts, compiled `Raw39CompleteJoin.lean`, printed all six final theorem axiom profiles, and reported:

```
PASS: exact Raw39 parent Bound 28311, source-connected all eleven children
```

Every final theorem above uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Relation to the global frontier

Raw39 is one of the 40 representatives in the currently accepted Canonical40 quotient frontier. Earlier source gates established that it occurs exactly once there and that removing it gives a 39-representative conditional quotient theorem. The new whole-parent Cover supplies the previously missing mathematical premise for making that decrement unconditional.

The separate global consumer still has to authenticate the accepted Canonical40 predecessor and this parent proof in one source-connected build. Until that consumer succeeds, this result is a complete **local parent closure**, not by itself a claim that the accepted global frontier has already fallen from 40 to 39.
