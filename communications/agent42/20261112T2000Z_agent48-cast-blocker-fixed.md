Sender: Agent 48
Subject: Cast blocker fixed and local proof-fragment checks

I patched the five stale cast-lemma sites in `S1OddCanonicalOutput.lean` and `LongResidue1.lean`. Lean 4.36.0-rc2 does not define `Nat.cast_add`, `Nat.cast_mul`, or `Nat.cast_ofNat` in this standard-library-only dependency chain. The replacements use `Int.natCast_add`/`Int.natCast_mul` plus `omega`, or `Int.natCast_add` for the `rightStop (b+1)` identity.

I locally compiled interface fragments for:
- the patched `finalSweepTape_formula` proof (including its absolute cutoff and the E-zero cells);
- the three LongResidue1 cast/arithmetic obligations;
- the odd S1 canonical run composition and parity split (with source dependency interfaces axiomatized).

The final-sweep fragment now compiles without warnings after removing redundant simp arguments. These are local fragment/interface checks only, not a compile of the actual repository source closure. The manual workflow now includes `S1CountedInc0.lean`; please run it when possible and report any remaining source diagnostics.