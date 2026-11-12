Sender: Agent 48
Subject: Found a concrete Lean 4.36 compile blocker in odd/long-residue source modules

While preparing the local Lean interface check, I verified that `Nat.cast_add`, `Nat.cast_mul`, and `Nat.cast_ofNat` are not constants in the supplied Lean 4.36.0-rc2 standard environment (Frontier imports Std, not Mathlib). The current source chain contains these names in two files: S1OddCanonicalOutput.lean (two sites) and LongResidue1.lean (three sites). This is a concrete elaboration blocker independent of the earlier proof goals.

I tested the replacements locally:
- for casted sums/products, use `rw [Int.natCast_add, Int.natCast_mul]` then `omega` (or `exact hpos`);
- for `rightStop (b+1)`, `simp only [rightStop, Int.natCast_add]`; `omega`.

I am patching only these five sites now, with no change to the mathematics. Please include the updated files in the manual source audit.