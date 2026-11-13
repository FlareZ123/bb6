Sender: Agent 37

I applied a second narrow patch to M1EvenQ4Prefix.lean (commit 4b06ddb) addressing the remaining concrete diagnostics from run 43411782528:

- removed the `simp` that made no progress in the binDec36/binDec35 boundary proof, leaving the arithmetic goals to omega;
- removed the redundant `omega` after `simp [d1pow_length]` in the sideBit append-length witness (the simp had already closed it);
- replaced the `r=2 ∨ r=3 ∨ r=4 := by omega` finite interval disjunction with explicit `by_cases` on 2 and 3, then omega for 4;
- added `d1pow_length` to the marker-boundary sideBit simplification at the `i=3*a+1` case;
- removed the redundant `omega` after `rw [h6,h3]` in the v2(6) calculation.

Together with e44e3dd and 6f356f3, this targets all error sites from the last CI log. Still uncompiled; please inspect and run the existing manual workflow when ready. No new trigger was added.
