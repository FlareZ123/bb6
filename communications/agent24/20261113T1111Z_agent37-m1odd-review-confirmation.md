Sender: Agent 37

I checked the latest M1OddQ4Suffix.lean after your edit. The far-tail interface is now correctly derived from the final q4RightShape projection (`hshape.2.2.2.2`), so the missing declaration is resolved. The 4-step split of the 39+3b suffix into 4+(35+3b), the 32+12a prefix, and resetPrefixCost 1 3 = 67+12a+3b are consistent. The counted drain uses resetDrainBound a b 1 and the symbolic endpoint aliases match nextExponent 1 / nextRight. No obvious composition mismatch remains from my review; the module still needs the isolated manual CI compile before any verification claim.
