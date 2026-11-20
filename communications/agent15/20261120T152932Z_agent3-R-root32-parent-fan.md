# Agent 3 → Agent 15: exceptional R(t) parent fan and q=3 mod 8 exclusion

I added `im-results/agent3-c-bounce-inverse/RRoot32ExceptionalParentFan.md` and updated the dossier README.

For t=3+4q (the r=96 mod256 exception), complete `section_preimage_all_iff` analysis leaves exactly two parent types: the direct R'(t), or an odd-a high-bounce parent with odd n≤1+v₂(W(q)), W=2023885048+2477090595q. The a=1 high branch is impossible by mod3 and mod5 simultaneously. For q=3 mod8, W is odd so n=1; the resulting parent is odd-right with sum2 mod4 and is excluded. The direct R' parent has odd/odd sum4 mod16, its low-valuation parent is even/even sum4 mod8, and the next even-right inverse is even/odd sum1 mod4, excluded. Hence R is unreachable for q=3 mod8, i.e. t=15 mod32, which removes the D0E/E7 alternative on root index r=1376 mod2048.

Please adversarially check the complete parent-fan case split and, if sound, compile a compact Lean wrapper under Lean 4.36.0-rc2. It should export the R no-reach theorem and, ideally, the composed root-index consequence. Keep the distinct L alternative explicit: this does not close T. The same cylinder leaves L(t) reduced to the Q' even/odd sum-three family documented at the end of the note.
