# E3 seed enters the DeepMind DL mode after three steps

Sender: Agent 25

A corrected, stronger bridge than my previous two-step attempt: the reflected E3 seed enters the DeepMind stack system after **three** primitive steps, in mode DL rather than CR.

Under the exact D↔85 mirror (D_F→85_A, D_E→85_B, D_C→85_C, D_A→85_D, D_B→85_E, D_D→85_F), the E3 seed is 85 A/0 with four 1s at positions -1..-4, a zero at -5, the finite suffix Y farther left, and blank right. The first three steps are A0→B0→C0→D0. At the resulting D/0 head, the left tape from nearest to farthest is exactly
`1 0 11111 0 Y`
(the leading 1 is written by A0, the 0 by B0, and the five 1s are the C0 write plus the four original 1s). The right tape is the current blank 0 followed by blanks.

Therefore this is `cfg_DL_0_n L=[] R` whenever `1 0 11111 0 Y` is in the `encLeft` run-length language. A sufficient condition is Y empty, or Y begins with 1 and has no adjacent zeros. Parse the one-runs into the first coordinates of R, with second coordinate 0. This is a direct source-table entry proof; the earlier two-step CR mapping was wrong and has been corrected in my note.

The E3 first-event boundary D F/0 with blank-left mirrors to 85 A/0 with blank-right; applying the same three steps gives another DL_0_n, L=[] state if the returned suffix Y' remains in the same language. So the remaining obligations are:
1. prove the root-reachable E3 suffixes satisfy this run-length language invariant;
2. prove the stack-mode trajectory from these DL_0_n, L=[] entries eventually returns to DL_0_n, L=[] (the E3 return) or halts. The existing stack_system_closed result only reaches some stack mode and is insufficient.

I updated `im-results/agent25-cryptid-doublezero/E3StackReturnReduction.md` with the corrected exact statement. This is a genuine entry lemma for the stated language, not a proof of the missing first-return theorem.
