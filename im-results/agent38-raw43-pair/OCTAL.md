# Raw43: an exact octal counter proves four hard one-hole cylinders nonhalting

The six residual literal tables in Agent25's spec_b1la_a0la.json include M110/M202 and M151/M243, related by E/F renaming and the exact stuttering coupling in Raw43Pair.lean. Raw43Octal.lean now proves unbounded ordinary live prefixes, for every compatible completion of each of those four partial tables. Parameters (v,s) = (false,false), (false,true), (true,false), (true,true) select 110,202,151,243 respectively.

## Structure

Use the repository's zipper convention (left includes scanned cell, both lists padded with zero). At a frontier A with empty left list, right word is 0^8 (1100)^k L_r U, where L_r is one of 16 low-phase words (18 cells for even r, 20 for odd r) and U is a little-endian list of 16-cell octal digit words. The low phase increments r and adds one periodic block on odd r. At phase 15 the higher word increments in base 8. Each leading seven adds 16 ones to a carry run; the first digit <7 is incremented and the unary carry run is erased into 16 zero cells per skipped digit.

Digit words:
0 0000000000000000
1 1101111000000000
2 0000001100000000
3 1101100000011110
4 0000000011000011
5 1101111011000011
6 0000001111000011
7 1101100001100011

The 15 low-phase transitions and 7 terminating carry transitions are literal finite equalities for arbitrary untouched tails (rfl); arbitrary periodic prefix and carry length are proven by induction. The theorem epochs uses N reserved zero digits, enough for N positive-cost frontier epochs from any valid phase/digit word. The start word for phase 0 is all zeros, exactly the original infinite blank tape under embed. The padded_live and never theorems transport through run_project, zrun_sound, and raw run_append. No finite simulation cutoff enters the proof.

## Verification and integration

Local Lean 4.36.0-rc2 checked Raw43Pair.lean and Raw43Octal.lean against a reconstructed **relevant source excerpt closure** of Frontier, RootShift, SparseZipper and SweepPumping (the original raw semantics, zipper embedding and transport lemmas, with unrelated declarations omitted). The theorem BB6.Agent38Raw43Octal.never reports [propext, Classical.choice, Quot.sound]. Full repository module closure and literal residual-list equality linkage are still pending; do not count this as an accepted Canonical57 Cover until that linkage is checked. M355/M377 remain independent. Files are intentionally in im-results pending source integration.

Expected module path additions: im-results/agent38-raw43-pair (Raw43Pair and Raw43Octal), plus existing SweepPumping dependency directory im-results/agent31-three-hole-tnf. Both files have unique namespaces.
