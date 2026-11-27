# Crossing-splice certificate bank: 23 Raw40 leaves

See [the splicing lemma and worked leaf 156](README.md). This bank applies it to 23 literal A1=0LA residuals: 20 in C1=1RB, two in C1=0RD and the previous C1=1LA leaf 156. With the five separate side-cycle witnesses, 28 distinct residuals have mathematical nonhalting certificates; only 1LC/66 and 0RD/154 remain in the targeted 30-leaf snapshot, pending reconciliation with current banks.

## General certificate

Run from blank for entry moves to A scanning blank at entryHead, all tape on and left of the head blank. Translate head to 0 and replay period moves to A at shift, with tape on and left blank. Each cut (a,b] lies strictly to the right of both heads, and the chronological crossing lists at a and b agree. Intervals are disjoint (adjacent allowed). The splicing lemma yields a computation on the start tape with every interval duplicated n times, ending on the correspondingly expanded finish tape, in period+increment*n moves.

For right word w, let P_w(n) denote the expansion by n additional copies. This has alternating constants and block^n terms. To derive the finish expression, subtract the final head from every cut coordinate. The checker proves P_start(n+1)=P_finish(n) for all n by literal equality after normalizing the two formal expressions. Normalization uses x(Vx)^n=(xV)^n x, shifting a variable power left across an adjacent constant character when it equals the block's last character; rotate the block and move that character to the following constant. This is an identity of words for all n, including zero, by induction. Other operations simply assemble constants and explicit extra copies. Equality of normalized tuples proves the required word identity with no finite extrapolation.

Let C(n,h) denote A scanning blank at h, left blank, right word P_start(n). The splice lemma yields C(n,h) -> C(n+1,h+shift) for every natural n, taking period+increment*n moves. Blank entry reaches C(0,entryHead). Every move is assigned, so all completions have arbitrarily long live prefixes. Mathematical proof plus exact finite-premise checks; the general Lean splice theorem is not yet available.

## Reproduction

Run python check_bank.py (without -O). No external packages. bank.json records literal tables, entry and head, period, shift, cuts and increment. The 22 new entries passed locally; the worked 1LA-156 entry passed its dedicated checker. No original-source Lean acceptance, completed Cover or global roster decrement is asserted.
