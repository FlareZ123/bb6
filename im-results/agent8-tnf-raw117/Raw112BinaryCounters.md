# Raw112 two exact binary-counter candidates

The raw112 parent is `1RB---_1RC---_0RD---_1LD1RE_---1LC_------`, with 25^6 completions. The later `raw112_checkpoint.py` (rather than the stale README) specifies 13,011 FAR candidates, 215 one-/two-block candidates, 6 late queries, and 34 remaining leaves. Reproduced the original open enumeration SHA-256 `61773d08354491c09508929b83a5090b564b7808e7dabf6b045d353c9ea2bf01`. None of the 34 queried its undefined row in the 10,000,000-step probe (finite evidence only).

Two of the 34 now have universal exact zipper inductions:

* 10554: `1RB0LF_1RC---_0RD1RA_1LD1RE_0RC1LC_0RA0LA`. At t=12, A scans zero with left word 00 and right word 001. At epoch n the right word is 00(0000)^n1. An arbitrary-tail carry crosses one four-cell digit at cost 22; a zero digit resets the preceding j digits at cost 4j+12. The finite low-order-block traversal has cost T(0)=0, T(n+1)=2T(n)+4n+34. Thus the epoch n→n+1 costs exactly 38·2^n.
* 12597: `1RB0RB_1RC---_0RD1RF_1LD1RE_0RA1LC_1LE0LF`. At t=59, E scans zero with left word 010100 and empty right word. At epoch n the left word is 0(10110)^n10100. An arbitrary-tail five-cell carry uses 5 steps, and a zero resets j earlier interior blocks at cost 13j+27. The low-order traversal cost T(0)=17, T(n+1)=2T(n)+13n+32. Epoch n→n+1 costs exactly 62·2^n−11.

Both exact entry, universal macro rules, arbitrary-tail inductions, cost formulas and growth theorems compile locally under Lean 4.36.0-rc2 against copied executable `Z0`, `move0`, `step0`, `run0`, `join0`, `rep`, `rep_snoc` from SweepPumping, using the matching slot/Move structure. Growth and fullCarry depend only on propext and Quot.sound. The final `never_of_growth` applications are included in the source modules but require the actual original-source import chain audit. Neither complete parent closure nor global roster reduction is claimed.

For the future full audit, map 10554 to `BB6.Agent8Raw112Binary.table/never`, 12597 to `BB6.Agent8Raw112Quinary.table/never`; retain the other 32 leaves in REMAIN. The checkpoint script intentionally remains unchanged as its historical ID-partition replay. Source CI dispatch is not available through the current connector, so no new workflow was added.
