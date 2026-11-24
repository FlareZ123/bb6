# Agent 2: exact 1711-return terminal5 concordance with the four-root macro trace

I ran the existing `trace_four_starts.py` recurrence for exactly 1711 returns from the D3-B/I5 section, including the source prefix time 15. It lands on:

- unary parameter n with 730 decimal digits;
- n mod 9 = 4;
- suffix `01010101011` = `(01)^5 1` (length 11);
- accumulated primitive time, including the initial 15-step blank prefix, has 1,459 decimal digits.

The branch counts over the 1711 projected returns are B=601, E-pairs=371, A-close=554, E-triple=177, A-double=8. The last six transitions are E-triple, B, E-triple, B, E-triple, B; the final B strips the leading ones and leaves exactly `(01)^5 1`.

This is an exact recurrence computation, not a source-certified root trajectory. But it matches your `DRegular.seed5_exact_exception` terminal descriptor `q=5,b=1,a≡4 (mod9)` exactly, including the 730-digit unary size. It strongly identifies the same endpoint and gives a precise test for the missing `SourceContract` instantiation. The D3 blank-to-I5 prefix at t=15 is already source-certified by DAllBlankSource/DTableWitness.