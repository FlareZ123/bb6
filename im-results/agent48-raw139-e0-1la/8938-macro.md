# Raw139 OneLA leaf 8938: exact macro reduction (still open)

Table [7,8,11,21,14,13,17,16,2,11,19,24], only F1 unspecified.
At step 2 blank run reaches C with nearest-first L=011, R empty.
The exact C-to-C rules on arbitrary untouched exterior tails are:

```
00 0 -> 010 _ 3
00 1 -> 110 _ 3
011 _ -> 01 1 3
1 010 -> 0100 _ 3
1 011 -> 1100 _ 3
01010 _ -> 0 0101 4
01011 _ -> 1 0101 4
110 1 -> 0 010 4
111 1 -> 1 010 4
1 001 -> F1 query after 5
0100 0 -> 01101 _ 7
0100 1 -> 11101 _ 7
1 00010 -> 011010 _ 7
1 00011 -> 111010 _ 7
10 110 -> 01101 _ 7
10 111 -> 11101 _ 7
1 0000 -> 010 01 8
10 10 -> 01 01 8
```

Decode OneLAMacro8938.lean.zlib.b64 with base64.b64decode and zlib.decompress (SHA256 273727af88c0a20df25e077e709bdba81ee8982471522b43967fa2b58972e1b7).
Compiled locally using Lean 4.36.0-rc2 and the accepted core and growth artifacts:
- rule_exact (arbitrary tails, not sampled lengths)
- rule_total (all padded input pairs)
- never_of_macro_invariant (initial, zero-padding closure, and safe macro closure imply NeverHalts for every compatible completion).

All three use only propext and/or Quot.sound. This is a reduction, **not** a nonhalting certificate for 8938.

Search notes: ngrams/asymmetric widths, rungrams, block-FAR widths 2–12, exact macro BiDFA and macro FAR with context and phase features, forward/backward regular-language saturation and negative-language-guided state merging, and two-sided finite automata SAT synthesis have not yet found an invariant. SAT timeouts are not impossibility proofs. 10M primitive steps observed at most two internal 00 pairs in the right tape, within 12 cells of head at C; not inductively established. Avoid treating it as a proof. A useful candidate invariant may preserve correlations across the separator rather than independent stack factors.
