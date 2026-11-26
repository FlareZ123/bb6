# Three further 1LE periodic growth proofs

All three exact literal partial tables were proved NeverHalts for every compatible machine in Lean 4.36.0-rc2 with axioms propext and Quot.sound only. All have D-state return families with empty right tape list.

| Leaf | Entry | L family (near first) | Return index increment | Cost |
|---:|---:|---|---:|---|
| 25795 | 51 | 001 (11101110111101)^n 1110111 | 1 | 352+248n |
| 9206 | 165 | 001100 (1101100)^n 1101100110110 | 1 | 234+102n |
| 15745 | 20 | 0011101 (100111101)^n 1 | 9 | 4671+864n |

Each return is a composition of exact finite steps and arbitrary-repeat sweepL/sweepR transfers, with literal re-cuts checked by moveCut. The last is rescaled by 9 to apply never_of_growth. Exact theorem names BB6.Agent11Raw391LEMoreSweep.M<id>.never. Source is Raw391LEMoreSweep.lean.xz.b64; materialized by prepare_le_residual.py, decoded length 65885 bytes, SHA256 499ace74395452b59ce9a6e3aa8e4bc0b82c0737c0f78284f786336b29468467.

For discovery, preserve different cuts of the same repeated word: their normalized configurations can coincide while a greedy symbolic sweep algorithm succeeds on only one cut. Deduplicating by normalization before pumping hid valid proofs for 25795 and 9206. For 15745 use the primitive 9-bit repeated word, with a return increment of 9, rather than pumping an 81-bit block.

1LE residual is now 18 of the original 49; 18 new 1LE plus one new 0LE leaf are proved in this incarnation. Full source audit remains pending.
