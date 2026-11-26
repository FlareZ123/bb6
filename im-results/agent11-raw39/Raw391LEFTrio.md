# Raw39 1LE leaves 5774, 5781, 5789 — common four-sweep growth

All three literal partial tables share the same F1 return family, with only C1 undefined.

| Variant | Normalized leaf | F1 move | Exact return cost |
| --- | ---: | --- | --- |
| a | 5774 | 0LE | 467 + 48 n |
| b | 5781 | 1LA | 473 + 48 n |
| c | 5789 | 1RE | 469 + 48 n |

At step 727 the blank trajectory enters state F with the current cell included in the near-first left list. The family at arbitrary n is
`F(10101000 (11100)^n 1110011100111110011, 0 (110)^n 11)`.
The next epoch increases both repetition counts by one. The variant-dependent fixed first phase takes 43,49,45 steps, respectively. The four arbitrary-tail block transfer phases are left 11100 -> 11000 (15n), right 11000 -> 10011 (9n), left 10011 -> 00110 (15n), right 00110 -> 10011 (9n). Fixed phases between/after them cost 170,33,179,42. The final literal list re-cut is proved using moveCut, and exact blank entry and every fixed/local segment are checked by kernel reduction.

`BB6.Agent11Raw391LEFTrio.never` proves NeverHalts for every compatible total completion for every variant. Local compilation on Lean 4.36.0-rc2 against the original artifact-linked SweepPumping dependency succeeded; axioms only propext and Quot.sound. Source SHA256 19b714c6c3bda5744acaea3dbd3ca8833d066cdaa6c1481411d70a14c8837dd1. The bits! macro expands string literals into ordinary literal Boolean lists at elaboration; no executable trust or native_decide enters the proof.

This closes three of the 36 previously remaining 1LE discovery holdouts (now 33). No complete 1LE or Raw39 parent Cover yet.
