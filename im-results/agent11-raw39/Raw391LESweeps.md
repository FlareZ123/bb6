# Raw39 1LE seven further sweep closures

All seven partial tables differ only in F1, with C1 undefined. These are exact unbounded growth certificates, not simulation classifications.

| Leaf | Module | State | Entry | Cost of return n to n+1 |
| ---: | --- | --- | ---: | --- |
| 5773 | Raw391LEDFour | D | 332 | 439 + 116n |
| 5783 | Raw391LEDFour | D | 332 | 437 + 114n |
| 5776 | Raw391LEDFour | D | 332 | 425 + 98n |
| 5782 | Raw391LEDFour | D | 332 | 427 + 100n |
| 5785 | Raw391LEFMore | F | 789 | 1096 + 192n |
| 5775 | Raw391LEFMore | F | 3087 | 1448 + 192n |
| 5788 | Raw391LEFMore | F | 3133 | 1494 + 192n |

The first four families have an empty right list and two adjacent repeated left blocks:
`00110011 I^n (11100)^n 11100111110011`, where I=111000 for 5773/5783, I=101000 for 5776/5782. The other three grow a ten-bit repeated word in the left list and a six-bit repeated word in the right list. The exact families and all phase equations are in the proof sources. Each proof is constructed using arbitrary-tail local equations, sweepL/sweepR induction, and list cut rotations; never_of_growth transfers the result to every compatible complete original machine.

Both modules compiled locally with Lean 4.36.0-rc2 against the exact original SweepPumping artifact dependencies. All seven named never theorems have only propext and Quot.sound as axioms. Each theorem's namespace is BB6.Agent11Raw391LEDFour.M<leaf>.never or BB6.Agent11Raw391LEFMore.M<leaf>.never. Matching .table declarations are defined alongside them.

Use `python unpack_le_sweeps.py <Lean-module-directory>` to materialize the two exact source files from the compact checked archive; it checks both decoded module SHA256s. Compile with LEAN_PATH pointing at the original source dependency closure.

Together with Raw391LEFTrio, ten of the thirteen original F1 siblings are now proved. Three remain: 5777,5779,5787. The 1LE discovery residual is 26. Full child coverage remains pending.
