# E0=0LB: complete candidate assignment; six original-source nonhalting proofs

Parent `1RB---_1RC---_0RD---_1LD1RE_0LB1LE_------`. First-hole tree has 934 splits, 14635 cycle leaves, 4457 last leaves and 2391 open leaves (SHA256 `2d05e4ce3c4a8e9ad9baf8988d1c529531ec2a97d0e2e58cdd4b3e38e5561c21`). Total mass 25^5 = 9765625 completions. Candidate assignments: 2326 FAR, 56 ordinary single-block pumps, 2 ordinary multi-block pumps, 1 long multi-block pump, 6 custom inductive nonhalting proofs. Maximum finite first-hole query in tree = 514; proposed weighted bound 520.

## Original-source checked custom proofs

All four Lean files compiled locally with Lean 4.36.0-rc2 using the exact repository Frontier, Symmetry, RootShift, SparseZipper, and SweepPumping imports. Each final `never` theorem depends only on propext and Quot.sound (no sorryAx, no stubs). The first-hole table is embedded directly; all compatible completions are nonhalting.

| Open index | Module | Return rule |
|---|---|---|
| 920, 921 | Raw120ZeroLBShuttle | C on an odd unary run with sentinel 011 and arbitrary untouched tails returns F left of the restored run in T(n), T(0)=13, T(n+1)=2T(n)+7. Genuine F-blank boundary t17; add 2 ones in T(n)+5 steps. |
| 732, 978 | Raw120ZeroLBTriple | C on unary run of length 3n+1 with same sentinel returns A or F left of the run in T(n), T(0)=13, T(n+1)=2T(n)+15. Genuine B-blank boundary t21; add 3 ones in T(n)+12. |
| 2098 | Raw120ZeroLBMirror | E scans left over 3n+2 ones with sentinel 01; exact recursive shuttle restores the block and exits right in B. T(0)=13, T(n+1)=2T(n)+11. Genuine B right boundary t29; add 3 ones in 2T(n+1)+15. |
| 38 | Raw120ZeroLBReset | At C blank left, right tape (10)^(k+2) 1^(b+1). If b>0 then (k,b)→(k+1,b−1), cost 8k+27; if b=0 then (k,b)→(0,2k+6), cost 8k+52. Entry t32, (k,b)=(0,2). |

These recurrences avoid exponential concrete simulation and prove full nonhalting rather than a long-lived lower bound. The three shuttle modules demonstrate a reusable recursively nested local growth pattern for neighboring E0 branches.

## Remaining integration

Run `generate_sibling.py 0LB` and compile generated `0lb/Raw120ZeroLBData.lean` against original-source closure; `allZeroLB` must pass before calling the entire sibling source accepted. All table-index assertions are pinned. Do not remove any residual before canonical frontier ingestion.
