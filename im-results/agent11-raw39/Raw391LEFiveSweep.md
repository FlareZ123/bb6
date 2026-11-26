# Five more 1LE leaves: periodic D-state growth

All five theorems were compiled with Lean 4.36.0-rc2 against the original SweepPumping artifact dependencies; each has only propext and Quot.sound as axioms. The literal tables are encoded in the checked proof source; theorem names are BB6.Agent11Raw391LEFiveSweep.M<id>.never.

At D with the right list empty, let A(a,b) have near-first left list 00 1^a (0011)^b and let B(a,b) have left list 001100 1^a (0011)^b. For the first four variants the observed phase sequence is A(6,b) -> A(8,b+2) -> B(6,b+4) -> A(12,b+6) -> B(8,b+10) -> A(6,b+18). The entire return is checked by explicit arbitrary-tail sweep identities, not by extrapolating the observed phases.

| Leaf | Entry | Family | Increment in block count | Epoch cost for n additional blocks |
|---:|---:|---|---:|---:|
| 7492 | 40 | A(6,1+n) | 18 | 3719+340n |
| 7495 | 42 | A(6,1+n) | 18 | 3739+340n |
| 7527 | 44 | A(6,1+n) | 18 | 3759+340n |
| 7529 | 38 | A(6,1+n) | 18 | 3699+340n |
| 7532 | 174 | A(8,3+n) | 16 | 3972+320n |

The last variant returns to A(8,b+16). For each variant the indexed family is rescaled by 18 or 16 so never_of_growth applies to a unit increment of its parameter. Proofs have 34 arbitrary-repeat sweeps (first four) or 32 (last); all finite computations are kernel reduction with untouched symbolic tails. No assumptions on the tape width.

The exact source is [Raw391LEFiveSweep.lean.xz.b64](Raw391LEFiveSweep.lean.xz.b64). The generator dispatch materializes it and checks SHA256 c69e36b505410b8d7d211a03c4befe1156cf3aada5c7bc7dbc4f65d68b0fb382. It is 209702 bytes decoded. The five normalized leaves are now proved, leaving 21 unclassified 1LE discovery leaves; no complete 1LE child bound is claimed.
