# Raw10 base34 rectangle 11

The exact source domain is matched by [Box11Core.lean](Box11Core.lean), checked locally in Lean 4.36.0-rc2 with the accepted Box6 dependency artifact and the Agent48 packed certificate infrastructure.

Fixed codes: [8,25,11,25,17,13,11,25,25,25,25,25], with holes denoted by 25. B1 has the 20 values [0,1,2,3,4,8,10,12,13,14,15,16,17,18,19,20,21,22,23,24]; E0 has 11 values [0,2,3,4,12,18,20,21,22,23,24]. All other holes have 25 choices. Total mass 20*11*25^5 = 2,148,437,500.

**Proved:** the E0=halt subrectangle of 195,312,500 tables has weighted bound 11, since the fixed authentic prefix reaches E0 after five ordinary moves. The exact source-index match and source-restricted bound have standard axioms only. The other ten E0 branches remain unclosed.

## Certificate lifting from the complete Box12 sibling

Instead of rediscovering all certificates, free the fixed B1 row in the existing Box12 tree. Its partition remains valid as a decomposition by the other slots. At every leaf recheck its witness under the weaker assignment; if that fails, recheck it under each permitted B1 assignment. Retain only failed subchecks. A missing child or exhausted recursion fuel is retained rather than dropped.

[TreeLift.lean](TreeLift.lean) proves this generic residual-emitting checker sound for arbitrary input trees, including incomplete ones. [Box11Lift.lean](Box11Lift.lean) links it to the exact source rectangle and proves a weighted bound B+5 conditional on DecidedBelow B for every compatible emitted residual. Both exported theorems compiled locally against the exact extracted Box12 and accepted Box6 dependencies, with axioms [propext, Classical.choice, Quot.sound] only. No external solver output is trusted.

The following is the native Lean evaluation of the lifted Box12 witness trees at B=200, with disjoint cylinders inherited from the original first-hole partition (not a kernel-checked numerical census):

| E0 | Residual cylinders | Residual mass |
|---:|---:|---:|
| 0 | 0 | 0 |
| 2 (new, no sibling tree) | 1 | 195,312,500 |
| 3 | 20 | 195,312,500 |
| 4 | 257,295 | 188,274,975 |
| 12 | 55,040 | 31,644,200 |
| 18 | 65,127 | 35,863,575 |
| 20 | 248,092 | 64,230,100 |
| 21 | 58,743 | 14,836,575 |
| 22 | 107,324 | 41,616,500 |
| 23 | 80,356 | 36,682,300 |
| 24 | 313,757 | 62,251,325 |
| Total | 1,185,755 | 866,024,550 |

The computed complement has mass 1,282,412,950, about 59.7% of Box11. The actual theorem uses the computed residual list, not the reported mass; no complete weighted bound on Box11 or global frontier reduction is claimed.

Reproduction: recover the frozen Box12 source/object bundle via [recover-join.py](../agent48-raw10-box12/recover-join.py), copy Box11Core.lean, TreeLift.lean and Box11Lift.lean to its work directory, compile in that order using the same Lean and LEAN_PATH as the recovery, then run `python lift-box12.py --work <work>`. Compile the generated LiftE*.lean files; they each print their residual count and mass. The generator reconstructs split nodes from the original theorem source while reusing the accepted leaf-tree definitions. The proof is independent of generator correctness.
