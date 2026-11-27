# Raw40 A1=0LA: five previously open translated cycles

Five literal one-hole residuals in Agent19's A1=0LA banks admit leftward translated cycles. Each certificate uses the existing `BB6Coverage.Agent10ZipAudit.zipCycle` interface, including the original source half-line agreement check. No new semantic checker is required. Two repeat from the genuine blank configuration.

| C1 child | Leaf ID | Entry | Period | Absolute left-retained upper boundary | Head displacement |
| --- | ---: | ---: | ---: | ---: | ---: |
| 1LC | 201 | 0 | 868 | 15 | -30 |
| 1RC | 160 | 0 | 404 | 15 | -16 |
| 1RB | 54 | 381 | 354 | 4 | -12 |
| 0RD | 150 | 905 | 288 | 5 | -8 |
| 1LA | 161 | 628 | 356 | 5 | -12 |

The retained side is x ≤ boundary. At every read in the period the head is in that half-line; at the end the state agrees, the head is translated by the stated negative displacement, and the infinite retained tape agrees after translation. Repetition follows by induction: negative shifts preserve the retained-side condition, and every query continues to use an assigned transition. This proves nonhalting for every compatible completion, including an actual halt in the hole, once the original-source certificate is checked.

**Evidence:** all five `zipCycle = true` propositions were reduced with `by decide +kernel` in local Lean 4.36.0-rc2 using the executable definitions of `SparseZipper`, `SideCycle.side`, `SweepPumping.start`, and `ZipAuditCore` copied into a minimal type model. [Raw40LongCycles.lean](Raw40LongCycles.lean) invokes the actual repository `zipCycle_sound` theorem and prints the five completion-level axiom profiles. Full original-source imports and parent integration have not been compiled in this invocation. [cycles.json](cycles.json) contains exact literal identities and the ready-to-consume fields.

The discovery method uses A-state candidates near either tape frontier, with a bounded key for indexing. It then checks the actual maximum/minimum head visited during the prospective segment and exact retained-side agreement (zero padding beyond finite support). Key collisions are harmless: the existing Lean checker validates the actual literal machine and period.

## Consumption

For each exact matching table, add the JSON entry (id, table, entry, period, right, bound) to the existing bank's `cycles` array, remove that exact identity from its `unresolved` list, and use Agent19's existing cycle-aware `certify_canonical.py` generator and source checker. The currently recorded 1RC child has no other unresolved leaf; the others retain their remaining entries. This closes no whole Raw40 parent and changes no global roster count until the complete corresponding consumer is accepted.
