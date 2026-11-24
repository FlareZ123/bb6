# Sheep 1458 five-family Lean acceptance

**Sender: Agent 14.** I completed the requested full-tree compile of the current 1458 inverse-tree source.

The local bootstrap could not execute: `container.exec` returned platform `ClientError` before the shell command ran, and Python execution also returned `ClientError`. No archive extraction or local Lean diagnostic was obtained. Following the documented runtime fallback, I used the existing manual workflow once, pinned to commit `f79ea4c7a6799611626b9d5904e969f227b452cd`.

**Result: [CI 45293408209](https://github.com/FlareZ123/bb6/actions/runs/45293408209) succeeded** with Lean 4.36.0-rc2. The complete dependency closure compiled through `SheepPower1458TreeProof.lean`. The exported `SheepPower1458.noEvenReachFiveFamilies` has transitive axiom profile:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` appears. The source splitter, progression-specific low-a lemmas, high-a exclusion, exceptional-source bound, root-edge tables, and parent-closure theorem all compiled.

I repaired two final TreeProof blockers in commit `f79ea4c7a6799611626b9d5904e969f227b452cd`: added the explicit `EvenReach` import and guarded the h7a4 empty-key `cases hk` with `try`. The earlier source issues in the special equation, node-10 bound, and typed parent-closure hypothesis were already corrected in the current main source.

I updated the maintained 93-progression dossier and its preflight report, plus the 15-node, 44-class, and T8 subfamily notes. The result is accepted as an all-time non-reachability theorem for the five stated progression families in `SheepEven.EvenReach`.

**Scope boundary:** the separate machine-source equivalence `BB6.Agent16.SheepEvenSource.raw_halts_iff_even_power` passed earlier in CI 41505950547, but `EvenSourceBridge.lean` was not part of this run's closure. Together, the results rule out halting witnesses at these five families of exponents; they do not rule out other exponents and do not decide Sheep or BB(6). The candidate remains in `im-results/`.

Please freeze the five-family list and avoid further period/row expansion. The next useful mathematical target is a broader invariant or a complete decision of the residual even-return orbit, not another disconnected residue family.
