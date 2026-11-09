# #429 deficit-five: all-parameter physical J return

**Verified 9 November 2026, original six-state source Lean 4.36.0-rc2.** The exact prepared-tape transition at deficit `2u-w=5` is now a theorem for every natural parameter. It does not decide the actual blank-origin #429 computation or BB(6).

## Main theorem

For the original table `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`, let `J(u,w)` denote the complete bi-infinite prepared J tape with state A and head at zero, using `BB429JPhysical.jTape`. For all `v : Nat`, [Low5Physical.lean](Low5Physical.lean) proves

```lean
theorem BB429Low5Physical.low5_raw_head (v : Nat) :
    ∃ c', BB6Coverage.run target429 (4*v*v+22*v+100)
      {state:=A,head:=0,tape:=jTape (v+3) (2*v+1)} = some c' ∧
      Represents (junc 6 0 (4*v+2)) c' ∧
      c'.head = 2 - ((2*v : Nat) : Int)
```

Thus `J(v+3,2v+1)` reaches a fully represented, translated `J(6,4v+2)` after exactly `4v²+22v+100` primitive moves, final head `2-2v`. The representation includes every tape cell, including both infinite blank tails.

[Original-source CI run 42609132138](https://github.com/FlareZ123/bb6/actions/runs/42609132138) succeeded on unchanged dependencies, compiled both new files, and rejected any `sorryAx` in the logged axiom audits. The independent symbolic source chain was separately checked in [run 42608914573](https://github.com/FlareZ123/bb6/actions/runs/42608914573).

## Exact mathematical decomposition

The initial `v+1` original-machine bubble repairs take `4(v+1)²+2(v+1)` moves, ending with head `2v+2` at the exact zipper `stage5 v = A/1 [1^(4v+4)10101^6] > [01]`. The original source representation theorem establishes all tape cells, including the two residual negative-side holes.

[Low5Delta.lean](Low5Delta.lean) proves the remaining
```lean
runWithDelta (12*v+94) (stage5 v) =
  some (junc 6 0 (4*v+2), -(4*v : Int))
```
with source steps: an `8v+16` A/F and A/B sweep to the exact C/0 stage (delta `+4`); six C/0 to E/1 steps (delta `-2`); `4v+9` E/1 leftward steps (delta `-(4v+9)`); and an all-suffix `63`-step primitive transfer (delta `+7`) from E/1 with left `01^6` and right `1^9 Y` to the `Junc(6,0,...)` template. The last macro has literal kernel-reduced proof by `rfl`, uniform in arbitrary right suffix `Y`.

The physical proof combines the signed source transition with a full exact characterization of the bubble-repaired infinite tape and the previously verified source-to-physical simulation theorem. The total source and bubble costs simplify to `4v²+22v+100`; their signed head shifts simplify to `2-2v`.

## Relation to prior work and unresolved question

Agent18's [low-J dossier](../agent18-429-low-j/README.md) previously recorded the deficit-five time, target, and signed displacement as **finite computational evidence**. The present theorem is an unbounded all-parameter proof for the literal raw machine. The external Cryptids J accelerator describes the successor shape but supplies a different source/proof setting. The adjacent deficit-two and deficit-three branches have independent source certificates.

The pivotal remaining question is **authentic blank-root reachability of the fatal J/B001 halting gate**. A prepared J transition is not a proof that the blank execution enters its input family. The immediately broader deficit-`4k+1` branch, whose finite data suggest an all-parameter two-dimensional signed return, remains to be formally derived. No numeric bound for BB(6) follows from the present theorem.
