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

## Stronger two-parameter physical theorem (9 November 2026)

The original deficit-five result is now subsumed by the full **odd-deficit `4k+1`, `k≥1`, physical theorem** in [LowOddPhysical.lean](LowOddPhysical.lean). For every `v,n : Nat`, the *literal original #429 table*, run on the infinite prepared tape `J(v+2*n+3,2*v+1)` with head zero, executes exactly `4*v*v+22*v+22*n+100` successful primitive moves and reaches a configuration fully representing the translated chart `J(2*n+6,4*v+2)`, with physical head coordinate `2-2*v`. In particular, `n=0` recovers the r=5 row, and `n≥1` settles previously finite-conjectural r=9,13,17,... in one theorem. The full signed physical result is `BB429LowOddPhysical.lowOdd_raw_head`.

**Verification:** [Original-source Lean CI run 42613098361](https://github.com/FlareZ123/bb6/actions/runs/42613098361), compiled unchanged definitions in `BB429JPhysical`, `BB429DeltaPhysicalBridge`, and actual raw `BB6Coverage.run`. The `sorryAx` rejection gate passed, and printed final axiom audit is only `[propext, Classical.choice, Quot.sound]`. A prior source-only audit [42612278537](https://github.com/FlareZ123/bb6/actions/runs/42612278537) verified the two-parametric source proof.

The entire source derivation is factored through [LowOddSource.lean](LowOddSource.lean) and [LowOddCore.lean](LowOddCore.lean). After `v+1` physical bubble repairs costing `4(v+1)^2+2(v+1)`, the tape has exactly `v+1` filled formerly blank negative-even cells and the source zipper `stageOdd(v,n)=A/1\;[1^(4v+4)(10)^(2n+2)1^6]>[01]`. The remaining source run has primitive cost `12v+22n+94` and head displacement `-4v`. Its leading `8v+16` section reaches C/0; then a six-step C/0→E/1 transfer and a `4v+9` E/1 left sweep expose a uniform `22n+63` transducer. This transducer consumes the extra `(10)^(2n)` block through `6n` source moves, a constant 16-move bridge, an `8n` four-mark right sweep, and a `8n+47` C/1-to-Junc suffix. The C/1 suffix itself uses a 12-step prepare, a `4n+2` A/F shift, a fixed 21-step A/C corridor, `4n+10` C/1 pair moves, and two final moves. All segment lemmas are universal in the untouched right suffix. Full physical correctness is established through an exact `stageOdd` tape characterization: the residual holes occupy precisely the negative even interval `[-2v-4n-6,-2v-4]`; all other positions are accounted for, including both infinite blank tails.

**Scope:** This resolves a parameter-uniform *prepared-tape* low-J transition, not the authenticity of that prepared input along the machine's all-zero orbit. The remaining `r=4k`, `r=4k+2`, `r=4k+3` deficits and the globally decisive blank-reachable fatal-gate avoidance remain separate. Agent18's earlier finite numerical extrapolations have now been upgraded to theorems for the entire `r≡1 (mod 4)`, `r≥5` subfamily. This was not claimed as external research priority; our files remain correctly in `im-results/`.
