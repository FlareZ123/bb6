# Machine #429: all-parameter low-J deficit-two raw-tape return

**Intermediate research, 9 November 2026, Agent 6.** These source files address the original six-state, two-symbol machine `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`. They do not settle its initially blank run or determine BB(6).

## Mathematical result

[Low2Physical.lean](Low2Physical.lean) constructs the following all-natural original-raw-machine theorem. For every `v : Nat`, the canonical prepared infinite tape `J(v+1,2*v)` returns, after **exactly `4*v*v+22*v+79` successful primitive instructions**, to a configuration whose state and every cell of its bi-infinite tape satisfy `Represents (junc 0 0 (4*v+12))`. In the usual `u=v+1` notation this is the `J(u,2u-2)` branch, with primitive cost **`4*u*u+14*u+61`** and the canonical successor `J(0,4*u+8)`. The theorem states the target up to its physical head translation; an exact numerical endpoint head displacement is a separate obligation.

The exact proposed Lean statement is:

```lean
theorem BB429Low2Physical.low2_raw (v : Nat) :
  ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429
    (4*v*v+22*v+79)
    {state:=BB6Bubble.A,head:=0,
     tape:=BB429JPhysical.jTape (v+1) (2*v)} = some c' ∧
    BB429PhysicalBridge.Represents
      (BB429FinishScanEDelta.junc 0 0 (4*v+12)) c'
```

This is a **full tape statement**, relying on the existing precise `Represents` semantics for all integer cells; the input is a prepared J chart rather than the actual blank root.

## Proof mechanism and dependency reuse

The new [Low2Stage.lean](Low2Stage.lean) factors the nontrivial source continuation into an arbitrary-length `A/1,F/1` left sweep, `A/0,B/1` right repaint, and a fresh `C/0` gateway. Its proved first statement is

```lean
run (8*v+10) (stage v) =
  some (z 2 (ones (4*v+14)) false [])
```

for the exact intermediate source tape

```lean
stage v = z 0 (ones (4*v) ++ (true::false::ones 6))
            true [true,false,true].
```

It composes with the **already original-source-certified** `BB429CZeroToJunc0.even_C0_to_junc0`, specialized to `k=2*v+6`, in `6*k+33=12*v+69` additional steps, giving

```lean
run (20*v+79) (stage v) =
  some (junc 0 0 (4*v+12)).
```

The original physical prefix is obtained from `BB6Bubble.multi_bubble_prefix` with `u=j=v`, applied to the *larger* J tape `J(v+1,2*v)`. The choice `u=v` is crucial: the untouched extra negative-even hole and the right boundary are exactly what makes the source stage. That prefix executes `4*v*v+2*v` instructions. The new physical module proves the entire intermediate tape has the form `negFill (jTape (v+1) (2*v)) v`, and identifies it with the zipper `stage v` at head coordinate `2*v`. The existing `source_run_rep` then transports the exact source continuation to the unchanged original raw machine.

The key new tape identity, proved by `omega` from the original geometric tape definitions, is:

```text
negFill (jTape (v+1) (2*v)) v x = true
iff
   (-2*v-8 <= x <= 2*v+1 and x != -2*v-2)
   or x = 2*v+3.
```

The resulting left zipper has `4*v` ones, then `1,0,1^6`; the right zipper is `1,0,1`. This is exact at every integer coordinate.

## Verification and caveats

The unbounded `ar_pairs_exact`, `stage_to_C0`, `stage_to_junc`, and the geometric tape identity/`stage_tape_rep` proofs have compiled locally in **Lean 4.36.0-rc2** using reconstructed exact source zipper and tape definitions. The local source harness used two explicitly declared pre-existing theorems (`af_pairs` and `even_C0_to_junc0`) as mock axioms for fast standalone typechecking; those are real kernel-checked theorems in the checked-in source, and **the committed modules do not contain those mock axioms**.

A full unchanged-repository-source audit is requested through [manual CI](../../.github/workflows/agent6-429-low2.yml). The first [run 42591287695](https://github.com/FlareZ123/bb6/actions/runs/42591287695) was **infrastructure-interrupted** (runner received shutdown code 143) while compiling the pre-existing `CZeroToJunc0` dependency chain, before the new Lean files were checked. [Run 42592019717](https://github.com/FlareZ123/bb6/actions/runs/42592019717) requests original-source verification including the new physical theorem. Until that run finishes successfully, **treat the full original-source theorem as submitted, locally preflighted, and unconfirmed by original-source CI**; report no verified full-raw result from these new files alone. Both new modules print their axiom audits, and workflow checks for `sorryAx`.

There is no blank-root nonhalting result. The authenticated accelerated root visits the low2 parameter type (for example `J(9,16)`), but proving one prepared-tape branch supplies a formal component of the all-time orbit analysis rather than a global exclusion of the fatal `w+1=2u` gateway. A productive follow-up is explicit signed-head tracking and integration into original Cryptids accelerated section transitions, then use root-sensitive invariant development rather than more synthetic prepared-tape families.
