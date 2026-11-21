# M1-even valuation bridge: local Lean acceptance

## Result

The theorem `BB6Coverage.Agent48M1EvenValuationBridge.m1EvenValuationBridge_run` is now kernel-checked from the original TM63 transition table.

For every natural number `v`, every infinite tape `T : Int → Bool`, and every head coordinate `h`, assume:

- `T h = false`;
- `state1LeftOnes T h (3*(v+1)+1)`, i.e. the required contiguous left-hand run of ones;
- the next two cells beyond that run are zero:
  `T (h-(3*(v+1)+2)) = false` and
  `T (h-(3*(v+1)+3)) = false`;
- the right boundary is `false, true, true, true` at `h+1,ldots,h+4).

Then the original source machine `tm2`, using the repository's infinite-tape `run` semantics, satisfies

```lean
run tm2 (12*v+23) ⟨1,h,T⟩ =
  some ⟨4,h+5,m1EvenValuationBridgeTape v T h⟩
```

The exact cost is the composition
`3*(3*(v+1)) + 7 + 3*(v+1) + 1 + 3 = 12*v+23`:
the counted state-1 left sweep, seven fixed setup transitions, counted state-5 right sweep, one-step exit, and three-step E scan.

## Formal verification

- Lean version: `Lean 4.36.0-rc2`.
- Exact target path: `im-results/agent48-counted-inc0/M1EvenValuationBridge.lean`.
- Exact target Git blob: `32ba6984aae5428e5e0e316cc356042c039323f9`.
- The target compiles with its source import closure.
- `#print axioms BB6Coverage.Agent48M1EvenValuationBridge.m1EvenValuationBridge_run` reports `[propext, Quot.sound]`.
- No `sorryAx` occurs in the target module's axiom output.

The local repair adds explicit source-table simp lemmas, normalizes the integer head coordinates, repairs the finite tape extensionality arguments, corrects sweep induction applications, and makes the final endpoint rewrites explicit.

## Scope and limitation

This establishes a reusable original-machine submacro under the stated local tape hypotheses. It does **not** prove that the authentic blank-root computation reaches a configuration satisfying those hypotheses, does not establish the full TM63 halting time, and does not determine `BB(6)`. The full root-connected composition remains a separate obligation.

## Reproduction outline

Reconstruct Lean 4.36.0-rc2 from the uploaded split archive as specified in the project prompt. Stage the target's direct import closure in dependency order:

1. `Frontier.lean`
2. `Symmetry.lean`
3. `RootShift.lean`
4. `ChampionRootBridge.lean`
5. `M1EvenState1Sweep.lean`
6. `M1EvenState5Sweep.lean`
7. `CountedSweep.lean`
8. `M1EvenValuationBridge.lean`

Compile each with `lean -o Module.olean Module.lean`, setting `LEAN_PATH` to the staging directory. The final target command is:

```sh
lean -o M1EvenValuationBridge.olean M1EvenValuationBridge.lean
```
