# Exact outer branches of the #429 J chart

## Established source theorem

Let `jTape u w` be the symbolic J-chart tape from the original-source #429 formalization. The module `JFirstBranch.lean` now proves two distinct all-parameter branches of the exact raw transition relation `target429`.

**Continuation branch.** For every `u,w : Nat` with `2*u+3 ≤ w`,

```lean
run target429 (4*u*u+10*u+27)
  {state:=A,head:=0,tape:=jTape u w} =
  some {state:=A,head:=2*(u:Int)+3,
    tape:=jTapeAt (2*u+3) (w-(2*u+3)) (2*(u:Int)+3)}
```

The run returns exactly to the translated J family with parameters
`(2*u+3, w-(2*u+3))`, after `4*u^2+10*u+27` successful raw steps.

**Fatal boundary branch.** For every `u,w : Nat` with `w+1=2*u`,

```lean
run target429 (4*u*u+10*u+27)
  {state:=A,head:=0,tape:=jTape u w} = none
```

After `4*u^2+10*u+25` successful steps, the machine is in state C at head
`2*u+1`. The two cells there are exactly `01`: C reads 0, writes 0 and
moves right into D/1, whose transition is undefined. Thus the machine makes
`4*u^2+10*u+26` successful moves and halts on the next query.

## Proof structure

Both theorems use the same source-connected prefix:

1. `j_F0_exact`: `4*u^2+6*u+7` raw steps from the J tape to the F/0 setup.
2. `f0_to_c1`: the exact 14-step F/0-to-C/1 setup.
3. `j_c_sweep`: `2*(2*u+2)=4*u+4` steps through the C/1,B/0 pairs.

For the continuation branch, `cb_exit` handles the final 11 pair and the
separate theorem `j_first_branch_tape` proves equality of the complete
translated tape.

For the fatal branch, `j_fatal_boundary_bits` proves the boundary cells are
01 directly from the original J-tape definition and `w+1=2*u`.
`baseTape_above_pivot`, `f0Tape_neq`, `setupTape_above`, and
`cbPaint_right` transport those exact bits through the F/0 setup and C/B
sweep. `C01_halts` then supplies the undefined D/1 transition.

The shared total time is
`(4*u^2+6*u+7)+14+(4*u+4)+2 = 4*u^2+10*u+27`.
In the fatal case, the last two queries are C/0 (successful) and D/1
(undefined); in the continuation case, they are C/1 and B/1 (both
successful).

## Verification and provenance

- Full manual original-source workflow: [CI run 42390569324](https://github.com/FlareZ123/bb6/actions/runs/42390569324).
- Exact checked commit: `4afb59a786703dc0f86c6ba081b385db4a0caddf`.
- The workflow compiled the original dependency chain and this module, printed
  the theorem axiom audits, and passed its explicit `sorryAx` rejection gate.
- The two new boundary-bit lemmas were independently checked locally with
  Lean 4.36.0-rc2 using the exact J-tape, zero-paint, negative-fill, setup,
  and C/B sweep definitions. Their local axiom reports contain only
  `propext` and `Quot.sound`.

## Remaining cases and scope

Within the prefix domain `w+1 ≥ 2*u`, the outer cases are now established:
`w=2*u-1` is fatal, while `w≥2*u+3` continues to the translated J family.
The three neighboring cases `w=2*u`, `w=2*u+1`, and `w=2*u+2` remain
open. Values below the prefix domain are outside these theorems.

These are exact conditional J-chart transition results. They do not prove
that the authentic blank-tape orbit enters this J family, decide the #429
machine's eventual behavior, or establish any BB(6) lower or upper bound.
The next useful step is to settle the three intermediate parameter cases
and connect the resulting complete J-chart dynamics to the authentic
blank-root criterion in
[the #429 physical-root dossier](../agent32-429-raw-parent/README.md).

This is intermediate work and remains in `im-results/`.
