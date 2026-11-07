# Exact primitive first branch of the #429 J family

## Result

For every pair of natural numbers (u,w) satisfying (2u+3\le w), the source-verified raw transition table `target429` satisfies

```lean
theorem j_first_branch (u w : Nat) (hw : 2*u+3 ≤ w) :
    run target429 (4*u*u+10*u+27)
      {state:=A,head:=0,tape:=jTape u w} =
    some {state:=A,head:=2*(u:Int)+3,
      tape:=jTapeAt (2*u+3) (w-(2*u+3)) (2*(u:Int)+3)}
```

Thus this branch returns exactly to the J family with parameters
`(2*u+3, w-(2*u+3))), translated to head position `2*u+3`, after exactly
`4*u^2+10*u+27` raw machine steps.

The proof is in [JFirstBranch.lean](JFirstBranch.lean). It is an exact raw-run
theorem, not a simulator-only claim.

## Proof decomposition

The raw run is composed from three verified pieces:

1. `j_F0_exact`: (4u^2+6u+7) steps from the J tape to the F/0 setup
   configuration.
2. `f0_to_c1`: a 14-step setup from F/0 to C/1.
3. A C/B sweep of (2u+2) pairs, taking (4u+4) steps, followed by the
   final two-step exit pair.

The total is
[
(4u^2+6u+7)+14+(4u+4)+2=4u^2+10u+27.
]

The pointwise tape identity is proved separately as
`j_first_branch_tape`; the final theorem composes it with the raw-step
sweep and exit lemmas. The F/0 write is proved extensionally, and the
`#print axioms` audit covers the prefix, setup, sweep, tape identity, and
composed theorem.

## Verification

- GitHub Actions workflow: [run 42378679590](https://github.com/FlareZ123/bb6/actions/runs/42378679590), successful.
- The axiom audit reports no `sorryAx` dependency for `j_F0_exact`,
  `f0_to_c1`, `cb_exit`, `j_first_branch_tape`, or `j_first_branch`.
  The final theorem depends only on the standard Lean axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- Independent finite simulation checked 32 additional parameter pairs
  (`u=0..7`, with four admissible values of `w` per `u`). An earlier
  155-pair regression is also recorded in the development notes. These
  simulations are regression checks; the universal claim is established by
  the Lean proof.

## Scope and next obligations

This result proves one conditional branch of the #429 J transition. It does
not show that the authentic blank-tape orbit enters this branch, determine
the orbit's eventual behavior, or establish a BB(6) bound.

The highest-value continuations are:

- prove the fatal boundary branch (w+1=2u) with its exact raw halting time;
- prove the neighboring exceptional branches (w=2u,2u+1,2u+2);
- connect the resulting source-level branch costs to the authentic blank
  orbit and its accumulated raw step count.

This remains intermediate research in `im-results/`, not a BB(6) solution
or a publishable global result.
