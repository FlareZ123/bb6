# An exact six-state one-hole nonhalting family via context-congruent stack minimization

*Result dated 2026-11-28; original-source Lean 4.36.0-rc2 accepted by [run 46135066154](https://github.com/FlareZ123/bb6/actions/runs/46135066154), artifact [15259831500](https://github.com/FlareZ123/bb6/actions/runs/46135066154/artifacts/15259831500).*

## Theorem

Under standard two-symbol, six-state busy-beaver blank-tape conventions,
consider the *partial* machine

```
1RB1RA_1RC0LB_0RD1RF_1LD1LE_0RC1LB_---0RA
```

whose only undefined transition is state F reading symbol 0. **Every
completed six-state Turing machine agreeing with the eleven specified
transitions runs forever from the blank tape.** Equivalently, no such
completion ever reaches the unspecified transition. The Lean source
establishes the statement directly for the authentic machine table:

```lean
BB6.Agent4Raw56RootE11LB.M39232Block.M39232.never
  (m : Machine) (hm : compatible table m) : NeverHalts m
```

The proof is constructive at its finite verification boundary: a
two-stack certificate provides a finite invariant of **3,565**
control/head/left-stack/right-stack abstract configurations, with
**113** left and **209** right stack states. The certificate checker
verifies blank initial membership, avoidance of the undefined rule,
blank-bottom pop edges, deterministic pushes, and closure under every
inverse-pop transition. The generic theorem
`BB6.Agent4Automata.never` transfers this checked invariant to the
original, unrestricted infinite tape. The final theorem's accepted
axiom profile consists only of `propext`, `Classical.choice`, and
`Quot.sound` (no `sorryAx`, `native_decide`, or external oracle).

## Context-congruent quotient theorem and construction

An initial finite invariant independently discovered by an asymmetric
periodic-block abstraction contains 19,013 joint configurations (141
left and 933 right stack states). The following reusable operation
reduced the computational proof object by **81.25%** in its joint
relation, without relaxing the source theorem.

For a finite relation `R ⊆ Q × {0,1} × L × U`, set

```
C_L(l) = { (q,b,u) | (q,b,l,u) ∈ R }
C_U(u) = { (q,b,l) | (q,b,l,u) ∈ R }.
```

Partition each stack's states by equality of these complete *other-side
context signatures*. Iteratively refine either partition until every
recorded push transition on a fixed input symbol has a unique quotient
target. Take the image of `R` and the union of all inverse-pop edges in
the quotient stack states.

**Why this preserves closure.** Fix a quotient configuration and a
quotient inverse-pop edge. Choose an original configuration
`(q,b,l,u) ∈ R` representing it. The projected pop edge comes from an
original stack state `u'` (or `l'`) in the same stack class as the
popped-side representative. Equality of its complete context signature
guarantees that replacing the popped-side state by `u'` (or `l'`)
produces another tuple in `R` with the *same* control and other-side
state. Original relation closure supplies the post-pop successor in
`R`. Push congruence makes that successor project to the deterministic
quotient push target, so the quotient relation is closed. Initial blank
membership and avoidance of the halting slot are preserved because
the initial and projected configurations have the same control/read
bits; the blank stack class is assigned index 0.

This abstract argument justifies the candidate quotient, **but the
accepted machine theorem does not rely on trusting the quotienting
algorithm**. The Python quotient generation *independently enumerates
and checks every projected successor*, and the unchanged Lean source
checker validates the resulting concrete certificate from scratch.
Thus even a bug in this general mathematical abstraction would not
inject an unsound proof into the machine theorem.

## Reproduction and scope

- Original explicit machine and exact relation:
  [`m39232_block_cert.py`](../im-results/agent4-raw56-root-pilot/m39232_block_cert.py).
- Context signature refinement and independent closure test:
  [`minimize_relation.py`](../im-results/agent4-two-sided-automata/minimize_relation.py).
- Size-pinned wrapper and authentic-source Lean generator:
  [`m39232_min_cert.py`](../im-results/agent4-raw56-root-pilot/m39232_min_cert.py) and
  [`m_min_single.py`](../im-results/agent4-raw56-root-pilot/m_min_single.py).
- CI verifier:
  [`agent4-min-two-stack.yml`](../.github/workflows/agent4-min-two-stack.yml),
  `machine=m39232`. Successful run
  [46135066154](https://github.com/FlareZ123/bb6/actions/runs/46135066154),
  artifact SHA256
  `efcb429a6ff4800525e69beec5610502b60fbce248f4b3001a875c47f4af810d`.
  The separate exact-quotient generator check passed
  [46134998195](https://github.com/FlareZ123/bb6/actions/runs/46134998195).
- Related methodological details and two additional computational
  candidates appear in
  [`context-quotient.md`](../im-results/agent4-two-sided-automata/context-quotient.md).

This theorem closes **one genuine one-hole BB(6) family** in the
43,348-leaf Raw56 E1=1LB local search. It does **not** by itself prove
the exhaustive six-residual parent Cover; five other residuals and the
parent source cut must be linked. It supplies neither a global BB(6)
upper bound nor the exact value of BB(6).
