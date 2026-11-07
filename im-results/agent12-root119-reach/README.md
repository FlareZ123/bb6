# Reachability exclusion for the first two odd-even prefix lengths

This directory contains a Lean result complementing
`agent42-root119-guard/Root119PrefixShield.lean`.

## Formal result

`Root119OddEvenN0Reach.lean` proves that no blank-reachable configuration
of the six-state auxiliary machine can have all of the following:

- state `B`, reading 0 at head position `h`;
- tape context `101` at positions `h-3,h-2,h-1`;
- tape context `000` or `110` at positions `h+1,h+2,h+3`.

The `000` case is the n=0 odd-even prefix input. The `110` case
is the n=1 input. In both cases, the theorem excludes the configuration
from `Reach` without using the more distant terminal-zero hypotheses or
the six-cell boundary guard.

The proof uses a seven-cell sliding-window abstraction. Each abstract step
allows an arbitrary bit at the newly exposed endpoint, so it over-approximates
the concrete tape evolution. The reverse-reachable closure of the two
forbidden B0 windows contains exactly 12 abstract states. The Lean file lists
those states and proves the predecessor-closure property by finite case
analysis. Every concrete machine step induces an abstract step, while the
blank initial window lies outside the 12-state set. Therefore neither target
window can occur in a blank-reachable configuration.

The independent script `audit_window_closure.py` reconstructs the 768-state
abstract graph, verifies 342 forward-reachable states, recomputes the
12-state reverse closure, and checks that the blank initial state is outside
it. Run it with `python audit_window_closure.py`.

The expanded module passed the repository workflow in
[run 42418128383](https://github.com/FlareZ123/bb6/actions/runs/42418128383).

The file also proves that Agent 42's synthetic
`oddEvenShieldCounterexample` is not in `Reach`. Its local tape pattern
is a valid counterexample to dropping the boundary guard for arbitrary
configurations, but it does not witness a reachable failure.

The Lean file prints axiom dependencies for the finite closure, reachability
invariant, and corollaries. They depend only on `propext` and
`Quot.sound`; there is no `sorryAx`.

## Scope and remaining question

This resolves the first two odd-even lengths. It does not establish the
odd-even boundary guard for n≥2, and it does not remove the guard from
Agent 42's general conditional preservation theorem.

The 10-million-step census reports 22 odd-even prefix inputs, all satisfying
the boundary guard. Its prefix-left-six audit records 21 inputs with
`010101` and one with `000101`. This is computational evidence; the
general reachability implication for n≥2 remains open.

The source theorem being complemented is
`../agent42-root119-guard/Root119PrefixShield.lean`.
