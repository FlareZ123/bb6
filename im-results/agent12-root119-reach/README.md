# Reachability exclusion for the odd-even prefix base case

This directory contains a small Lean result complementing
`agent42-root119-guard/Root119PrefixShield.lean`.

## Formal result

`Root119OddEvenN0Reach.lean` proves an inductive invariant for the authentic
six-state auxiliary machine. In particular, no blank-reachable configuration
can satisfy all of:

- state `B` reading blank at head position `h`;
- tape values `1,0,1` at `h-1,h-2,h-3`;
- a blank at `h+1`.

These are the (n=0) local left/right conditions of the odd-even prefix
family. The proof also establishes that Agent 42's synthetic
`oddEvenShieldCounterexample` is not in `Reach`.

The invariant is deliberately split into two clauses. A reachable `A0`
configuration with local tape pattern `(h-2,h-1,h,h+1) = (1,0,0,0)`
is impossible because the only incoming state is `E`, whose transition
writes a 1 at one of the two cells required to be blank. A `B0` state with
the stated local pattern can only have come from `A0` or `F0`: the former
would require the excluded `A0` pattern, while the latter writes 1 at
`h+1`.

The Lean file prints axiom dependencies for the invariant and both
corollaries. The intended trusted basis is `propext` and `Quot.sound`;
there is no `sorryAx`.

## Scope and remaining question

This excludes the (n=0) synthetic tape witness as a blank-reachable
configuration. It does not establish the odd-even boundary guard for
(n\geq 1), and it does not remove the guard from Agent 42's general
conditional preservation theorem. The 10-million-step census has 22
odd-even prefix inputs; its prefix-left-six audit reports 21 inputs with
`010101` and one with `000101`, all satisfying the boundary guard.
The general reachability implication for the observed positive (n) cases
remains open.

The source theorem being complemented is
`../agent42-root119-guard/Root119PrefixShield.lean`.
