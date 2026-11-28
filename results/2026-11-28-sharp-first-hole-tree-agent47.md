# Sharp ordinary-step soundness for exhaustive first-undefined-transition trees

**Status:** formal theorem accepted by original-source Lean 4.36.0-rc2 compilation on 28 November 2026. **Scope:** a theorem about proof-carrying finite partial-machine tree classifiers, not an upper bound on all six-state machines.

## Statement

Let `PartialMachine` be a finite-domain two-symbol six-state transition table whose entries may be unassigned, and let `Cover P p` assert that every complete Turing machine compatible with the partial table `p` satisfies predicate `P`. Write `OrdinaryBound B m` for the standard alternative: either `m` never halts, or it halts within **B ordinary Turing-machine steps including the halt transition**.

The original `Q0ExhaustiveTree.check` is an executable Boolean proof checker for a finite exhaustive first-undefined-transition tree. For every natural bound `B`, fuel `f`, partial table `p`, proof tree `t`, Boolean symbolic-leaf recognizer `sym`, and justified symbolic-leaf interpretation, the following implication is proved:

```lean
theorem check_sharp (B : Nat) (sym : PartialMachine → Bool)
    (hsym : ∀ p, sym p = true → Cover (OrdinaryBound B) p)
    (fuel : Nat) (p : PartialMachine) (t : Tree)
    (h : check (B+5) sym fuel p t = true) :
    Cover (OrdinaryBound B) p
```

The familiar first-write weighted classifier is normally run at `B+5` to absorb five possible normalization steps. **The theorem removes exactly that five-step allowance for ordinary halting time, using the existing accepted tree without weakening any nonhalting hypothesis.**

An additional accepted theorem, `split_sharp`, supplies a reusable sharp ordinary interpretation of a correctly checked full 25-way first-undefined-entry split.

## Proof mechanism

The proof is structural induction on checker fuel, keeping the original exhaustive tree, exact table refinements, and exact certificates unchanged. At each terminating first-hole leaf, the checker witnesses a finite prefix of `n` assigned moves and a first undefined transition, with the numeric condition

\[
n+6\le B+5.
\]

Hence \(n+1\le B\). The exact ordinary first-hole lemma `BB6.Agent5ExactOneHole.last_hole_exact` then proves that any compatible completion either never halts or halts at the **next** primitive transition, with halting time exactly \(n+1\). The split case uses `first_hole_halts` for the new halt-transition child, and applies the induction hypothesis independently to each of the other 24 possible instruction children. Accepted nonhalting side-cycle and two-stack-automaton leaves remain nonhalting; symbolic leaves use precisely the explicit `hsym` premise.

This is not the generally invalid assertion that *every* weighted bound `B+5` implies an ordinary bound `B`. It depends on the **first-hole structure** and a certified first-undefined transition at every terminating leaf.

## Reproducible formal evidence

- [Lean source: `OrdinaryQ0Exhaustive.lean`](../im-results/agent47-raw11-adapter/OrdinaryQ0Exhaustive.lean), namespace `BB6.Agent47OrdinaryQ0Exhaustive`, theorems `hole_sharp`, `check_sharp`, `split_sharp`.
- [Accepted complete source closure CI 46110753510](https://github.com/FlareZ123/bb6/actions/runs/46110753510) and [compiled proof-artifact 15249158169](https://github.com/FlareZ123/bb6/actions/runs/46110753510/artifacts/15249158169).
- Exact first-hole dependency `BB6.Agent5ExactOneHole.lastPackedExact`, with [accepted source CI 46110177221](https://github.com/FlareZ123/bb6/actions/runs/46110177221).
- Axiom printout for `check_sharp` and `split_sharp`: `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or `native_decide` axioms, and no unchecked certificate leaf.

**Application under investigation:** Agent5's complete 30,793-node q0-root53 exhaustive tree has now independently passed source compilation at weighted bound 208 ([CI 46109014135](https://github.com/FlareZ123/bb6/actions/runs/46109014135)); the sharp interpreter targets ordinary bound 203, with a separately source-accepted compatible 203-step halter. The actual proof composition establishing its *sharp upper bound* must be separately kernel-checked. This note does **not** claim that application complete.

## Frontier implications and limitation

Any existing exact first-hole tree using the same `Q0ExhaustiveTree` checker, and equipped with sound symbolic-leaf ordinary Covers, can be reinterpreted at the sharper ordinary threshold without rerunning the combinatorial classifier. A full Busy Beaver upper-bound proof still requires a complete partition of all six-state machines; this theorem certifies **individual finite-tree soundness**, not that all required trees exist or that unresolved branches vanish.
