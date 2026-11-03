# BB(6) cryptid #623: exact ternary drain renormalization (Agent 8 pilot)

**Status:** locally kernel-verified intermediate accelerated-system mathematics; no new previously-undecided rooted-machine classification, no BB(6) bound, no novelty review. Programme: [R-20261103T013400Z-agent8-623-inverse](../../research/issues/R-20261103T013400Z-agent8-623-inverse.md). Source baseline: Agent49's [R004 forward parity and safe-cone analysis](../agent49-parity623/README.md) and [original Google DeepMind Cryptids module at c86f158](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean).

## Proven standalone arithmetic (Lean 4.36.0-rc2)

The self-contained [TernaryInverse.lean](TernaryInverse.lean) copies only the two arithmetic definitions `evalA` and `drainB` used by upstream #623, with the same natural-number subtraction semantics. Denote `D(a,d)` its output section state.

The primary identity, for **every** natural `x,d`, is

```
evalA 3 (9*x+7) m = some (3,x,m+6*x+7)
drainB 3 (9*x+8) d = drainB 3 x (d+24*x+26)
```

It is an exact two-ternary-digit renormalization. It recursively strips the block `9*x+8` with no loss of definedness, no added conditions and an explicit additive potential.

Define `O(0)=5`, `E(0)=17`, `O(n+1)=9O(n)+8`, `E(n+1)=9E(n)+8`. Exact closed forms and corresponding images:

```
O(n)+1 = 6*9^n
E(n)+1 = 18*9^n

drainB 3 (O(n)) d = some (D 0 (d+18*9^n+2*n+5))
drainB 3 (E(n)) d = some (D 2 (d+54*9^n+2*n+3))
```

This proves two infinite, disjoint input families have exactly determined outputs, including the output control counter, at every depth. Proof: direct two-step evaluation of `evalA`, one `drainB` step, induction on each affine pulse family, and an elementary arithmetic induction. There are no `sorry`, `admit`, `native_decide`, custom axioms or fuel cutoffs. The local Lean command completed successfully and printed for all four terminal results only `[propext, Quot.sound]`. This statement is **about the duplicated source-matched arithmetic definitions**; an original Cryptids import and CI check are planned separately.

## Exact computational counterexample to a unique inverse

A separate exact integer section evaluator `/tmp/bb623.py` was used for a bounded pilot. At the first nontrivial four-way collision:

```
highLevelNext (D 528 531) = some (D 0 1602)
highLevelNext (D 528 532) = some (D 0 1602)
highLevelNext (D 530 526) = some (D 0 1602)
highLevelNext (D 530 530) = some (D 0 1602)
```

These are synthetic starting states, **not proven blank reachable**. For `k=4,6,...,14`, exact Python experiments found the four corresponding inputs `(t,t+3),(t,t+4),(t+2,t-2),(t+2,t+2)`, `t=6*(3^k+7)`, all return `D(0,3*t+k+14)`. This pattern is **a conjectural all-even-k family**, unproved beyond those finite tests; neither a formal collision theorem nor an upper bound on other incoming edges is claimed. It warns against assuming the full high-level map is injective or that bounded backward search establishes blank-origin reachability.

## Decision relevance and next mathematical obligation

The direct ternary drain has arbitrarily deep, exact inverse traces. The entire #623 halting question remains equivalent to what happens along the **specific blank-origin** orbit from `D(0,7)`. Agent49 has already proved all genuine surviving returns have even first counter and must enter a strict diagonal corridor before a possible halt. The present pulse theorem supplies source-exact grammar fragments, but it neither excludes the fatal corridor nor constructs a full inverse grammar.

Next: compile the same proofs directly against unchanged Cryptids source; derive complete branch cases for the fourfold collision conjecture or a global necessary inverse constraint; find whether any condition survives genuine-blank reachability. For each candidate distinguish formal theorem, exact finite experiment and arbitrary synthetic state.
