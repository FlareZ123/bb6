# Agent 18: exact whole-cycle halting iff for Machine B

**Intermediate formal method; no BB(6) holdout decision or bound improvement.** This strengthens the previous single-decrement section theorem in `im-results/agent5-b-section/Section.lean` by proving the **entire countdown** and its exact finite-halting equivalence for every starting `a`. It is based on the transition table formally certified by upstream Google DeepMind at [Cryptids](https://github.com/google-deepmind/cryptids/blob/ced8f9f44f67a167d5ecc03e687b048c67926371/BusyBeaver/BB6/M_1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_HHH1RE.lean); an explicit kernel-checked import-based equivalence to the upstream `next` is still desirable.

Machine B: `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`. Certified blank-tape entry is `(3,0,0)`.

`BReduction.lean` defines exactly the published map `nextB`, a finite nonhalting trace relation `Star`, and a finite `Halts` inductive predicate. For the parity transducer

```
F(p,d) = (d % 2, 3*(d/2)+2+4*p)
```

the kernel-checked `cycle` theorem proves for **every** natural `a,d` and `p<=1`:

```
Star (a,p,d) (0, (iterF a (p,d)).1, (iterF a (p,d)).2).
```

In particular all `a` decrements are accompanied by their exact required `b`-drain traces, not only an informal macro abbreviation.

The theorem `cycle_halts_iff` proves for **every** natural `a`:

```
Halts (a,0,0) ↔
  (iterF a (0,0)).1 = 0 ∨
  ((iterF a (0,0)).1 = 1 ∧ Halts (2*(iterF a (0,0)).2+9,0,0)).
```

Thus the next entire-cycle parity bit exactly decides whether the present cycle halts or recursively resumes at its unique reset. This is a symbolic biconditional in the **actual** accelerated dynamics, not a finite computation. The final global obligation remains proving whether a recursively sampled parity bit is ever zero starting from `a=3`. Only the independent published Cryptids proof establishes the connection to raw TM semantics; this local file copies its map exactly.

## Verification

On 2026-11-02, `BReduction.lean` compiled successfully under the supplied Lean **4.36.0-rc2**, importing only `Lean.Elab.Tactic.Omega`. Both `#print axioms cycle` and `#print axioms cycle_halts_iff` printed exactly `[propext, Quot.sound]`, with no `sorryAx` or `native_decide`. The local source SHA-256 was `e10b23b2d685cd437158fbbe709b16b9a8e70e511912fc87a788006df40d1ade`. Recompile with `lean im-results/agent18-b-cycle/BReduction.lean` after installing Lean 4.36.0-rc2.

This result formalizes an already understood conceptual reduction, and should remain in `im-results/` pending an all-time blank-entry decision or sufficiently novel theorem.
