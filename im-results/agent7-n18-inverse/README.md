# Agent 7: fixed P1 n=18 all-time blank-entry exclusion

**Research status, 2026-11-02:** A complete finite inverse-cone proof was constructed and locally Lean kernel-checked against a signature-compatible copy of the genuine `GAncestor` and `Blocked` constructors. The complete original-source audit runs in [agent7-p1-n18-certificate.yml](../../.github/workflows/agent7-p1-n18-certificate.yml) and must pass before declaring the stronger source-verified conclusion. This is an **intermediate** individual-index result; it does not decide P1 or BB(6).

## Statement

For machine `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`, let the actual accelerated blank-origin predicate be `BB6.Agent1.Reach` and `H(n) = 14*2^n - 2*n - 10`. The generated theorem is

```lean
BB6.Agent7N18.no_blank_critical_18 :
  ¬ BB6.Agent1.Reach 2 (14*2^18 - 2*18 - 10)
```

Numerically `H(18)=3,669,970`; Agent50's universal `critical_target_implies_three` reduces a hypothetical reachable `(2,H(18))` to `(H(18)-6,3)=(3,669,964,3)`. The source-derived `Blocked` predicate of Agent4Cone excludes the latter.

## Exact inverse cone

`gen_n18.py` deterministically enumerates the universal `GAncestor` predecessor list for each positive interior hub, constructs full case-disjunction proofs by induction over the **original inductive definition**, then closes every feeder branch using existing original-source necessary blank-orbit invariants. Each interior proof `inv_i` is exhaustive over every possible recursive inverse nesting, not bounded-time sampling or a guessed finite inverse depth.

The generated certificate contains **51 interior hubs**, **152 total exact inverse branches**, **78 modularly impossible leaves** (positive odd right counter and even left coordinate congruent to two modulo four), and **51 positive even-right leaves** with left coordinate `a+12` strictly between two adjacent numbers of the form `14*2^j`. It also exhaustively eliminates the exceptional source input `v=1` at every hub. The 51 hub proofs are composed into a `Blocked (3669964) 3` certificate and transferred to blank-origin nonreachability through `ConeKernel.blocked_no_reach`.

A standalone exact constructor-signature Lean 4.36.0-rc2 check compiled the generated `Blocked` proof and reported only `[propext, Classical.choice, Quot.sound]`. Its final transfer to actual source `Reach` awaits the GitHub CI audit. Reproduction: run `python im-results/agent7-n18-inverse/gen_n18.py`; the script creates `N18.lean` next to itself and prints exact branch counts. Then use the manual workflow, which compiles unchanged original `GParity,GInverse,PosEvenForm,ResetGate,P1Triple,P1ResidualArithmetic,P1ResidualReach,P1Gate,ConeKernel` modules and checks generated `N18.lean` with the Lean kernel and final `#print axioms`.

## Scope and credit

The necessary-ancestor relation and exact blank reachability criteria are sourced from Agents1, 4, 47, and 50. This contribution is a fully explicit closed finite inverse cone for one previously unclassified exponent, `n=18`, with reproducible generated proof and an original-source verification path. Generalization to an entire surviving residue family remains open. Fixed-n exclusion does not prove that P1 is nonhalting and does not improve the maximum halting-runtime bounds for BB(6).
