# Machine C: one-family halting criterion, kernel verified

**Status:** substantive intermediate result for an unresolved BB(6) machine. It does **not** determine BB(6), prove this machine nonhalting, or improve a global BB(6) bound.

Target original machine: `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`.

The source `Funnel.lean` copies the three-counter `nextC` accelerator from Google DeepMind's certified Cryptids BB(6) module `BusyBeaver/BB6/M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.lean`. Its actual blank-entry counter state is `(a,k,c)=(5,0,1)`. The upstream formal library supplies the machine-to-counter correspondence, but our standalone source has not imported that library into a cross-module kernel checked bridge. Verify the copied definition against upstream before making original-machine-level claims.

## Strongest verified theorem

Let `Reach` mean zero or more successful accelerated transitions. Let `blankHalts` mean that some reachable state has `nextC s = none`. Lean 4.36.0-rc2 certifies:

```lean
theorem blank_halts_iff_single_family :
  blankHalts ↔ ∃ j, Reach (5,0,1) (0,2*j,4*j+10)
```

**The only remaining halting family is the real blank-start reachability question `(0,2j,4j+10)`.** Reaching any member guarantees termination, and termination implies reaching some member. Proving every member unreachable would decide this Cryptids holdout as nonhalting. No such global exclusion has yet been shown.

## Proof structure

1. **Sweep funnel.** Define `funnel (a,k,c)` by `c=a+5 ∧ (a+k)%2=0`. Every funnel state deterministically executes a finite sequence ending at the known dangerous precursor `(0,a+k,5)`.
2. **All predecessor branches.** An exhaustive `nextC` case split (`preimage_funnel`) verifies that predecessors of funnel states either already lie in the funnel or are one of `(1,4,0)` and `(0,2j,4j+10)`. The blank-entry state lies outside the funnel.
3. **Terminal completeness.** Independent `critical_predecessor`, `no_zero_output`, and reachability induction prove that the only reachable transitions into `c=2` come from `(0,2j,5)`. This establishes `blank_halts_iff_feeder` with both feeders.
4. **Eliminate singleton.** Six explicitly enumerated configurations form a backward-closed finite set with no blank-entry member: `(1,4,0)`, `(1,3,1)`, `(1,1,3)`, `(3,1,0)`, `(3,0,1)`, and `(2,0,4)`. `dead_preimage` verifies their predecessor closure; `blank_ne_singleton_feeder` is the resulting exact exclusion.
5. Eliminate that singleton disjunct from the earlier equivalence to prove the displayed one-family theorem.

## Verification and recovery

* Full Lean source: `Funnel.lean.xz.b64`, XZ-compressed and base64-encoded.
* Recover via `unpack.py`, which checks SHA-256 and atomically writes the source.
* Original Lean source size: **14,128 bytes**, SHA-256 `5385feff08cbbb6c59bbde7008011956e9195a7e5dcf9098f899a80e232bf712`.
* Lean: **4.36.0-rc2**. Imports only `Lean.Elab.Tactic.Omega`. No Mathlib, `sorry`, or `admit`.
* Successful local invocation: `lean Funnel.lean`.
* Output: `'BB6Agent10.blank_halts_iff_single_family' depends on axioms: [propext, Classical.choice, Quot.sound]`, without `sorryAx`.

## Remaining research tasks

* Exclude the entire `(0,2j,4j+10)` family from `Reach (5,0,1)`, or find a genuine counterexample.
* Investigate whether modular, parity, or backward-invariant constraints make this high-`c` feeder family easier than Agent 8's critical `(0,2j,5)` guard.
* Import the exact upstream Cryptids module to produce a Lean-checked equivalence between the standalone definition and the already certified machine acceleration.

This refines Agent 8's earlier `CriticalReach.lean` halting criterion. It remains a reduction of an open problem, so it belongs in `im-results/` pending a genuine holdout decision or independently defensible publishable result.

Author: Agent 10, 2026-11-02.
