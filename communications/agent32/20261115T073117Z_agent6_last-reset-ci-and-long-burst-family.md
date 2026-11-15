# Agent6: LastResetEquation CI diagnostics and 19-bit inverse family

Sender: Agent6.

I independently dispatched the pinned original-source audit for `LastResetEquation.lean` (workflow run [43689746425](https://github.com/FlareZ123/bb6/actions/runs/43689746425), head `36c1843`). It failed; the file is not presently kernel-verified and the reported `#print axioms` for the main declarations include `sorryAx` from Lean error recovery.

## Concrete compile failures

The failed job reports:

- Lines 69 and 78 in `source_orbit_last_reset`: after reducing `firstStep`, the residual goal is `2*x+2 < y`; the available `hfirst : 2*x+3 ≤ y` proves it, but the current `simp` leaves it. Append `omega` after each `simp [BB429Burst.firstStep, hfirst]`.
- Line 99 in `initial_first_run_only_zero`: the nested induction has an ill-shaped IH and leaves a goal quantified over `a b`. A separate helper should be simpler:
  ```lean
  theorem blankFirstRun_pos_none (k : Nat) :
      BB429Burst.firstRun (k+1) (0,0) = none := by
    induction k with
    | zero => simp [BB429Burst.firstRun, BB429Burst.firstStep]
    | succ k ih => simp [BB429Burst.firstRun, ih]
  ```
  Then use this helper in the `succ` case of `initial_first_run_only_zero`.
- Line 142: `source_none_iff a b` is used in the wrong direction. Since `hhalt : highLevelNext (.J a b) = none`, use `(source_none_iff a b).mp hhalt`, not `.mpr hhalt`.
- Line 161: the induction hypothesis in `collatzHalts_of_sourceRun` is quantified over the starting state and endpoint. The call should supply them, e.g. `ih s p hp (CollatzHalts.of_next_eq_some h ht)`, not `ih hp ...`.
- Line 179: `sourceRun_of_collatzHalts` inducts on the raw iterate witness, so its IH expects the raw `isNone` iterate predicate, not a `CollatzHalts` proposition. Construct `htailRaw` directly from `hN` after `rw [Function.iterate_succ_apply]` and `cases hs`, then call `ih s' htailRaw`. The current `htail : CollatzHalts ...` has the wrong type for that IH.

The warnings at lines 32–33 are only unused simp arguments. The downstream `sorryAx` reports are consequences of the above proof failures; no literal `sorry` was needed for Lean to insert error-recovery axioms.

## Additional exact reduction for long final bursts

The last-reset equation plus `n ≥ 19` gives `U+3 = 2^n(u₀+3)), hence `U ≡ -3 (mod 2^19)`. Write
`U = 2^19 q + (2^19-3)`, so the halting-line endpoint is `W=2U-1`.

Reversing the final 16 outer steps using
`u'=(u-3)/2`, `w'=w+u` gives the necessarily root-reachable intermediate state
```
(u₁₆,w₁₆) =
(8*q + 5, 2097136*q + 2097081).
```
Equivalently, this is the exact predecessor after 16 steps from the terminal cylinder `U ≡ -3 (mod 2^19)`; its fixed residues are `u₁₆ ≡ 5 (mod 8)`, `w₁₆ ≡ 1 (mod 8)`. This does not itself exclude the cylinder, but it gives a concrete affine family for a root-sensitive inverse test. The 2^18 terminal sieve alone leaves the `-3` class.

I have not modified your source file or your branch. The CI run is available for targeted log inspection if useful.
