import FirstGateRays
import High3Ladder
import Lean.Elab.Tactic.Omega

namespace BB429FirstGateRaw
open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429High3Ladder BB429FirstGateRays

theorem branchU_pos (u n : Nat) (hu : 1 ≤ u) : 1 ≤ branchU u n := by
  induction n generalizing u with
  | zero => simpa [branchU] using hu
  | succ n ih => exact ih (2*u+3) (by omega)

theorem branch_shift_anc (u n : Nat) (hu : 1 ≤ u) :
    branchShift u n + (2*branchU u n - 1) = anc u n := by
  induction n generalizing u with
  | zero =>
      simp [branchShift, branchU, anc]
  | succ n ih =>
      change 2*u+3 + branchShift (2*u+3) n +
        (2*branchU (2*u+3) n-1) = 2*u+3 + anc (2*u+3) n
      rw [Nat.add_assoc, ih (2*u+3) (by omega)]

/-- On a fully specified synthetic J-family tape, n first branches followed
    by the fatal boundary halt the actual six-state table. The time is
    expressed as an exact sum of primitive-machine step counts. -/
theorem raw_fatal_anc (u n : Nat) (hu : 1 ≤ u) :
    run target429 (branchCostSum u n + branchCost (branchU u n))
      (jConfig u (anc u n)) = none := by
  have hs := branch_shift_anc u n hu
  have hpos := branchU_pos u n hu
  have hbudget : branchShift u n ≤ anc u n := by omega
  have hhigh := j_high3_ladder u (anc u n) n 0 hbudget
  have hgate : (anc u n-branchShift u n)+1 = 2*branchU u n := by omega
  have hhalt : run target429 (branchCost (branchU u n))
        (jConfig (branchU u n) (anc u n-branchShift u n)) = none := by
    change run target429 (4*(branchU u n)*(branchU u n)+10*(branchU u n)+27)
      {state:=A,head:=0,tape:=jTape (branchU u n) (anc u n-branchShift u n)} = none
    exact BB429JFirstBranch.j_fatal_branch _ _ hgate
  have hshifted : run target429 (branchCost (branchU u n))
        (shiftConfig (0+(branchShift u n:Int))
          (jConfig (branchU u n) (anc u n-branchShift u n))) = none := by
    rw [run_shiftConfig, hhalt]
    rfl
  have hcompose :
      run target429 (branchCostSum u n + branchCost (branchU u n))
        (shiftConfig 0 (jConfig u (anc u n))) = none := by
    rw [BB6Bubble.run_add', hhigh]
    simpa using hshifted
  simpa [shiftConfig] using hcompose

/-- Infinite explicit even-parameter family of synthetic J tapes
    corresponding to the current right-five MidA boundary conjecture. -/
theorem even_raw_fatal (m : Nat) :
    run target429
      (branchCostSum 3 (4*(m+1)) + branchCost (branchU 3 (4*(m+1))))
      (jConfig 3 (4*(evenK m)+17)) = none := by
  rw [evenK_anc]
  exact raw_fatal_anc 3 (4*(m+1)) (by omega)

/-- Infinite explicit odd-parameter family of synthetic J tapes
    corresponding to the current right-five MidA boundary conjecture. -/
theorem odd_raw_fatal (m : Nat) :
    run target429
      (branchCostSum 11 (4*m+1) + branchCost (branchU 11 (4*m+1)))
      (jConfig 11 (4*(oddK m)+10)) = none := by
  rw [oddK_anc]
  exact raw_fatal_anc 11 (4*m+1) (by omega)

#print axioms branch_shift_anc
#print axioms raw_fatal_anc
#print axioms even_raw_fatal
#print axioms odd_raw_fatal
end BB429FirstGateRaw
