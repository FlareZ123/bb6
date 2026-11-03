import Row262
set_option maxHeartbeats 3000000
namespace BB6.Row262

def rightBurst : Nat → List Bool
  | 0 => []
  | q + 1 => rightBurst q ++ [false, false, true]

def leftBurst : Nat → List Bool
  | 0 => []
  | q + 1 => [false, true, true] ++ leftBurst q

-- Five physical steps from the D0 branch.
theorem burst_d5 (ls ys : List Bool) :
    run 5 ⟨0, ls, false, true :: false :: false :: false :: true :: ys⟩ =
      ⟨0, false :: false :: false :: true :: true :: ls, true, ys⟩ := by
  simp [run, step, moveR]

-- Four further physical steps from the A1 branch, with an immediate left zero.
theorem burst_a4 (ls ys : List Bool) :
    run 4 ⟨0, false :: false :: false :: true :: true :: ls, true, ys⟩ =
      ⟨0, false :: true :: true :: ls, false, true :: false :: ys⟩ := by
  simp [run, step, moveL, moveR]

-- Two guaranteed A checkpoints with exactly 9 physical transitions.
theorem pair9 (ls ys : List Bool) :
    run 9 ⟨0, ls, false,
      true :: false :: false :: false :: true :: ys⟩ =
      ⟨0, false :: true :: true :: ls, false, true :: false :: ys⟩ := by
  have decomp := run_add 5 4 ⟨0, ls, false,
    true :: false :: false :: false :: true :: ys⟩
  simpa [burst_d5, burst_a4] using decomp

-- q repetitions of [0,0,1] after the initial right-hand bits 1,0.
-- Each pair adds [0,1,1] to the nearest-first left tape; exact raw duration 9q.
theorem pair_burst (q : Nat) (ls ys : List Bool) :
    run (9*q) ⟨0, ls, false, [true, false] ++ rightBurst q ++ ys⟩ =
      ⟨0, leftBurst q ++ ls, false, [true, false] ++ ys⟩ := by
  induction q generalizing ls ys with
  | zero => simp [rightBurst, leftBurst, run]
  | succ q ih =>
      have e : 9*(q+1) = 9*q+9 := by omega
      rw [e, run_add]
      have h := ih ls ([false, false, true] ++ ys)
      rw [show [true, false] ++ rightBurst (q+1) ++ ys =
        [true, false] ++ rightBurst q ++ ([false, false, true] ++ ys) from
         by simp [rightBurst, List.append_assoc]]
      rw [h]
      simpa [leftBurst, List.append_assoc] using pair9 (leftBurst q ++ ls) ys

#print axioms BB6.Row262.burst_d5
#print axioms BB6.Row262.burst_a4
#print axioms BB6.Row262.pair9
#print axioms BB6.Row262.pair_burst
end BB6.Row262
