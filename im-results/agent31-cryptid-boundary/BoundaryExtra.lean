import Lean.Elab.Tactic.Omega
import Boundary

set_option maxHeartbeats 5000000
namespace CryptidBoundary

-- A complete return when an A-boundary has another zero to its right.
def preA (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false :: pairs m ++ [true,true], false, ys, 0⟩

theorem preA_start (m : Nat) (ys : List Bool) :
  run 3 (preA m (false::ys)) = sweepD m (true::true::ys) := by
  simp [preA, sweepD, step, run, goR, goL, pairs]

theorem preA_nil_start (m : Nat) :
  run 3 (preA m []) = sweepD m [true,true] := by
  simp [preA, sweepD, step, run, goR, goL, pairs]

theorem preA_run (m : Nat) (ys : List Bool) :
  run (2*m+6) (preA m (false::ys)) =
    ⟨[],false,List.replicate (2*m+5) true ++ ys,5⟩ := by
  have ht : 2*m+6 = 3+(2*m+3) := by omega
  rw [ht, run_add, preA_start, sweepD_run]
  have hL : List.replicate (2*m+3) true ++ (true::true::ys) =
      List.replicate (2*m+5) true ++ ys := by
    calc
      _ = (List.replicate (2*m+3) true ++ List.replicate 2 true) ++ ys := by simp [List.append_assoc]
      _ = List.replicate ((2*m+3)+2) true ++ ys := by rw [List.replicate_append_replicate]
      _ = _ := by rw [show (2*m+3)+2 = 2*m+5 by omega]
  exact congrArg (fun z : List Bool => Cfg.mk [] false z 5) hL

theorem preA_nil_run (m : Nat) :
  run (2*m+6) (preA m []) =
    ⟨[],false,List.replicate (2*m+5) true,5⟩ := by
  have ht : 2*m+6 = 3+(2*m+3) := by omega
  rw [ht, run_add, preA_nil_start, sweepD_run]
  have hL : List.replicate (2*m+3) true ++ [true,true] =
      List.replicate (2*m+5) true := by
    calc
      _ = List.replicate (2*m+3) true ++ List.replicate 2 true := by rfl
      _ = List.replicate ((2*m+3)+2) true := List.replicate_append_replicate
      _ = _ := by rw [show (2*m+3)+2 = 2*m+5 by omega]
  exact congrArg (fun z : List Bool => Cfg.mk [] false z 5) hL

theorem full_A_00 (k : Nat) (ys : List Bool) :
  run (12*k*k+49*k+44)
    (init (List.replicate (3*k+1) true ++ false::false::ys)) =
      ⟨[],false,List.replicate (8*k+11) true ++ ys,5⟩ := by
  have ht : 12*k*k+49*k+44 =
      (12*k*k+41*k+32) + (2*(4*k+3)+6) := by omega
  rw [ht, run_add, prefix_A]
  change run (2*(4*k+3)+6) (preA (4*k+3) (false::ys)) = _
  rw [preA_run]
  rw [show 2*(4*k+3)+5 = 8*k+11 by omega]

theorem full_A_nil (k : Nat) :
  run (12*k*k+49*k+44) (init (List.replicate (3*k+1) true)) =
      ⟨[],false,List.replicate (8*k+11) true,5⟩ := by
  have ht : 12*k*k+49*k+44 =
      (12*k*k+41*k+32) + (2*(4*k+3)+6) := by omega
  rw [ht, run_add, prefix_A_nil]
  change run (2*(4*k+3)+6) (preA (4*k+3) []) = _
  rw [preA_nil_run]
  rw [show 2*(4*k+3)+5 = 8*k+11 by omega]

-- Blank-right suffix, including an actual all-zero unbounded extension.
theorem prefix_B_nil (k : Nat) :
  run (12*k*k+41*k+31) (init (List.replicate (3*k) true)) =
      ⟨pairs (4*k+3) ++ [true,true], false, [], 1⟩ := by
  have hs := setup24 (List.replicate (3*k) true)
  change run 24 (init (List.replicate (3*k) true)) =
    midM 3 (List.replicate (3*k) true) at hs
  have ht : 12*k*k+41*k+31 = 24 + pumpTime k + (2*(4*k+3)+1) := by
    rw [pumpTime_formula]; omega
  rw [ht]
  calc
    run (24 + pumpTime k + (2*(4*k+3)+1))
      (init (List.replicate (3*k) true)) =
      run (2*(4*k+3)+1)
        (run (pumpTime k) (run 24 (init (List.replicate (3*k) true)))) := by
        rw [run_add (24+pumpTime k), run_add 24 (pumpTime k)]
    _ = _ := by
      rw [hs]
      have hp := pump_iter k ([] : List Bool)
      simp only [List.append_nil] at hp
      rw [hp, boundary_B_nil]

theorem full_B_nil (k : Nat) :
  run (12*k*k+49*k+40) (init (List.replicate (3*k) true)) =
    ⟨[],false,List.replicate (8*k+9) true,5⟩ := by
  have ht : 12*k*k+49*k+40 =
      (12*k*k+41*k+31) + (2*(4*k+3)+3) := by omega
  rw [ht, run_add, prefix_B_nil]
  change run (2*(4*k+3)+3) (preB (4*k+3) []) = _
  rw [preB_run]
  rw [show 2*(4*k+3)+3 = 8*k+9 by omega]
  simp

#print axioms full_A_00
#print axioms full_A_nil
#print axioms full_B_nil
end CryptidBoundary
