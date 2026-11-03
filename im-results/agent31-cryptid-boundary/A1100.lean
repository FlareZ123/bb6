import Lean.Elab.Tactic.Omega
import Boundary

set_option maxHeartbeats 5000000
set_option maxRecDepth 512
namespace CryptidBoundary

def aBoundary (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false :: pairs m ++ [true, true], false, ys, 0⟩

theorem a1100_start (m : Nat) (ys : List Bool) :
    run 17 (aBoundary (m+2) (true::true::false::false::ys)) =
      sweepD m (true::true::false::(List.replicate 6 true ++ ys)) := by
  simp [aBoundary, sweepD, run, step, goL, goR, pairs]

theorem a1100_run (m : Nat) (ys : List Bool) :
    run (2*(m+2)+16) (aBoundary (m+2) (true::true::false::false::ys)) =
      ⟨[],false,List.replicate (2*(m+2)+1) true ++
          (false::List.replicate 6 true ++ ys),5⟩ := by
  have ht : 2*(m+2)+16 = 17+(2*m+3) := by omega
  rw [ht, run_add, a1100_start, sweepD_run]
  have hp : List.replicate (2*m+3) true ++
         (true::true::false::(List.replicate 6 true ++ ys)) =
       List.replicate (2*(m+2)+1) true ++
         (false::List.replicate 6 true ++ ys) := by
    calc
      _ = (List.replicate (2*m+3) true ++ List.replicate 2 true) ++
            (false::List.replicate 6 true ++ ys) := by simp [List.append_assoc]
      _ = List.replicate ((2*m+3)+2) true ++
            (false::List.replicate 6 true ++ ys) := by rw [List.replicate_append_replicate]
      _ = _ := by rw [show 2*m+3+2=2*(m+2)+1 by omega]
  exact congrArg (fun z : List Bool => Cfg.mk [] false z 5) hp

theorem full_A_1100 (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+54)
      (init (List.replicate (3*k+1) true ++ false::true::true::false::false::ys)) =
      ⟨[],false,List.replicate (8*k+7) true ++
          (false::List.replicate 6 true ++ ys),5⟩ := by
  have ht : 12*k*k+49*k+54 =
      (12*k*k+41*k+32)+(2*(4*k+3)+16) := by omega
  rw [ht, run_add, prefix_A]
  change run (2*(4*k+3)+16)
    (aBoundary (4*k+3) (true::true::false::false::ys)) = _
  have hs := a1100_run (4*k+1) ys
  have hm : (4*k+1)+2 = 4*k+3 := by omega
  rw [hm] at hs
  have ho : 2*(4*k+3)+1 = 8*k+7 := by omega
  rw [ho] at hs
  exact hs

#print axioms a1100_start
#print axioms a1100_run
#print axioms full_A_1100
end CryptidBoundary
