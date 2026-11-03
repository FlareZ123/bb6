import Lean.Elab.Tactic.Omega
import A1100

set_option maxHeartbeats 5000000
set_option maxRecDepth 1024
namespace CryptidBoundary

theorem a110111_start (m : Nat) (ys : List Bool) :
    run 27 (aBoundary (m+3)
      (true::true::false::true::true::true::ys)) =
      sweepD m (List.replicate 8 true ++
          (false::true::false::true::false::ys)) := by
  simp [aBoundary,sweepD,run,step,goL,goR,pairs]

theorem a110111_run (m : Nat) (ys : List Bool) :
    run (2*(m+3)+24) (aBoundary (m+3)
      (true::true::false::true::true::true::ys)) =
        ⟨[],false,List.replicate (2*(m+3)+5) true ++
          (false::true::false::true::false::ys),5⟩ := by
  have ht : 2*(m+3)+24 = 27+(2*m+3) := by omega
  rw [ht,run_add,a110111_start,sweepD_run]
  have hp : List.replicate (2*m+3) true ++
        (List.replicate 8 true ++
          (false::true::false::true::false::ys)) =
        List.replicate (2*(m+3)+5) true ++
          (false::true::false::true::false::ys) := by
    rw [← List.append_assoc, List.replicate_append_replicate]
    congr 1
  exact congrArg (fun z : List Bool => Cfg.mk [] false z 5) hp

theorem full_A_110111 (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+62)
      (init (List.replicate (3*k+1) true ++
        false::true::true::false::true::true::true::ys)) =
      ⟨[],false,List.replicate (8*k+11) true ++
        (false::true::false::true::false::ys),5⟩ := by
  have ht : 12*k*k+49*k+62 =
     (12*k*k+41*k+32)+(2*(4*k+3)+24) := by omega
  rw [ht,run_add,prefix_A]
  change run (2*(4*k+3)+24)
    (aBoundary (4*k+3) (true::true::false::true::true::true::ys)) = _
  have hs := a110111_run (4*k) ys
  have hm : (4*k)+3 = 4*k+3 := by omega
  rw [hm] at hs
  have ho : 2*(4*k+3)+5 = 8*k+11 := by omega
  rw [ho] at hs
  exact hs

#print axioms a110111_start
#print axioms a110111_run
#print axioms full_A_110111
end CryptidBoundary
