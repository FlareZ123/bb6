import Lean.Elab.Tactic.Omega
import A1100

namespace CryptidBoundary

set_option maxHeartbeats 8000000
set_option maxRecDepth 2048

/-- A new ten-symbol terminal for the A boundary. Every variable stack depth
    reaches the source's existing D sweep after exactly 33 raw transitions. -/
theorem a1101010111_start (m : Nat) (ys : List Bool) :
    run 33 (aBoundary m
      (true::true::false::true::false::true::false::true::true::true::ys)) =
    sweepD m
      (true::true::false::true::false::true::false::true::false::true::false::ys) := by
  simp [aBoundary, sweepD, run, step, goL, goR, pairs]

/-- Exact unbounded raw return at the formerly unresolved 1101010111 terminal.
    The final zero is physical tape data when ys is nonempty. -/
theorem a1101010111_run (m : Nat) (ys : List Bool) :
    run (2*m+36) (aBoundary m
      (true::true::false::true::false::true::false::true::true::true::ys)) =
    ⟨[], false, List.replicate (2*m+5) true ++
      (false::true::false::true::false::true::false::true::false::ys), 5⟩ := by
  have ht : 2*m+36 = 33+(2*m+3) := by omega
  rw [ht, run_add, a1101010111_start, sweepD_run]
  have hp :
      List.replicate (2*m+3) true ++
        (true::true::false::true::false::true::false::true::false::true::false::ys) =
      List.replicate (2*m+5) true ++
        (false::true::false::true::false::true::false::true::false::ys) := by
    calc
      _ = (List.replicate (2*m+3) true ++ List.replicate 2 true) ++
            (false::true::false::true::false::true::false::true::false::ys) := by
              simp [List.append_assoc]
      _ = List.replicate ((2*m+3)+2) true ++
            (false::true::false::true::false::true::false::true::false::ys) := by
              rw [List.replicate_append_replicate]
      _ = _ := by rw [show (2*m+3)+2=2*m+5 by omega]
  exact congrArg (fun z : List Bool => Cfg.mk [] false z 5) hp

/-- Genuine original F/0 symbolic source, before adding any blank-root claim. -/
theorem full_A_1101010111 (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+74)
      (init (List.replicate (3*k+1) true ++
        false::true::true::false::true::false::true::false::true::true::true::ys)) =
    ⟨[], false, List.replicate (8*k+11) true ++
      (false::true::false::true::false::true::false::true::false::ys), 5⟩ := by
  have ht : 12*k*k+49*k+74 =
      (12*k*k+41*k+32)+(2*(4*k+3)+36) := by omega
  rw [ht, run_add, prefix_A]
  change run (2*(4*k+3)+36)
    (aBoundary (4*k+3)
      (true::true::false::true::false::true::false::true::true::true::ys)) = _
  have hs := a1101010111_run (4*k+3) ys
  have ho : 2*(4*k+3)+5 = 8*k+11 := by omega
  rw [ho] at hs
  exact hs

#print axioms a1101010111_start
#print axioms a1101010111_run
#print axioms full_A_1101010111

end CryptidBoundary
