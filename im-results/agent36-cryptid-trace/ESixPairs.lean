import Lean.Elab.Tactic.Omega
import CryptidPairs

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace CryptidBoundary

/-- General E-side suffix: q many 10 tokens then 1101111110 and any tail. -/
def eNinePairs (m q : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+2) ++ [true,true], false,
    pairs q ++ ([true,true,false] ++
      (List.replicate 6 true ++ (false::ys))), 4⟩

def aNinePacket : List Bool :=
  [true,false,true,false,true,false,true,true,true,false]

theorem eNinePairs_two (m q : Nat) (ys : List Bool) :
    run 2 (eNinePairs m q ys) =
      scanStart (q+1) (pairs (m+2) ++ [true,true])
        ([true,true,false] ++
          (List.replicate 6 true ++ (false::ys))) := by
  simp [eNinePairs, scanStart, run, step, goL, goR, pairs]

/-- The complete fixed A-side 20-step handoff after E scanned the q pairs.
    At least one reversed pair is available on the left. -/
theorem aNine_twenty (q m : Nat) (ys : List Bool) :
    run 20
      (⟨oppairs (q+1) ++ (pairs (m+2) ++ [true,true]), false,
        [true,true,false] ++
          (List.replicate 6 true ++ (false::ys)), 0⟩ : Cfg) =
      cWalk (q+1) (pairs (m+2) ++ [true,true])
        (aNinePacket ++ ys) := by
  simp [run, step, goL, goR, oppairs, pairs,
    aNinePacket, cWalk, List.append_assoc]

/-- All q and m: a complete E-to-B return. -/
theorem eNinePairs_toB (m q : Nat) (ys : List Bool) :
    run (4*q+30) (eNinePairs m q ys) =
      sweepB m (false :: List.replicate (2*q+6) true ++
        (packetSix ++ ys)) := by
  have ht : 4*q+30 = (2+2*(q+1))+(20+(2*(q+1)+4)) := by omega
  rw [ht, run_add (2+2*(q+1)) (20+(2*(q+1)+4)),
    run_add 2 (2*(q+1)), eNinePairs_two, scan_run]
  change run (20+(2*(q+1)+4))
    (⟨oppairs (q+1) ++ (pairs (m+2) ++ [true,true]), false,
      [true,true,false] ++
        (List.replicate 6 true ++ (false::ys)), 0⟩ : Cfg) = _
  rw [run_add 20 (2*(q+1)+4), aNine_twenty,
    run_add (2*(q+1)) 4, cWalk_run, cBase]
  have hp :
    [false,true,true,true] ++
      (List.replicate (2*(q+1)) true ++
        (aNinePacket ++ ys)) =
    false :: List.replicate (2*q+6) true ++
      (packetSix ++ ys) := by
    simp only [aNinePacket, packetSix, List.replicate_append_replicate,
      List.append_assoc, List.cons_append, List.nil_append]
    congr 1
    simp [← List.replicate_append_replicate]
    omega
  exact congrArg (sweepB m) hp

theorem eNinePairs_run (m q : Nat) (ys : List Bool) :
    run (2*m+4*q+33) (eNinePairs m q ys) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (false :: List.replicate (2*q+6) true ++
          (packetSix ++ ys)), 5⟩ := by
  have ht : 2*m+4*q+33 = (4*q+30)+(2*m+3) := by omega
  rw [ht,run_add,eNinePairs_toB,sweepB_run]

/-- Universal original Cryptid six-state F-section return on E-side
    0(10)^q1101111110, including q=0; arbitrary suffix is preserved. -/
theorem full_E_nine_pairs (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+68+4*q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++
          ([true,true,false] ++
            (List.replicate 6 true ++ (false::ys)))))) =
      ⟨[], false, List.replicate (8*k+5) true ++
        (false :: List.replicate (2*q+6) true ++
          (packetSix ++ ys)), 5⟩ := by
  have ht : 12*k*k+49*k+68+4*q =
    (12*k*k+41*k+33)+(2*(4*k+1)+4*q+33) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k+1)+4*q+33) (eNinePairs (4*k+1) q ys) = _
  rw [eNinePairs_run]
  rw [show 2*(4*k+1)+3=8*k+5 by omega]

#print axioms eNinePairs_two
#print axioms aNine_twenty
#print axioms eNinePairs_toB
#print axioms eNinePairs_run
#print axioms full_E_nine_pairs
end CryptidBoundary
