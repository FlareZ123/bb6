import Lean.Elab.Tactic.Omega
import CryptidPairs

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace CryptidBoundary

/-- E-side suffix: q copies of 10, then 110111 and any further bits. -/
def eAfterDoubleThree (m q : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+2) ++ [true,true], false,
    pairs q ++ ([true,true,false] ++ ([true,true,true] ++ ys)), 4⟩

/-- The bounded A turn leaves its suffix arbitrary after the first 110111. -/
def aThreePacket : List Bool :=
  [true,false,true,false,true,false]

def eThreePacket : List Bool :=
  [false,true,false,true,false]

theorem eAfterDoubleThree_two (m q : Nat) (ys : List Bool) :
    run 2 (eAfterDoubleThree m q ys) =
      scanStart (q+1) (pairs (m+2) ++ [true,true])
        ([true,true,false] ++ ([true,true,true] ++ ys)) := by
  simp [eAfterDoubleThree, scanStart, run, step, goL, goR, pairs]

/-- Fixed A-turn, uniform in number of scanned 10 pairs, left parameter,
    and all bits following the three required ones. -/
theorem aAfterDoubleThree_twenty (q m : Nat) (ys : List Bool) :
    run 20
      (⟨oppairs (q+1) ++ (pairs (m+2) ++ [true,true]), false,
        [true,true,false] ++ ([true,true,true] ++ ys), 0⟩ : Cfg) =
      cWalk (q+1) (pairs (m+2) ++ [true,true])
        (aThreePacket ++ ys) := by
  simp [run, step, goL, goR, oppairs, pairs, aThreePacket, cWalk]

/-- Exact E-to-B return after 0 (10)^q 110111 y. -/
theorem eAfterDoubleThree_toB (m q : Nat) (ys : List Bool) :
    run (4*q+30) (eAfterDoubleThree m q ys) =
      sweepB m (false :: List.replicate (2*q+6) true ++
        (eThreePacket ++ ys)) := by
  have ht : 4*q+30 = (2+2*(q+1))+(20+(2*(q+1)+4)) := by omega
  rw [ht, run_add (2+2*(q+1)) (20+(2*(q+1)+4)),
    run_add 2 (2*(q+1)), eAfterDoubleThree_two, scan_run]
  change run (20+(2*(q+1)+4))
    (⟨oppairs (q+1) ++ (pairs (m+2) ++ [true,true]), false,
      [true,true,false] ++ ([true,true,true] ++ ys), 0⟩ : Cfg) = _
  rw [run_add 20 (2*(q+1)+4), aAfterDoubleThree_twenty,
    run_add (2*(q+1)) 4, cWalk_run, cBase]
  have hr :
    List.replicate (2*q+6) true =
      List.replicate 3 true ++
        (List.replicate (2*(q+1)) true ++ [true]) := by
    have hn : 2*q+6 = 3+(2*(q+1)+1) := by omega
    rw [hn, ← List.replicate_append_replicate,
      ← List.replicate_append_replicate]
    rfl
  rw [hr]
  simp only [aThreePacket, eThreePacket, List.append_assoc,
    List.cons_append, List.nil_append, List.replicate_succ,
    List.replicate_zero]

theorem eAfterDoubleThree_run (m q : Nat) (ys : List Bool) :
    run (2*m+4*q+33) (eAfterDoubleThree m q ys) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (false :: List.replicate (2*q+6) true ++
          (eThreePacket ++ ys)), 5⟩ := by
  have ht : 2*m+4*q+33 = (4*q+30)+(2*m+3) := by omega
  rw [ht,run_add,eAfterDoubleThree_toB,sweepB_run]

/-- Universal original Cryptid machine F-section return from E on
    0(10)^q110111, ALL k,q and any right continuation ys. -/
theorem full_E_after_110111 (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+68+4*q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++
          ([true,true,false] ++ ([true,true,true] ++ ys))))) =
      ⟨[], false, List.replicate (8*k+5) true ++
        (false :: List.replicate (2*q+6) true ++
          (eThreePacket ++ ys)), 5⟩ := by
  have ht : 12*k*k+49*k+68+4*q =
    (12*k*k+41*k+33)+(2*(4*k+1)+4*q+33) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k+1)+4*q+33)
    (eAfterDoubleThree (4*k+1) q ys) = _
  rw [eAfterDoubleThree_run]
  rw [show 2*(4*k+1)+3=8*k+5 by omega]

/-- The specific six-one 1101111110 case is a consequence of the
    stronger three-one prefix theorem above. -/
theorem full_E_nine_pairs (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+68+4*q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++
          ([true,true,false] ++
            (List.replicate 6 true ++ (false::ys)))))) =
      ⟨[], false, List.replicate (8*k+5) true ++
        (false :: List.replicate (2*q+6) true ++
          (packetSix ++ ys)), 5⟩ := by
  have h := full_E_after_110111 k q
    (List.replicate 3 true ++ (false::ys))
  have hr :
    ([true,true,false] ++
      ([true,true,true] ++ (List.replicate 3 true ++ (false::ys)))) =
    ([true,true,false] ++ (List.replicate 6 true ++ (false::ys))) := by
      simp [List.replicate]
  have hp :
    eThreePacket ++ (List.replicate 3 true ++ (false::ys)) =
      packetSix ++ ys := by
      simp [eThreePacket, packetSix, List.replicate]
  rw [hr, hp] at h
  exact h

#print axioms eAfterDoubleThree_two
#print axioms aAfterDoubleThree_twenty
#print axioms eAfterDoubleThree_toB
#print axioms eAfterDoubleThree_run
#print axioms full_E_after_110111
#print axioms full_E_nine_pairs
end CryptidBoundary
