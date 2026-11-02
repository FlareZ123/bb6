import ESixPairs
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192

namespace CryptidBoundary

/-- A further right-cylinder occurring in unconstrained suffix closure:
    0 (10)^q 1101010111 ys, for any right continuation ys. -/
def eAltTail (m q : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+2) ++ [true,true], false,
    pairs q ++ ([true,true,false,true,false,true,false,true,true,true] ++ ys), 4⟩

def altTurnPacket : List Bool :=
  [true,false,true,false,true,false,true,false,true,false]

def altReturnPacket : List Bool :=
  [false,true,false,true,false,true,false,true,false]

theorem eAltTail_two (m q : Nat) (ys : List Bool) :
    run 2 (eAltTail m q ys) =
      scanStart (q+1) (pairs (m+2) ++ [true,true])
        ([true,true,false,true,false,true,false,true,true,true] ++ ys) := by
  simp [eAltTail, scanStart, run, step, goL, goR, pairs]

theorem aAltTurn32 (q m : Nat) (ys : List Bool) :
    run 32
      (⟨oppairs (q+1) ++ (pairs (m+2) ++ [true,true]), false,
        [true,true,false,true,false,true,false,true,true,true] ++ ys, 0⟩ : Cfg) =
      cWalk (q+1) (pairs (m+2) ++ [true,true])
        (altTurnPacket ++ ys) := by
  simp [run,step,goL,goR,oppairs,pairs,cWalk,altTurnPacket]

theorem eAltTail_toB (m q : Nat) (ys : List Bool) :
    run (4*q+42) (eAltTail m q ys) =
      sweepB m (false :: List.replicate (2*q+6) true ++
        (altReturnPacket ++ ys)) := by
  have ht : 4*q+42=(2+2*(q+1))+(32+(2*(q+1)+4)) := by omega
  rw [ht,run_add (2+2*(q+1)) (32+(2*(q+1)+4)),
    run_add 2 (2*(q+1)),eAltTail_two,scan_run]
  change run (32+(2*(q+1)+4))
    (⟨oppairs (q+1) ++ (pairs (m+2) ++ [true,true]),false,
       [true,true,false,true,false,true,false,true,true,true] ++ ys,0⟩ : Cfg) = _
  rw [run_add 32 (2*(q+1)+4),aAltTurn32,
    run_add (2*(q+1)) 4,cWalk_run,cBase]
  have hp :
    List.replicate (2*q+6) true =
      List.replicate 3 true ++
      (List.replicate (2*(q+1)) true ++ [true]) := by
    have hn : 2*q+6=3+(2*(q+1)+1) := by omega
    rw [hn,← List.replicate_append_replicate,
      ← List.replicate_append_replicate]
    rfl
  rw [hp]
  simp only [altTurnPacket,altReturnPacket,List.append_assoc,
    List.cons_append,List.nil_append,List.replicate_succ,
    List.replicate_zero]

theorem eAltTail_run (m q : Nat) (ys : List Bool) :
    run (2*m+4*q+45) (eAltTail m q ys) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (false :: List.replicate (2*q+6) true ++
          (altReturnPacket ++ ys)),5⟩ := by
  have ht : 2*m+4*q+45=(4*q+42)+(2*m+3) := by omega
  rw [ht,run_add,eAltTail_toB,sweepB_run]

/-- New universal E return on 1101010111, all k,q and any unknown right tape. -/
theorem full_E_alt_tail (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+80+4*q)
      (init (List.replicate (3*k+2) true ++ false ::
        (pairs q ++
          ([true,true,false,true,false,true,false,true,true,true] ++ ys)))) =
      ⟨[],false,List.replicate (8*k+5) true ++
        (false :: List.replicate (2*q+6) true ++
          (altReturnPacket ++ ys)),5⟩ := by
  have ht : 12*k*k+49*k+80+4*q =
    (12*k*k+41*k+33)+(2*(4*k+1)+4*q+45) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k+1)+4*q+45) (eAltTail (4*k+1) q ys) = _
  rw [eAltTail_run]
  rw [show 2*(4*k+1)+3=8*k+5 by omega]

#print axioms eAltTail_two
#print axioms aAltTurn32
#print axioms eAltTail_toB
#print axioms eAltTail_run
#print axioms full_E_alt_tail
end CryptidBoundary
