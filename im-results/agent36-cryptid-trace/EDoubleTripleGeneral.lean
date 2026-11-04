import CryptidTriplePairs
import CryptidPairs
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

namespace CryptidBoundary

/-- An A head with a reversed 01 stack crosses the 110 gateway in seven
    original six-state transitions and restores the entire left stack. -/
theorem aDoubleSeven (q : Nat) (L ys : List Bool) :
    run 7
      (⟨oppairs (q+1) ++ L,false,[true,true,false] ++ ys,0⟩ : Cfg) =
      ⟨[false,true,true] ++ (oppairs (q+1) ++ L),false,ys,0⟩ := by
  simp [run,step,goL,goR,oppairs]

theorem aTenOppStep (L ys : List Bool) :
    run 2 (⟨L,false,[true,false] ++ ys,0⟩ : Cfg) =
      ⟨[false,true] ++ L,false,ys,0⟩ := by
  simp [run,step,goL,goR]

/-- All 10 packets are consumed in exactly two steps each, reversing
    them as 01 packets onto the left. -/
theorem aTenOppIter (r : Nat) (L ys : List Bool) :
    run (2*r) (⟨L,false,pairs r ++ ys,0⟩ : Cfg) =
      ⟨oppairs r ++ L,false,ys,0⟩ := by
  induction r generalizing L with
  | zero => simp [run,pairs,oppairs]
  | succ r ih =>
    have ht : 2*(r+1)=2+2*r := by omega
    rw [ht,run_add]
    change run (2*r)
      (run 2 (⟨L,false,[true,false] ++ (pairs r ++ ys),0⟩ : Cfg)) = _
    rw [aTenOppStep]
    change run (2*r)
      (⟨[false,true] ++ L,false,pairs r ++ ys,0⟩ : Cfg) = _
    rw [ih]
    have hp : oppairs r ++ ([false,true] ++ L) =
        oppairs (r+1) ++ L := by
      rw [← List.append_assoc,oppairs_comm_one]
      rfl
    rw [hp]

/-- The final five-step turn needs no knowledge of the untouched right tape. -/
theorem aDoubleFive (q : Nat) (L ys : List Bool) :
    run 5
      (⟨[false,true,true] ++ (oppairs (q+1) ++ L),false,ys,1⟩ : Cfg) =
      cWalk (q+1) L ([true,false,true] ++ ys) := by
  simp [run,step,goL,goR,cWalk,oppairs]

/-- Entire A-side 110(10)^r111 variable turn, uniformly in all counters. -/
theorem aDoubleTurn (q r : Nat) (L ys : List Bool) :
    run (20+6*r)
      (⟨oppairs (q+1) ++ L,false,
        [true,true,false] ++ (pairs r ++ ([true,true,true] ++ ys)),0⟩ : Cfg) =
      cWalk (q+1) L
        ([true,false,true] ++
          (oppairs r ++ ([false,true,false] ++ ys))) := by
  have ht : 20+6*r = 7+(2*r+(8+(4*r+5))) := by omega
  rw [ht,run_add 7 (2*r+(8+(4*r+5))),aDoubleSeven]
  change run (2*r+(8+(4*r+5)))
    (⟨[false,true,true] ++ (oppairs (q+1) ++ L),false,
       pairs r ++ ([true,true,true] ++ ys),0⟩ : Cfg) = _
  rw [run_add (2*r) (8+(4*r+5)),aTenOppIter]
  change run (8+(4*r+5))
    (⟨oppairs r ++ ([false,true,true] ++ (oppairs (q+1) ++ L)),false,
       [true,true,true] ++ ys,0⟩ : Cfg) = _
  rw [run_add 8 (4*r+5),aTriple8]
  change run (4*r+5)
    (bPop r ([false,true,true] ++ (oppairs (q+1) ++ L))
      ([false,true,false] ++ ys)) = _
  rw [run_add (4*r) 5,bPop_run]
  change run 5
    (⟨[false,true,true] ++ (oppairs (q+1) ++ L),false,
      oppairs r ++ ([false,true,false] ++ ys),1⟩ : Cfg) = _
  rw [aDoubleFive]

def eDoubleTriple (m q r : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+2) ++ [true,true],false,
    pairs q ++ ([true,true,false] ++
      (pairs r ++ ([true,true,true] ++ ys))),4⟩

def doubleTriplePacket (r : Nat) : List Bool :=
  [false,true] ++ (oppairs r ++ [false,true,false])

theorem eDoubleTriple_two (m q r : Nat) (ys : List Bool) :
    run 2 (eDoubleTriple m q r ys) =
      scanStart (q+1) (pairs (m+2) ++ [true,true])
        ([true,true,false] ++ (pairs r ++ ([true,true,true] ++ ys))) := by
  simp [eDoubleTriple,scanStart,run,step,goL,goR,pairs]

theorem eDoubleTriple_toB (m q r : Nat) (ys : List Bool) :
    run (4*q+30+6*r) (eDoubleTriple m q r ys) =
      sweepB m (false :: List.replicate (2*q+6) true ++
        (doubleTriplePacket r ++ ys)) := by
  have ht : 4*q+30+6*r =
    (2+2*(q+1)) + ((20+6*r)+(2*(q+1)+4)) := by omega
  rw [ht,run_add (2+2*(q+1)) ((20+6*r)+(2*(q+1)+4)),
    run_add 2 (2*(q+1)),eDoubleTriple_two,scan_run]
  change run ((20+6*r)+(2*(q+1)+4))
    (⟨oppairs (q+1) ++ (pairs (m+2) ++ [true,true]),false,
      [true,true,false] ++ (pairs r ++ ([true,true,true] ++ ys)),0⟩ : Cfg) = _
  rw [run_add (20+6*r) (2*(q+1)+4),aDoubleTurn,
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
  simp only [doubleTriplePacket,List.append_assoc,List.cons_append,
    List.nil_append,List.replicate_succ,List.replicate_zero]

theorem eDoubleTriple_run (m q r : Nat) (ys : List Bool) :
    run (2*m+4*q+33+6*r) (eDoubleTriple m q r ys) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (false :: List.replicate (2*q+6) true ++
          (doubleTriplePacket r ++ ys)),5⟩ := by
  have ht : 2*m+4*q+33+6*r = (4*q+30+6*r)+(2*m+3) := by omega
  rw [ht,run_add,eDoubleTriple_toB,sweepB_run]

/-- Universal original-machine E return on 0 (10)^q 110 (10)^r 111 ys,
    absorbing two formerly separate fixed-gate families. -/
theorem full_E_double_triple (k q r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+68+4*q+6*r)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ ([true,true,false] ++
          (pairs r ++ ([true,true,true] ++ ys)))))) =
      ⟨[],false,List.replicate (8*k+5) true ++
        (false :: List.replicate (2*q+6) true ++
          (doubleTriplePacket r ++ ys)),5⟩ := by
  have ht : 12*k*k+49*k+68+4*q+6*r =
    (12*k*k+41*k+33)+(2*(4*k+1)+4*q+33+6*r) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k+1)+4*q+33+6*r)
    (eDoubleTriple (4*k+1) q r ys) = _
  rw [eDoubleTriple_run]
  rw [show 2*(4*k+1)+3=8*k+5 by omega]

#print axioms aDoubleSeven
#print axioms aTenOppIter
#print axioms aDoubleFive
#print axioms aDoubleTurn
#print axioms eDoubleTriple_toB
#print axioms full_E_double_triple
end CryptidBoundary
