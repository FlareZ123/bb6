import Lean.Elab.Tactic.Omega
import CryptidTriplePairs
import CryptidPairs
import A1100

namespace BB6.Agent37EAlternatingTriple

open CryptidBoundary

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- Complete shared tail of an arbitrary three-one A terminal. -/
def aWord (r : Nat) (ys : List Bool) : List Bool :=
  [true,true] ++ oppairs (r+2) ++ (false::ys)

def leftAfterSeven (L : List Bool) : List Bool :=
  [false,true,true,false] ++ L

/-- Seven actions expose an arbitrary (10)^r scanner on the right.
    The unknown left tape is preserved behind the four-cell head pattern. -/
theorem a_turn7 (L : List Bool) (r : Nat) (ys : List Bool) :
    run 7
      (⟨false::L, false,
        [true,true,false] ++ pairs r ++ ([true,true,true] ++ ys),0⟩ : Cfg) =
    scanStart r (leftAfterSeven L) ([true,true,true] ++ ys) := by
  simp [leftAfterSeven, scanStart, run, step, goL, goR,
    pairs, List.append_assoc]

/-- B pop of the scanner stack adds one 01 pair on its right. -/
theorem popRight (r : Nat) (ys : List Bool) :
    oppairs r ++ ([false,true,false] ++ ys) =
      oppairs (r+1) ++ (false::ys) := by
  calc
    _ = (oppairs r ++ [false,true]) ++ (false::ys) := by
      simp [List.append_assoc]
    _ = ([false,true] ++ oppairs r) ++ (false::ys) := by
      rw [oppairs_comm_one]
    _ = _ := by simp [oppairs]

/-- Generic six-step B close strips only the four known left bits, returning
    D/0 and leaving every further left and right cell symbolic. -/
theorem close6 (L : List Bool) (r : Nat) (ys : List Bool) :
    run 6
      (⟨leftAfterSeven L, false,
        oppairs (r+1) ++ (false::ys),1⟩ : Cfg) =
      ⟨L,false,aWord r ys,3⟩ := by
  simp [leftAfterSeven,aWord,oppairs,pairs,
    run,step,goL,goR,List.append_assoc]

/-- Universal A/0 transducer on 110(10)^r111, independent of the entire
    unknown left tail.  This is the central all-r 6-step-per-pair lemma. -/
theorem a_turn (L : List Bool) (r : Nat) (ys : List Bool) :
    run (6*r+21)
      (⟨false::L, false,
        [true,true,false] ++ pairs r ++ ([true,true,true] ++ ys),0⟩ : Cfg) =
      ⟨L,false,aWord r ys,3⟩ := by
  have ht : 6*r+21 = 7+(2*r+(8+(4*r+6))) := by omega
  rw [ht,run_add,a_turn7]
  rw [run_add,scan_run]
  rw [run_add,aTriple8]
  rw [run_add]
  change run 6 (run (4*r)
    (bPop r (leftAfterSeven L) ([false,true,false] ++ ys))) = _
  rw [bPop_run,popRight]
  exact close6 L r ys

/-- The first E transition exposes one extra initial 10 pair. -/
def eStart (m q r : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+2) ++ [true,true],false,
    pairs q ++ ([true,true,false] ++ pairs r ++ ([true,true,true] ++ ys)),4⟩

theorem e_two (m q r : Nat) (ys : List Bool) :
    run 2 (eStart m q r ys) =
      scanStart (q+1) (pairs (m+2) ++ [true,true])
        ([true,true,false] ++ pairs r ++ ([true,true,true] ++ ys)) := by
  simp [eStart,scanStart,run,step,goL,goR,pairs,List.append_assoc]

theorem e_scan (m q r : Nat) (ys : List Bool) :
    run (2*q+4) (eStart m q r ys) =
      ⟨oppairs (q+1) ++ (pairs (m+2) ++ [true,true]),false,
        [true,true,false] ++ pairs r ++ ([true,true,true] ++ ys),0⟩ := by
  have ht : 2*q+4 = 2+2*(q+1) := by omega
  rw [ht,run_add,e_two,scan_run]

theorem e_mid (m q r : Nat) (ys : List Bool) :
    run (2*q+6*r+25) (eStart m q r ys) =
      ⟨true :: (oppairs q ++ (pairs (m+2) ++ [true,true])),
        false,aWord r ys,3⟩ := by
  have ht : 2*q+6*r+25 = (2*q+4)+(6*r+21) := by omega
  rw [ht,run_add,e_scan]
  change run (6*r+21)
    (⟨false::(true::(oppairs q ++ (pairs (m+2)++[true,true]))),
      false,[true,true,false] ++ pairs r ++ ([true,true,true] ++ ys),0⟩ : Cfg) = _
  exact a_turn _ r ys

theorem d_to_c (m q r : Nat) (ys : List Bool) :
    run 1
      (⟨true :: (oppairs q ++ (pairs (m+2) ++ [true,true])),
        false,aWord r ys,3⟩ : Cfg) =
      cWalk q (pairs (m+2) ++ [true,true]) (true::aWord r ys) := by
  simp [cWalk,run,step,goL,goR]

def bWord (q r : Nat) (ys : List Bool) : List Bool :=
  [false,true,true,true] ++
    (List.replicate (2*q) true ++ (true::aWord r ys))

theorem e_to_b (m q r : Nat) (ys : List Bool) :
    run (4*q+6*r+30) (eStart m q r ys) =
      sweepB m (bWord q r ys) := by
  have ht : 4*q+6*r+30 = (2*q+6*r+25)+(1+(2*q)+4) := by omega
  rw [ht,run_add,e_mid]
  rw [show 1+2*q+4=1+(2*q+4) by omega,run_add,d_to_c]
  rw [show 2*q+4=(2*q)+4 by omega,run_add,cWalk_run]
  change run 4
    (⟨pairs (m+2) ++ [true,true],true,
      List.replicate (2*q) true ++ (true::aWord r ys),2⟩ : Cfg) = _
  rw [cBase]
  rfl

theorem e_run (m q r : Nat) (ys : List Bool) :
    run (2*m+4*q+6*r+33) (eStart m q r ys) =
      ⟨[],false,List.replicate (2*m+3) true ++ bWord q r ys,5⟩ := by
  have ht : 2*m+4*q+6*r+33 = (4*q+6*r+30)+(2*m+3) := by omega
  rw [ht,run_add,e_to_b,sweepB_run]

/-- The entire packet is 0, followed by exactly 2q+6 ones, then the
    (01)^(r+2) marker and an explicit zero before the arbitrary tail. -/
theorem bWord_shape (q r : Nat) (ys : List Bool) :
    bWord q r ys =
      false :: (List.replicate (2*q+6) true ++
        (oppairs (r+2) ++ (false::ys))) := by
  have hp :
    (List.replicate 3 true ++ List.replicate (2*q) true) ++
      List.replicate 3 true =
      List.replicate (2*q+6) true := by
    rw [List.replicate_append_replicate,List.replicate_append_replicate]
    congr 1
    omega
  unfold bWord aWord
  rw [←hp]
  simp [List.append_assoc]

/-- Exact original-source full six-state F/0 return for all k,q,r,ys:
    I_(3k+4)(0(10)^q 110(10)^r111 ys)
      -> I_(8k+5)(0 1^(2q+6) (01)^(r+2) 0 ys)
    after exactly 12k²+49k+68+4q+6r primitive transitions. -/
theorem full_E_alternating_triple (k q r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+68+4*q+6*r)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++
          ([true,true,false] ++ pairs r ++ ([true,true,true] ++ ys))))) =
      ⟨[],false,List.replicate (8*k+5) true ++
        (false :: (List.replicate (2*q+6) true ++
          (oppairs (r+2) ++ (false::ys)))),5⟩ := by
  have ht : 12*k*k+49*k+68+4*q+6*r =
    (12*k*k+41*k+33)+(2*(4*k+1)+4*q+6*r+33) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k+1)+4*q+6*r+33)
    (eStart (4*k+1) q r ys) = _
  rw [e_run,bWord_shape]
  rw [show 2*(4*k+1)+3=8*k+5 by omega]

#print axioms a_turn7
#print axioms popRight
#print axioms close6
#print axioms a_turn
#print axioms e_to_b
#print axioms e_run
#print axioms bWord_shape
#print axioms full_E_alternating_triple

end BB6.Agent37EAlternatingTriple
