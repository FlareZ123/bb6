import Lean.Elab.Tactic.Omega
import EZeroPair
import EDoubleTripleGeneral

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EZeroPump
open CryptidBoundary
open BB6.Agent32EZero

/-- E-boundary with an arbitrary run of 10 pairs in the exceptional 1100 exit. -/
def extended (m r : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+3) ++ [true,true], false,
    [true,true,false] ++ (pairs r ++ (false::ys)),4⟩

private def left11 (m : Nat) : List Bool :=
  (run 11 (eZero m [])).l

private theorem extended11 (m r : Nat) (ys : List Bool) :
    run 11 (extended m r ys) =
      ⟨left11 m,false,pairs r ++ (false::ys),0⟩ := by
  simp [extended,left11,eZero,run,step,goL,goR,pairs,List.append_assoc]

private theorem ordinary11 (m : Nat) (ys : List Bool) :
    run 11 (eZero m ys) =
      ⟨left11 m,false,false::ys,0⟩ := by
  simp [left11,eZero,run,step,goL,goR,pairs,List.append_assoc]

/-- A 10-token scanner followed by the reverse C sweep leaves the
    unknown left tape invariant while turning r tokens into 2r ones. -/
private theorem pair_pump (r : Nat) (L ys : List Bool) :
    run (4*r+2)
      (⟨L,false,pairs r ++ (false::ys),0⟩ : Cfg) =
    ⟨L,true,List.replicate (2*r) true ++ (true::ys),2⟩ := by
  have ht : 4*r+2 = 2*r+(2+2*r) := by omega
  rw [ht,run_add,aTenOppIter]
  rw [run_add]
  have h2 : run 2
      (⟨oppairs r ++ L,false,false::ys,0⟩ : Cfg) =
    ⟨oppairs r ++ L,true,true::ys,2⟩ := by
      simp [run,step,goL,goR]
  rw [h2]
  change run (2*r) (cWalk r L (true::ys)) = _
  rw [cWalk_run]

private theorem ones_shuffle (n : Nat) (ys : List Bool) :
    List.replicate n true ++ (true::ys) =
      true :: (List.replicate n true ++ ys) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [List.replicate_succ] using congrArg (List.cons true) ih

theorem compare13 (m r : Nat) (ys : List Bool) :
    run (4*r+13) (extended m r ys) =
      run 13 (eZero m (List.replicate (2*r) true ++ ys)) := by
  have h1 := extended11 m r ys
  have h2 := ordinary11 m (List.replicate (2*r) true ++ ys)
  have h3 := pair_pump r (left11 m) ys
  rw [show 4*r+13 = 11+(4*r+2) by omega,run_add,h1,h3]
  rw [show 13 = 11+2 by omega,run_add,h2]
  simpa [run,step,goL,goR] using (ones_shuffle (2*r) ys)

/-- General exceptional source gate. All r produce the same fixed
    packetZero, followed by exactly 2r additional ones. -/
theorem extended_front (m r : Nat) (ys : List Bool) :
    run (4*r+60) (extended m r ys) =
      sweepB m (packetZero ++ (List.replicate (2*r) true ++ ys)) := by
  rw [show 4*r+60 = (4*r+13)+47 by omega,run_add,compare13]
  rw [← run_add]
  exact eZero_front m (List.replicate (2*r) true ++ ys)

/-- Source-connected complete raw F/0 return for the exceptional
    E suffix 0 110 (10)^r 0 Y, for all k,r and arbitrary Y.
    No blank-orbit reachability or first-return minimality is asserted. -/
theorem full_exceptional_pump (k r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+96+4*r)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,true,false] ++ (pairs r ++ (false::ys))))) =
    ⟨[],false,List.replicate (8*k+3) true ++
      (packetZero ++ (List.replicate (2*r) true ++ ys)),5⟩ := by
  rw [show 12*k*k+49*k+96+4*r =
    (12*k*k+41*k+33)+((4*r+60)+(2*(4*k)+3)) by omega,
    run_add,prefix_E]
  change run ((4*r+60)+(2*(4*k)+3))
    (extended (4*k) r ys) = _
  rw [run_add,extended_front,sweepB_run]
  rw [show 2*(4*k)+3 = 8*k+3 by omega]

#print axioms extended_front
#print axioms full_exceptional_pump
end BB6.Agent2EZeroPump
