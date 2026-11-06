import Lean.Elab.Tactic.Omega
import AIterDoubleZero
import EGenericTurn

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EOneZero
open CryptidBoundary
open BB6.Agent2EGenericTurn

/-- Exact fixed five-step C/1-to-E/1 close of the marked 01101 left stack. -/
private theorem cFive (L ys : List Bool) :
    run 5
      (⟨[false,true,true,false,true] ++ L,true,ys,2⟩ : Cfg) =
      ⟨L,true,List.replicate 5 true ++ ys,4⟩ := by
  simp [run,step,goL,goR]

private theorem ones_normalize (r : Nat) (ys : List Bool) :
    List.replicate 5 true ++
        (List.replicate (2*r) true ++ (true::ys)) =
      List.replicate (2*r+6) true ++ ys := by
  calc
    _ = (List.replicate 5 true ++ List.replicate (2*r) true) ++
        (List.replicate 1 true ++ ys) := by simp [List.append_assoc]
    _ = (List.replicate (5+2*r) true ++
        List.replicate 1 true) ++ ys := by
      rw [List.replicate_append_replicate]
      simp [List.append_assoc]
    _ = List.replicate ((5+2*r)+1) true ++ ys := by
      rw [List.replicate_append_replicate]
    _ = _ := by rw [show (5+2*r)+1=2*r+6 by omega]

/-- General all-left-tape A/0-to-E/1 turn on 10110(10)^r0 Y.
    It preserves every unknown left tape and the suffix Y, using
    exactly 16+4r original primitive steps for all natural r. -/
theorem a_one_zero_turn (r : Nat) (L ys : List Bool) :
    run (4*r+16)
      (⟨L,false,[true,false,true,true,false] ++
        (pairs r ++ (false::ys)),0⟩ : Cfg) =
      ⟨L,true,List.replicate (2*r+6) true ++ ys,4⟩ := by
  let L1 : List Bool := oppairs 1 ++ L
  let L2 : List Bool := [false,true,true] ++ L1
  let L3 : List Bool := oppairs r ++ L2
  let z : List Bool := pairs r ++ (false::ys)
  have h1 : run 2
      (⟨L,false,[true,false,true,true,false] ++ z,0⟩ : Cfg) =
      ⟨L1,false,[true,true,false] ++ z,0⟩ := by
    dsimp [L1,z]
    simpa [oppairs,List.append_assoc] using
      (aTenOppStep L ([true,true,false] ++ (pairs r ++ (false::ys))))
  have h2 : run 7
      (⟨L1,false,[true,true,false] ++ z,0⟩ : Cfg) =
      ⟨L2,false,z,0⟩ := by
    dsimp [L1,L2,z]
    exact aDoubleSeven 0 L (pairs r ++ (false::ys))
  have h3 : run (2*r)
      (⟨L2,false,z,0⟩ : Cfg) =
      ⟨L3,false,false::ys,0⟩ := by
    dsimp [L3,z]
    exact aTenOppIter r L2 (false::ys)
  have h4 : run 2
      (⟨L3,false,false::ys,0⟩ : Cfg) =
      ⟨L3,true,true::ys,2⟩ := by
    exact BB6.Agent2AIterDoubleZero.aZeroTwo L3 ys
  have h5 : run (2*r)
      (⟨L3,true,true::ys,2⟩ : Cfg) =
      ⟨L2,true,List.replicate (2*r) true ++ (true::ys),2⟩ := by
    dsimp [L3]
    exact cWalk_run r L2 (true::ys)
  have h6 : run 5
      (⟨L2,true,List.replicate (2*r) true ++ (true::ys),2⟩ : Cfg) =
      ⟨L,true,List.replicate (2*r+6) true ++ ys,4⟩ := by
    have hs := cFive L (List.replicate (2*r) true ++ (true::ys))
    have hl : L2=[false,true,true,false,true] ++ L := by rfl
    rw [hl,hs]
    exact congrArg (fun zs : List Bool => (⟨L,true,zs,4⟩ : Cfg))
      (ones_normalize r ys)
  have ht : 4*r+16 = 2+(7+(2*r+(2+(2*r+5)))) := by omega
  rw [ht,run_add,h1]
  rw [run_add,h2]
  rw [run_add,h3]
  rw [run_add,h4]
  rw [run_add,h5]
  exact h6

/-- Fixed original source E/1-to-D/0 closing segment, for every
    size m of the untouched alternating left stack. -/
private theorem eFinishEight (m : Nat) (zs : List Bool) :
    run 8
      (⟨oppairs 1 ++ (pairs (m+3) ++ [true,true]),true,zs,4⟩ : Cfg) =
      sweepD m
        ([true,true,false,true,true,true,true,false] ++ zs) := by
  simp [run,step,goL,goR,pairs,oppairs,sweepD,List.append_assoc]

def eOneStart (m r : Nat) (ys : List Bool) : Cfg :=
  eStart m 0
    ([true,false,true,true,false] ++ (pairs r ++ (false::ys)))

theorem e_one_zero_boundary (m r : Nat) (ys : List Bool) :
    run (2*m+31+4*r) (eOneStart m r ys) =
      ⟨[],false,List.replicate (2*m+3) true ++
        ([true,true,false,true,true,true,true,false] ++
          (List.replicate (2*r+6) true ++ ys)),5⟩ := by
  have ht : 2*m+31+4*r =
      4+((4*r+16)+(8+(2*m+3))) := by omega
  rw [ht,run_add]
  change run ((4*r+16)+(8+(2*m+3)))
    (⟨oppairs 1 ++ (pairs (m+3) ++ [true,true]),false,
      [true,false,true,true,false] ++ (pairs r ++ (false::ys)),0⟩ : Cfg) = _
  rw [run_add,a_one_zero_turn]
  rw [run_add,eFinishEight,sweepD_run]

/-- Original source exact F/0 endpoint on
    I_(3k+4)(0 10110 (10)^r 0 Y), with arbitrary tail Y.
    This supplies the one-initial-pair boundary absent from the
    earlier two-or-more-pairs first-physical-return family. -/
theorem full_one_zero (k r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+64+4*r)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,false,true,true,false] ++
          (pairs r ++ (false::ys))))) =
      ⟨[],false,List.replicate (8*k+3) true ++
        ([true,true,false,true,true,true,true,false] ++
          (List.replicate (2*r+6) true ++ ys)),5⟩ := by
  rw [show 12*k*k+49*k+64+4*r =
    (12*k*k+41*k+33)+(2*(4*k)+31+4*r) by omega,
    run_add,prefix_E]
  change run (2*(4*k)+31+4*r) (eOneStart (4*k) r ys) = _
  rw [e_one_zero_boundary]
  rw [show 2*(4*k)+3=8*k+3 by omega]

#print axioms a_one_zero_turn
#print axioms e_one_zero_boundary
#print axioms full_one_zero
end BB6.Agent2EOneZero
