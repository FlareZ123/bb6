import Lean.Elab.Tactic.Omega
import CryptidPairs
import MarkerTowerSource

namespace BB6.Agent2EAltTurn
open CryptidBoundary
set_option maxHeartbeats 15000000
set_option maxRecDepth 8192

/-- Reverse four-step scanner over the left 01 stack. -/
def reverse (n : Nat) (L ys : List Bool) : Cfg :=
  ⟨oppairs n ++ L,true,true::ys,0⟩

theorem reverse_four (n : Nat) (L ys : List Bool) :
    run 4 (reverse (n+1) L ys) =
      reverse n L ([true,false] ++ ys) := by
  simp [reverse,oppairs,run,step,goL,goR,List.append_assoc]

private theorem pairs_snoc (n : Nat) :
    pairs n ++ [true,false] = [true,false] ++ pairs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [pairs,List.append_assoc] using
      congrArg (fun zs : List Bool => [true,false] ++ zs) ih

theorem reverse_run (n : Nat) (L ys : List Bool) :
    run (4*n) (reverse n L ys) =
      reverse 0 L (pairs n ++ ys) := by
  induction n generalizing ys with
  | zero => rfl
  | succ n ih =>
    have ht : 4*(n+1)=4+4*n := by omega
    rw [ht,run_add,reverse_four,ih]
    apply congrArg (reverse 0 L)
    calc
      _ = (pairs n ++ [true,false]) ++ ys := by simp [List.append_assoc]
      _ = [true,false] ++ (pairs n ++ ys) := by rw [pairs_snoc]; simp [List.append_assoc]
      _ = pairs (n+1) ++ ys := rfl

/-- The initial seven moves of the A turn are independent of the left tape. -/
private theorem front_seven (L zs : List Bool) :
    run 7
      (⟨L,false,[true,true,false,true] ++ zs,0⟩ : Cfg) =
      ⟨[false,true,true] ++ L,false,true::zs,0⟩ := by
  simp [run,step,goL,goR]

/-- Transition from the final 111 token into the reverse scanner. -/
private theorem turn_two (L ys : List Bool) :
    run 2 (⟨L,false,[true,true,true] ++ ys,0⟩ : Cfg) =
      reverse 1 L ys := by
  simp [reverse,oppairs,run,step,goL,goR]

/-- The last seven moves recover the unknown left list and place state C/1. -/
private theorem finish_seven (L zs : List Bool) :
    run 7
      (⟨[false,true,true] ++ L,true,
        [true,true,false] ++ zs,0⟩ : Cfg) =
      ⟨L,true,[true,false,true,false,true,false] ++ zs,2⟩ := by
  simp [run,step,goL,goR]

private theorem a_scan_two (L ys : List Bool) :
    run 2 (⟨L,false,[true,false] ++ ys,0⟩ : Cfg) =
      ⟨[false,true] ++ L,false,ys,0⟩ := by
  simp [run,step,goL,goR]

private theorem a_scan (n : Nat) (L ys : List Bool) :
    run (2*n) (⟨L,false,pairs n ++ ys,0⟩ : Cfg) =
      ⟨oppairs n ++ L,false,ys,0⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have ht : 2*(n+1)=2+2*n := by omega
    rw [ht,run_add]
    change run (2*n)
      (run 2 (⟨L,false,[true,false] ++ (pairs n ++ ys),0⟩ : Cfg)) = _
    rw [a_scan_two]
    have h := ih ([false,true] ++ L)
    simpa [oppairs,List.append_assoc] using h

/-- Source-level A turn across 11(01)^(r+1)11. The left tape and trailing
    right suffix are entirely arbitrary. All 6r+20 primitive moves are exact. -/
theorem turn_all (r : Nat) (L ys : List Bool) :
    run (6*r+20)
      (⟨L,false,[true,true] ++
        (oppairs (r+1) ++ ([true,true] ++ ys)),0⟩ : Cfg) =
      (⟨L,true,pairs (r+3) ++ ys,2⟩ : Cfg) := by
  let U : List Bool := [false,true,true] ++ L
  let V : List Bool := [true,true,true] ++ ys
  have hfront : run 7
      (⟨L,false,[true,true] ++
        (oppairs (r+1) ++ ([true,true] ++ ys)),0⟩ : Cfg) =
        (⟨U,false,pairs r ++ V,0⟩ : Cfg) := by
    have h0 := front_seven L (oppairs r ++ ([true,true] ++ ys))
    have hw : true :: (oppairs r ++ ([true,true] ++ ys)) =
      pairs r ++ V := by
      have h := BB6.Agent2MarkerTower.one_marker r
      simpa [BB6.Agent2MarkerTower.marker,V,List.append_assoc] using
        congrArg (fun zs : List Bool => zs ++ ys) h
    calc
      run 7 (⟨L,false,[true,true] ++
          (oppairs (r+1) ++ ([true,true] ++ ys)),0⟩ : Cfg)
          = run 7
            (⟨L,false,[true,true,false,true] ++
              (oppairs r ++ ([true,true] ++ ys)),0⟩ : Cfg) := by rfl
      _ = ⟨U,false,true :: (oppairs r ++ ([true,true] ++ ys)),0⟩ := by
        simpa only [U] using h0
      _ = ⟨U,false,pairs r ++ V,0⟩ := by rw [hw]
  have hscan : run (2*r)
      (⟨U,false,pairs r ++ V,0⟩ : Cfg) =
      (⟨oppairs r ++ U,false,V,0⟩ : Cfg) :=
    a_scan r U V
  have hturn : run 2
      (⟨oppairs r ++ U,false,V,0⟩ : Cfg) =
      reverse (r+1) U ys := by
    change run 2
      (⟨oppairs r ++ U,false,[true,true,true] ++ ys,0⟩ : Cfg) = _
    rw [turn_two]
    simp [reverse,oppairs,List.append_assoc]
  have hback := reverse_run (r+1) U ys
  have hfinish : run 7 (reverse 0 U (pairs (r+1) ++ ys)) =
      (⟨L,true,pairs (r+3) ++ ys,2⟩ : Cfg) := by
    change run 7
      (⟨[false,true,true] ++ L,true,
        [true,true,false] ++ (pairs r ++ ys),0⟩ : Cfg) = _
    rw [finish_seven]
    simp [pairs,List.append_assoc]
  have ht : 6*r+20 = 7+(2*r+(2+(4*(r+1)+7))) := by omega
  rw [ht,run_add,hfront,run_add,hscan,
      run_add,hturn,run_add,hback,hfinish]

/-- E section immediately after the original E unary-prefix source. -/
def eMany (m q r : Nat) (ys : List Bool) : Cfg :=
  ⟨false :: false :: pairs (m+3) ++ [true,true],false,
    pairs q ++ ([true,true] ++
      (oppairs (r+1) ++ ([true,true] ++ ys))),4⟩

def outputWord (q r : Nat) (ys : List Bool) : List Bool :=
  [true,true] ++
    ([false,true,true,true] ++
      (List.replicate (2*(q+1)) true ++
        (pairs (r+3) ++ ys)))

theorem e_two (m q r : Nat) (ys : List Bool) :
    run 2 (eMany m q r ys) =
      scanStart (q+1) (pairs (m+3) ++ [true,true])
        ([true,true] ++
          (oppairs (r+1) ++ ([true,true] ++ ys))) := by
  simp [eMany,scanStart,run,step,goL,goR,pairs]

theorem e_scan (m q r : Nat) (ys : List Bool) :
    run (2*q+4) (eMany m q r ys) =
      ⟨oppairs (q+1) ++ (pairs (m+3) ++ [true,true]),false,
        [true,true] ++ (oppairs (r+1) ++ ([true,true] ++ ys)),0⟩ := by
  have ht : 2*q+4=2+2*(q+1) := by omega
  rw [ht,run_add,e_two,scan_run]
  rfl

private theorem sweep_two (m : Nat) (ys : List Bool) :
    run 2 (sweepB (m+1) ys) =
      sweepD m ([true,true] ++ ys) := by
  simp [sweepB,sweepD,pairs,run,step,goL,goR]

private theorem tail_six (m q r : Nat) (ys : List Bool) :
    run 6
      (⟨pairs ((m+1)+2) ++ [true,true],true,
        List.replicate (2*(q+1)) true ++
          (pairs (r+3) ++ ys),2⟩ : Cfg) =
      sweepD m (outputWord q r ys) := by
  let zs : List Bool :=
    List.replicate (2*(q+1)) true ++ (pairs (r+3) ++ ys)
  have hb : run 4
      (⟨pairs ((m+1)+2) ++ [true,true],true,zs,2⟩ : Cfg) =
      sweepB (m+1) ([false,true,true,true] ++ zs) :=
    cBase (m+1) zs
  have ht : 6=4+2 := by omega
  rw [ht,run_add]
  change run 2
      (run 4 (⟨pairs ((m+1)+2) ++ [true,true],true,zs,2⟩ : Cfg)) = _
  rw [hb,sweep_two]
  rfl

private theorem a_finish (m q r : Nat) (ys : List Bool) :
    run (2*(q+1)+6)
      (⟨oppairs (q+1) ++ (pairs (m+3) ++ [true,true]),true,
        pairs (r+3) ++ ys,2⟩ : Cfg) =
      sweepD m (outputWord q r ys) := by
  rw [run_add]
  change run 6 (run (2*(q+1))
    (cWalk (q+1) (pairs (m+3) ++ [true,true])
      (pairs (r+3) ++ ys))) = _
  rw [cWalk_run]
  change run 6
    (⟨pairs ((m+1)+2) ++ [true,true],true,
      List.replicate (2*(q+1)) true ++
        (pairs (r+3) ++ ys),2⟩ : Cfg) = _
  exact tail_six m q r ys

theorem e_front (m q r : Nat) (ys : List Bool) :
    run (4*q+6*r+32) (eMany m q r ys) =
      sweepD m (outputWord q r ys) := by
  have ht : 4*q+6*r+32 = (2*q+4)+((6*r+20)+(2*(q+1)+6)) := by omega
  rw [ht,run_add,e_scan]
  rw [run_add,turn_all]
  exact a_finish m q r ys

theorem e_run (m q r : Nat) (ys : List Bool) :
    run (2*m+4*q+6*r+35) (eMany m q r ys) =
      (⟨[],false,List.replicate (2*m+3) true ++
        outputWord q r ys,5⟩ : Cfg) := by
  have ht : 2*m+4*q+6*r+35 = (4*q+6*r+32)+(2*m+3) := by omega
  rw [ht,run_add,e_front,sweepD_run]

/-- Uniform original-machine E packet return for all r>=0, corresponding
    to the suffix 11(01)^(r+1)11, all k,q and arbitrary trailing ys.
    No blank-tape reachability or first-return minimality is claimed. -/
theorem full_E_many (k q r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+68+4*q+6*r)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++
          ([true,true] ++
            (oppairs (r+1) ++ ([true,true] ++ ys)))))) =
      (⟨[],false,List.replicate (8*k+3) true ++
        outputWord q r ys,5⟩ : Cfg) := by
  have ht : 12*k*k+49*k+68+4*q+6*r =
      (12*k*k+41*k+33)+(2*(4*k)+4*q+6*r+35) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k)+4*q+6*r+35) (eMany (4*k) q r ys) = _
  rw [e_run]
  rw [show 2*(4*k)+3=8*k+3 by omega]

#print axioms reverse_run
#print axioms front_seven
#print axioms turn_two
#print axioms finish_seven
#print axioms turn_all
#print axioms e_front
#print axioms full_E_many
end BB6.Agent2EAltTurn
