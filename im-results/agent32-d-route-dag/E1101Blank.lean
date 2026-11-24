import Boundary
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 15000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent32E1101Blank
open CryptidBoundary

/-- The terminal 1101 is followed by the physically implicit all-blank tail. -/
def eStart (m q : Nat) : Cfg :=
  ⟨[false,false] ++ pairs (m+3) ++ [true,true],false,
    pairs q ++ [true,true,false,true],4⟩

def packet0 : List Bool :=
  [false,true,true,true,true,false,true,false,true,false,true,false,true,true]

def packet (q : Nat) : List Bool :=
  [false] ++ List.replicate (2*q+2) true ++ [false] ++ List.replicate 8 true

/-- Zero-pair branch has a distinct fixed turn. -/
theorem zero_front (m : Nat) : run 64 (eStart m 0) = preB m packet0 := by
  simp [eStart,packet0,preB,run,step,goL,goR,pairs]

theorem zero_return (m : Nat) : run (2*m+67) (eStart m 0) =
    ⟨[],false,List.replicate (2*m+3) true ++ packet0,5⟩ := by
  rw [show 2*m+67 = 64+(2*m+3) by omega,run_add,zero_front,preB_run]

/-- The initial two steps expose the existing arbitrary-length scan. -/
theorem scan_two (m q : Nat) : run 2 (eStart m q) =
    scanStart (q+1) (pairs (m+3) ++ [true,true]) [true,true,false,true] := by
  simp [eStart,scanStart,run,step,goL,goR,pairs]

theorem scan_done (m q : Nat) : run (2*q+4) (eStart m q) =
    ⟨oppairs (q+1) ++ pairs (m+3) ++ [true,true],false,[true,true,false,true],0⟩ := by
  rw [show 2*q+4 = 2+2*(q+1) by omega,run_add,scan_two,scan_run]
  simp [scanDone,List.append_assoc]

/-- Two scanned pairs suffice for a fixed turn on the exact blank tail. -/
theorem turn20 (r : Nat) (L : List Bool) :
    run 20 (⟨oppairs (r+2) ++ L,false,[true,true,false,true],0⟩ : Cfg) =
    ⟨oppairs r ++ L,true,[true,false] ++ List.replicate 8 true,2⟩ := by
  simp [run,step,goL,goR,oppairs]

def cWalk (r : Nat) (L ys : List Bool) : Cfg :=
  ⟨oppairs r ++ L,true,ys,2⟩

theorem cWalk_two (r : Nat) (L ys : List Bool) :
    run 2 (cWalk (r+1) L ys) = cWalk r L (true::true::ys) := by
  simp [cWalk,run,step,goL,goR,oppairs]

theorem cWalk_run (r : Nat) (L ys : List Bool) :
    run (2*r) (cWalk r L ys) =
    ⟨L,true,List.replicate (2*r) true ++ ys,2⟩ := by
  induction r generalizing ys with
  | zero => simp [cWalk,run,oppairs]
  | succ r ih =>
    rw [show 2*(r+1) = 2+2*r by omega,run_add,cWalk_two,ih]
    have hh : List.replicate (2*r) true ++ (true::true::ys) =
        List.replicate (2*(r+1)) true ++ ys := by
      rw [show 2*(r+1) = 2*r+2 by omega,← List.replicate_append_replicate]
      simp [List.append_assoc]
    rw [hh,show 2+2*r = 2*(r+1) by omega]

theorem cTurn4 (m : Nat) (ys : List Bool) :
    run 4 (⟨pairs (m+3) ++ [true,true],true,ys,2⟩ : Cfg) =
    preB (m+1) ([false,true,true,true] ++ ys) := by
  simp [preB,run,step,goL,goR,pairs]

theorem packet_shape (r : Nat) :
    [false,true,true,true] ++ (List.replicate (2*r) true ++
      ([true,false] ++ List.replicate 8 true)) = packet (r+1) := by
  unfold packet
  simp only [List.cons_append,List.nil_append]
  have h : true :: true :: true :: (List.replicate (2*r) true ++
      true :: false :: List.replicate 8 true) =
      List.replicate (2*(r+1)+2) true ++ false :: List.replicate 8 true := by
    rw [show 2*(r+1)+2 = 3+2*r+1 by omega,
      ← List.replicate_append_replicate,← List.replicate_append_replicate]
    simp [List.append_assoc]
  simpa [List.append_assoc] using congrArg (List.cons false) h

/-- Uniform exact endpoint for all positive pair counts. -/
theorem positive_front (m r : Nat) :
    run (4*(r+1)+26) (eStart m (r+1)) = preB (m+1) (packet (r+1)) := by
  rw [show 4*(r+1)+26 = (2*(r+1)+4)+(20+(2*r+4)) by omega,
    run_add,scan_done,run_add]
  rw [show r+1+1 = r+2 by omega]
  rw [List.append_assoc]
  rw [turn20,run_add]
  change run 4 (run (2*r) (cWalk r (pairs (m+3) ++ [true,true])
    ([true,false] ++ List.replicate 8 true))) = _
  rw [cWalk_run,cTurn4,packet_shape]

theorem positive_return (m r : Nat) :
    run (2*m+31+4*(r+1)) (eStart m (r+1)) =
    ⟨[],false,List.replicate (2*m+5) true ++ packet (r+1),5⟩ := by
  rw [show 2*m+31+4*(r+1) = (4*(r+1)+26)+(2*(m+1)+3) by omega,
    run_add,positive_front,preB_run]
  rw [show 2*(m+1)+3 = 2*m+5 by omega]

theorem full_zero (k : Nat) :
    run (12*k*k+49*k+100)
      (init (List.replicate (3*k+2) true ++ false :: [true,true,false,true])) =
    ⟨[],false,List.replicate (8*k+3) true ++ packet0,5⟩ := by
  rw [show 12*k*k+49*k+100 = (12*k*k+41*k+33)+(2*(4*k)+67) by omega,
    run_add,prefix_E]
  change run (2*(4*k)+67) (eStart (4*k) 0) = _
  rw [zero_return,show 2*(4*k)+3 = 8*k+3 by omega]

theorem full_positive (k r : Nat) :
    run (12*k*k+49*k+64+4*(r+1))
      (init (List.replicate (3*k+2) true ++ false ::
        (pairs (r+1) ++ [true,true,false,true]))) =
    ⟨[],false,List.replicate (8*k+5) true ++ packet (r+1),5⟩ := by
  rw [show 12*k*k+49*k+64+4*(r+1) =
      (12*k*k+41*k+33)+(2*(4*k)+31+4*(r+1)) by omega,
    run_add,prefix_E]
  change run (2*(4*k)+31+4*(r+1)) (eStart (4*k) (r+1)) = _
  rw [positive_return,show 2*(4*k)+5 = 8*k+5 by omega]

#print axioms full_zero
#print axioms full_positive
end BB6.Agent32E1101Blank
