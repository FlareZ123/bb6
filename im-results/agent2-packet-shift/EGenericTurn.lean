import Lean.Elab.Tactic.Omega
import CryptidPairs

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EGenericTurn
open CryptidBoundary

/-- An E-boundary with q alternating pairs and an arbitrary right frontier. -/
def eStart (m q : Nat) (zs : List Bool) : Cfg :=
  ⟨false::false::pairs (m+3) ++ [true,true], false, pairs q ++ zs, 4⟩

/-- The output packet for any A->C local turnaround. -/
def outPacket (q : Nat) (out ys : List Bool) : List Bool :=
  [true,true] ++ ([false,true,true,true] ++
    (List.replicate (2*(q+1)) true ++ (out ++ ys)))

theorem eStart_two (m q : Nat) (zs : List Bool) :
    run 2 (eStart m q zs) =
      scanStart (q+1) (pairs (m+3) ++ [true,true]) zs := by
  simp [eStart, scanStart, run, step, goL, goR, pairs]

theorem eStart_scan (m q : Nat) (zs : List Bool) :
    run (2*q+4) (eStart m q zs) =
      ⟨oppairs (q+1) ++ (pairs (m+3) ++ [true,true]), false, zs, 0⟩ := by
  have ht : 2*q+4 = 2+2*(q+1) := by omega
  rw [ht,run_add,eStart_two,scan_run]
  rfl

private theorem sweepB_two (m : Nat) (zs : List Bool) :
    run 2 (sweepB (m+1) zs) =
      sweepD m ([true,true] ++ zs) := by
  simp [sweepB, sweepD, pairs, run, step, goL, goR]

private theorem cFinish (m q : Nat) (out ys : List Bool) :
    run 6
      (⟨pairs ((m+1)+2) ++ [true,true], true,
          List.replicate (2*(q+1)) true ++ (out ++ ys),2⟩ : Cfg) =
      sweepD m (outPacket q out ys) := by
  let zs : List Bool := List.replicate (2*(q+1)) true ++ (out ++ ys)
  have hbase :
      run 4 (⟨pairs ((m+1)+2) ++ [true,true],true,zs,2⟩ : Cfg) =
        sweepB (m+1) ([false,true,true,true] ++ zs) :=
    cBase (m+1) zs
  rw [show (6:Nat)=4+2 by rfl,run_add]
  change run 2 (run 4 (⟨pairs ((m+1)+2) ++ [true,true],true,zs,2⟩ : Cfg)) = _
  rw [hbase,sweepB_two]
  rfl

/-- Universal E-boundary compiler. One fixed finite A/0-to-C/1
    turn that never touches the unknown left tape yields an all-q E
    return with the same arbitrary suffix. -/
theorem eFront (m q N : Nat) (front out ys : List Bool)
    (hTurn : ∀ L : List Bool,
      run N (⟨L,false,front ++ ys,0⟩ : Cfg) =
        ⟨L,true,out ++ ys,2⟩) :
    run (4*q+N+12) (eStart m q (front ++ ys)) =
      sweepD m (outPacket q out ys) := by
  have ht : 4*q+N+12 = (2*q+4)+(N+(2*(q+1)+6)) := by omega
  rw [ht,run_add,eStart_scan]
  rw [run_add]
  rw [hTurn]
  rw [show 2*(q+1)+6 = 2*(q+1)+6 by rfl,run_add]
  change run 6 (run (2*(q+1))
    (cWalk (q+1) (pairs (m+3) ++ [true,true]) (out ++ ys))) = _
  rw [cWalk_run]
  change run 6
    (⟨pairs ((m+1)+2) ++ [true,true], true,
       List.replicate (2*(q+1)) true ++ (out ++ ys),2⟩ : Cfg) = _
  exact cFinish m q out ys

/-- Every finite local A/C turn uniformly generates a genuine E return
    from the original six-state F-on-zero source, at exact primitive time.
    No finite cut-off on k,q or the untouched right-hand suffix. -/
theorem full_E_from_turn (k q N : Nat) (front out ys : List Bool)
    (hTurn : ∀ L : List Bool,
      run N (⟨L,false,front ++ ys,0⟩ : Cfg) =
        ⟨L,true,out ++ ys,2⟩) :
    run (12*k*k+49*k+N+48+4*q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ (front ++ ys)))) =
      ⟨[],false,List.replicate (8*k+3) true ++ outPacket q out ys,5⟩ := by
  have ht : 12*k*k+49*k+N+48+4*q =
    (12*k*k+41*k+33)+(2*(4*k)+4*q+N+15) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k)+4*q+N+15) (eStart (4*k) q (front++ys)) = _
  have hs := eFront (4*k) q N front out ys hTurn
  have hn : 2*(4*k)+4*q+N+15 = (4*q+N+12)+(2*(4*k)+3) := by omega
  rw [hn,run_add,hs,sweepD_run]
  rw [show 2*(4*k)+3 = 8*k+3 by omega]

#print axioms eStart_scan
#print axioms eFront
#print axioms full_E_from_turn
end BB6.Agent2EGenericTurn
