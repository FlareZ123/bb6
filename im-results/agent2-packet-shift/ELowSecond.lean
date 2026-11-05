import Lean.Elab.Tactic.Omega
import CryptidPairs

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

namespace BB6.Agent2E1101010111

open CryptidBoundary

/-- E zero boundary with q alternating pairs and the ten-bit 1101010111 tail. -/
def eZig (m q : Nat) (ys : List Bool) : Cfg :=
  ⟨false :: false :: pairs (m+3) ++ [true,true], false,
    pairs q ++ ([true,true,false,true,false,true,false,true,true,true] ++ ys), 4⟩

/-- The unsimplified output packet, suitable for direct source lemma rewrites. -/
def zigPacket (q : Nat) (ys : List Bool) : List Bool :=
  [true,true] ++
    ([false,true,true,true] ++
      (List.replicate (2*(q+1)) true ++
        ([true,false,true,false,true,false,true,false,true,false] ++ ys)))

theorem eZig_two (m q : Nat) (ys : List Bool) :
    run 2 (eZig m q ys) =
      scanStart (q+1) (pairs (m+3) ++ [true,true])
        ([true,true,false,true,false,true,false,true,true,true] ++ ys) := by
  simp [eZig, scanStart, run, step, goL, goR, pairs]

theorem eZig_scan (m q : Nat) (ys : List Bool) :
    run (2*q+4) (eZig m q ys) =
      ⟨oppairs (q+1) ++ (pairs (m+3) ++ [true,true]), false,
        [true,true,false,true,false,true,false,true,true,true] ++ ys, 0⟩ := by
  have ht : 2*q+4 = 2+2*(q+1) := by omega
  rw [ht, run_add, eZig_two, scan_run]
  rfl

/-- Finite 32-step A/C turn checked directly against the literal source table:
    this 32-step turn. is independent of the entire unknown left tape. -/
theorem a1101010111_turn32 (L ys : List Bool) :
    run 32 (⟨L,false,[true,true,false,true,false,true,false,true,true,true] ++ ys,0⟩ : Cfg) =
      ⟨L,true,[true,false,true,false,true,false,true,false,true,false] ++ ys,2⟩ := by
  simp [run, step, goL, goR]

/-- A B-on-zero stack sweep consumes a single rightward pair in two steps. -/
theorem sweepB_two (m : Nat) (ys : List Bool) :
    run 2 (sweepB (m+1) ys) =
      sweepD m ([true,true] ++ ys) := by
  simp [sweepB, sweepD, pairs, run, step, goL, goR]

/-- The proved C-on-one 4-step base and a 2-step B-prefix join the D sweep. -/
theorem cTailSix (m q : Nat) (ys : List Bool) :
    run 6
      (⟨pairs ((m+1)+2) ++ [true,true], true,
          List.replicate (2*(q+1)) true ++
            ([true,false,true,false,true,false,true,false,true,false] ++ ys),2⟩ : Cfg) =
      sweepD m (zigPacket q ys) := by
  let zs : List Bool :=
    List.replicate (2*(q+1)) true ++
      ([true,false,true,false,true,false,true,false,true,false] ++ ys)
  have hbase :
      run 4 (⟨pairs ((m+1)+2) ++ [true,true],true,zs,2⟩ : Cfg) =
        sweepB (m+1) ([false,true,true,true] ++ zs) :=
    cBase (m+1) zs
  have ht : 6 = 4+2 := by omega
  rw [ht,run_add]
  change run 2 (run 4 (⟨pairs ((m+1)+2) ++ [true,true],true,zs,2⟩ : Cfg)) = _
  rw [hbase,sweepB_two]
  rfl

theorem aZig_finish (m q : Nat) (ys : List Bool) :
    run (2*q+40)
      (⟨oppairs (q+1) ++ (pairs (m+3) ++ [true,true]), false,
        [true,true,false,true,false,true,false,true,true,true] ++ ys, 0⟩ : Cfg) =
      sweepD m (zigPacket q ys) := by
  have ht : 2*q+40 = 32+(2*(q+1)+6) := by omega
  rw [ht,run_add,a1101010111_turn32]
  rw [show 2*(q+1)+6 = 2*(q+1)+6 by rfl, run_add]
  change run 6 (run (2*(q+1))
    (cWalk (q+1) (pairs (m+3) ++ [true,true])
      ([true,false,true,false,true,false,true,false,true,false] ++ ys))) = _
  rw [cWalk_run]
  change run 6
    (⟨pairs ((m+1)+2) ++ [true,true], true,
       List.replicate (2*(q+1)) true ++
         ([true,false,true,false,true,false,true,false,true,false] ++ ys),2⟩ : Cfg) = _
  exact cTailSix m q ys

/-- An all-q E-turn identity from exact source sweeps. -/
theorem eZig_front (m q : Nat) (ys : List Bool) :
    run (4*q+44) (eZig m q ys) =
      sweepD m (zigPacket q ys) := by
  have ht : 4*q+44 = (2*q+4)+(2*q+40) := by omega
  rw [ht,run_add,eZig_scan]
  exact aZig_finish m q ys

theorem eZig_run (m q : Nat) (ys : List Bool) :
    run (2*m+4*q+47) (eZig m q ys) =
      ⟨[],false,List.replicate (2*m+3) true ++ zigPacket q ys,5⟩ := by
  have ht : 2*m+4*q+47 = (4*q+44)+(2*m+3) := by omega
  rw [ht,run_add,eZig_front,sweepD_run]

/-- Exact all-k,all-q,all-suffix endpoint on the original six-state rule table.
    Original-source Lean CI and axiom audit required. -/
theorem full_E_1101010111_pairs_raw (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+80+4*q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ ([true,true,false,true,false,true,false,true,true,true] ++ ys)))) =
      ⟨[],false,List.replicate (8*k+3) true ++ zigPacket q ys,5⟩ := by
  have ht : 12*k*k+49*k+80+4*q =
    (12*k*k+41*k+33)+(2*(4*k)+4*q+47) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k)+4*q+47) (eZig (4*k) q ys) = _
  rw [eZig_run]
  rw [show 2*(4*k)+3 = 8*k+3 by omega]

#print axioms a1101010111_turn32
#print axioms sweepB_two
#print axioms cTailSix
#print axioms aZig_finish
#print axioms full_E_1101010111_pairs_raw

end BB6.Agent2E1101010111
