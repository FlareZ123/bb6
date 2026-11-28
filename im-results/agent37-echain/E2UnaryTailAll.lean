import Lean.Elab.Tactic.Omega
import EGenericTurn
import PacketSource

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace BB6.Agent37E2UnaryTail
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2EGenericTurn

/-- The fourth bit following the initial 0 111 is a physical branch bit.
    A zero leaves a five-bit alternating tail; a one creates six bits. -/
private def zeroFront : List Bool :=
  [true,true,false,true,true,true,false]

private def oneFront : List Bool :=
  [true,true,false,true,true,true,true]

private def zeroOut : List Bool :=
  [true,true,false] ++ List.replicate 6 true ++
    [false,true,false,true,false]

private def oneOut : List Bool :=
  [true,true,false] ++ List.replicate 6 true ++
    [false,true,false,true,false,true]

/-- Finite original-table computation, independent of the arbitrary
    left pair stack and of the untouched suffix. -/
theorem zeroFront32 (m : Nat) (ys : List Bool) :
    run 32 (eStart m 0 (zeroFront ++ ys)) =
      sweepD m (zeroOut ++ ys) := by
  simp [eStart,zeroFront,zeroOut,sweepD,
    run,step,goL,goR,pairs,List.append_assoc]

theorem oneFront32 (m : Nat) (ys : List Bool) :
    run 32 (eStart m 0 (oneFront ++ ys)) =
      sweepD m (oneOut ++ ys) := by
  simp [eStart,oneFront,oneOut,sweepD,
    run,step,goL,goR,pairs,List.append_assoc]

theorem zeroRun (m : Nat) (ys : List Bool) :
    run (2*m+35) (eStart m 0 (zeroFront ++ ys)) =
      ⟨[],false,List.replicate (2*m+3) true ++ (zeroOut ++ ys),5⟩ := by
  rw [show 2*m+35=32+(2*m+3) by omega,
      run_add,zeroFront32,sweepD_run]

theorem oneRun (m : Nat) (ys : List Bool) :
    run (2*m+35) (eStart m 0 (oneFront ++ ys)) =
      ⟨[],false,List.replicate (2*m+3) true ++ (oneOut ++ ys),5⟩ := by
  rw [show 2*m+35=32+(2*m+3) by omega,
      run_add,oneFront32,sweepD_run]

private theorem repInput (k : Nat) :
    List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
  rw [show 3*k+4=2+(3*k+2) by omega,
      ← List.replicate_append_replicate]
  rfl

private theorem repOutput (k : Nat) :
    List.replicate (8*k+5) true =
      List.replicate (8*k+3) true ++ [true,true] := by
  rw [show 8*k+5=(8*k+3)+2 by omega,
      ← List.replicate_append_replicate]
  rfl

private theorem zeroInput (k : Nat) (ys : List Bool) :
    packet (3*k+4) 0 2
        (false :: true :: true :: true :: false :: ys) =
      init (List.replicate (3*k+2) true ++
        false :: (zeroFront ++ ys)) := by
  rw [show packet (3*k+4) 0 2
      (false :: true :: true :: true :: false :: ys) =
      (⟨[],false,List.replicate (3*k+4) true ++
        (false :: ([true,true,false,true,true,true,false] ++ ys)),5⟩ : Cfg) by
        simp [packet,word,oppairs,List.replicate,List.append_assoc]]
  rw [repInput]
  simp [init,zeroFront,List.append_assoc]

private theorem oneInput (k : Nat) (ys : List Bool) :
    packet (3*k+4) 0 2
        (false :: true :: true :: true :: true :: ys) =
      init (List.replicate (3*k+2) true ++
        false :: (oneFront ++ ys)) := by
  rw [show packet (3*k+4) 0 2
      (false :: true :: true :: true :: true :: ys) =
      (⟨[],false,List.replicate (3*k+4) true ++
        (false :: ([true,true,false,true,true,true,true] ++ ys)),5⟩ : Cfg) by
        simp [packet,word,oppairs,List.replicate,List.append_assoc]]
  rw [repInput]
  simp [init,oneFront,List.append_assoc]

private theorem zeroOutput (k : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*k+3) true ++
      (zeroOut ++ ys),5⟩ : Cfg) =
    packet (8*k+5) 0 6
      ([false,true,false,true,false] ++ ys) := by
  rw [show List.replicate (8*k+3) true ++ (zeroOut ++ ys) =
      (List.replicate (8*k+3) true ++ [true,true]) ++
       (false :: List.replicate 6 true ++
         ([false,true,false,true,false] ++ ys)) by
      simp [zeroOut,List.replicate,List.append_assoc]]
  rw [← repOutput]
  simp [packet,word,oppairs,List.append_assoc]

private theorem oneOutput (k : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*k+3) true ++
      (oneOut ++ ys),5⟩ : Cfg) =
    packet (8*k+5) 0 6
      ([false,true,false,true,false,true] ++ ys) := by
  rw [show List.replicate (8*k+3) true ++ (oneOut ++ ys) =
      (List.replicate (8*k+3) true ++ [true,true]) ++
       (false :: List.replicate 6 true ++
         ([false,true,false,true,false,true] ++ ys)) by
      simp [oneOut,List.replicate,List.append_assoc]]
  rw [← repOutput]
  simp [packet,word,oppairs,List.append_assoc]

/-- Every k and every suffix: q=0, p=2 E boundary with 0 111 0 guard.
    Neither the unary parameter nor the suffix is numerically bounded. -/
theorem e_two_1110 (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+68)
      (packet (3*k+4) 0 2
        (false :: true :: true :: true :: false :: ys)) =
      packet (8*k+5) 0 6
        ([false,true,false,true,false] ++ ys) := by
  rw [zeroInput]
  have ht : 12*k*k+49*k+68 =
    (12*k*k+41*k+33)+(2*(4*k)+35) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k)+35) (eStart (4*k) 0 (zeroFront ++ ys)) = _
  rw [zeroRun]
  rw [show 2*(4*k)+3=8*k+3 by omega]
  exact zeroOutput k ys

/-- Every k and every suffix: q=0, p=2 E boundary with 0 111 1 guard.
    This includes arbitrarily many further ones, not just the fixed 01^6
    section used in the older P2 reset theorem. -/
theorem e_two_1111 (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+68)
      (packet (3*k+4) 0 2
        (false :: true :: true :: true :: true :: ys)) =
      packet (8*k+5) 0 6
        ([false,true,false,true,false,true] ++ ys) := by
  rw [oneInput]
  have ht : 12*k*k+49*k+68 =
    (12*k*k+41*k+33)+(2*(4*k)+35) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k)+35) (eStart (4*k) 0 (oneFront ++ ys)) = _
  rw [oneRun]
  rw [show 2*(4*k)+3=8*k+3 by omega]
  exact oneOutput k ys

/-- Complete binary branch for a q=0 E-two boundary with at least three
    ones after its zero, regardless of the next bit and remaining tape. -/
theorem e_two_111_any (k : Nat) (b : Bool) (ys : List Bool) :
    run (12*k*k+49*k+68)
      (packet (3*k+4) 0 2
        (false :: true :: true :: true :: b :: ys)) =
      packet (8*k+5) 0 6
        ((if b then [false,true,false,true,false,true]
               else [false,true,false,true,false]) ++ ys) := by
  cases b with
  | false => exact e_two_1110 k ys
  | true => exact e_two_1111 k ys

#print axioms zeroFront32
#print axioms oneFront32
#print axioms e_two_1110
#print axioms e_two_1111
#print axioms e_two_111_any

end BB6.Agent37E2UnaryTail
