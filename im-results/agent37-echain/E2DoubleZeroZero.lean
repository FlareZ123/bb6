import Lean.Elab.Tactic.Omega
import E2DoubleZeroNoGuard

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

namespace BB6.Agent37E2DoubleZeroZero
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2EGenericTurn BB6.Agent37E2AlternatingTurn

/-- With zero alternating pairs, four ones suffice for the D-to-B
    turnaround. The old proof required two gratuitous 11 lookahead bits. -/
def zeroOutFour : List Bool :=
  [false,true,true,true,true,false,true,false,true,false,true,false]

theorem d4ZeroClose44 (m : Nat) (ys : List Bool) :
    run 44
      (⟨oppairs 1 ++ (pairs (m+3) ++ [true,true]),true,
        List.replicate 4 true ++ ys,3⟩ : Cfg) =
    sweepB m (zeroOutFour ++ ys) := by
  simp [run,step,goL,goR,oppairs,pairs,sweepB,zeroOutFour,
    List.append_assoc]

theorem frontZero (m : Nat) (ys : List Bool) :
    run 60 (eStart m 0 (aFront 0 ++ ys)) =
      sweepB m (zeroOutFour ++ ys) := by
  have hscan : run 4 (eStart m 0 (aFront 0 ++ ys)) =
      ⟨oppairs 1 ++ (pairs (m+3) ++ [true,true]),false,
        aFront 0 ++ ys,0⟩ := by
    simpa using eStart_scan m 0 (aFront 0 ++ ys)
  rw [show (60:Nat)=4+(12+44) by omega,run_add,hscan,run_add]
  change run 44
    (run 12
      (aStart 0 (oppairs 1 ++
        (pairs (m+3) ++ [true,true])) ys)) = _
  rw [show (12:Nat)=4*0+12 by omega,aTurnAllNat]
  change run 44
    (⟨oppairs 1 ++ (pairs (m+3) ++ [true,true]),true,
      List.replicate 4 true ++ ys,3⟩ : Cfg) = _
  exact d4ZeroClose44 m ys

private theorem inputShapeZero (k : Nat) (ys : List Bool) :
    packet (3*k+4) 0 2 ([false,false] ++ ys) =
      init (List.replicate (3*k+2) true ++
        false :: (aFront 0 ++ ys)) := by
  have hn : List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ←List.replicate_append_replicate]
    rfl
  simp [packet,word,oppairs,init,aFront,hn,List.append_assoc]

private theorem outputShapeZero (k : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*k+3) true ++
      (zeroOutFour ++ ys),5⟩ : Cfg) =
    packet (8*k+3) 0 4
      ([false,true,false,true,false,true,false] ++ ys) := by
  simp [packet,word,oppairs,zeroOutFour,List.append_assoc]

/-- q=0 all-suffix source result. No need to inspect a single bit of ys. -/
theorem e_two_00_zero (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+96)
      (packet (3*k+4) 0 2 ([false,false] ++ ys)) =
    packet (8*k+3) 0 4
      ([false,true,false,true,false,true,false] ++ ys) := by
  rw [inputShapeZero]
  have ht : 12*k*k+49*k+96 =
      (12*k*k+41*k+33) + (60+(2*(4*k)+3)) := by omega
  rw [ht,run_add,prefix_E]
  change run (60+(2*(4*k)+3))
    (eStart (4*k) 0 (aFront 0 ++ ys)) = _
  rw [run_add,frontZero,sweepB_run]
  rw [show 2*(4*k)+3=8*k+3 by omega]
  exact outputShapeZero k ys

/-- Both distinct physical 00 corridors, with all k,q and all tails. -/
def allTime (k q : Nat) : Nat :=
  match q with
  | 0 => 12*k*k+49*k+96
  | q+1 => 12*k*k+49*k+64+4*q

def allOut (k q : Nat) (ys : List Bool) : Cfg :=
  match q with
  | 0 => packet (8*k+3) 0 4
      ([false,true,false,true,false,true,false] ++ ys)
  | q+1 => packet (8*k+5) 0 (2*(q+1)+2)
      (false :: List.replicate 6 true ++ ys)

theorem e_two_00_all (k q : Nat) (ys : List Bool) :
    run (allTime k q)
      (packet (3*k+4) q 2 ([false,false] ++ ys)) =
    allOut k q ys := by
  cases q with
  | zero => exact e_two_00_zero k ys
  | succ q => exact BB6.Agent37E2DoubleZeroNoGuard.e_two_00_positive k q ys

#print axioms d4ZeroClose44
#print axioms frontZero
#print axioms e_two_00_zero
#print axioms e_two_00_all
end BB6.Agent37E2DoubleZeroZero
