import Lean.Elab.Tactic.Omega
import E2AlternatingPacket
import E2AlternatingTurn
import E2ShortPositive
import EGenericTurn
import PacketSource

set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
set_option linter.unusedSimpArgs false

namespace BB6.Agent37E2ZeroGuard

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2EGenericTurn
open BB6.Agent37E2AlternatingTurn
open BB6.Agent37E2AlternatingPacket
open BB6.Agent37ShortEPositive

/-- The short *other* A frontier 110011Y is four primitive transitions
    faster than the known 110100Y transition, but has the same D/1 output
    provided by the two trailing one guards. -/
def guardTail : List Bool := [false,false,true,true]

private theorem onesSix (ys : List Bool) :
    List.replicate 4 true ++ ([true,true] ++ ys) =
      List.replicate 6 true ++ ys := by
  rfl

theorem guardedFrontPositive (m q : Nat) (ys : List Bool) :
    run (4*q+28)
      (eStart m (q+1) (aFront 0 ++ (List.replicate 2 true ++ ys))) =
    sweepD m (shortPacket (q+1) ys) := by
  have ht : 4*q+28 =
      (2*(q+1)+4)+(12+(2*(q+1)+8)) := by omega
  rw [ht,run_add,eStart_scan,run_add]
  change run (2*(q+1)+8)
    (run 12 (aStart 0 (oppairs (q+2) ++
      (pairs (m+3) ++ [true,true])) (List.replicate 2 true ++ ys))) = _
  rw [show (12:Nat)=4*0+12 by omega,aTurnAllNat]
  change run (2*(q+1)+8)
    (⟨oppairs (q+2) ++ (pairs (m+3) ++ [true,true]),true,
      List.replicate 4 true ++ (List.replicate 2 true ++ ys),3⟩ : Cfg) = _
  have hs : List.replicate 4 true ++ (List.replicate 2 true ++ ys) =
      List.replicate 6 true ++ ys := by rfl
  rw [hs]
  exact dPositive q m ys

theorem guardedFrontZero (m : Nat) (ys : List Bool) :
    run 60
      (eStart m 0 (aFront 0 ++ (List.replicate 2 true ++ ys))) =
    sweepB m (zeroOut ++ ys) := by
  have hscan : run 4 (eStart m 0
      (aFront 0 ++ (List.replicate 2 true ++ ys))) =
      ⟨oppairs 1 ++ (pairs (m+3) ++ [true,true]),false,
        aFront 0 ++ (List.replicate 2 true ++ ys),0⟩ := by
    simpa using eStart_scan m 0
      (aFront 0 ++ (List.replicate 2 true ++ ys))
  rw [show (60:Nat)=4+(12+44) by omega,run_add,hscan,run_add]
  change run 44
    (run 12 (aStart 0 (oppairs 1 ++
      (pairs (m+3) ++ [true,true])) (List.replicate 2 true ++ ys))) = _
  rw [show (12:Nat)=4*0+12 by omega,aTurnAllNat]
  change run 44
    (⟨oppairs 1 ++ (pairs (m+3) ++ [true,true]),true,
      List.replicate 4 true ++ (List.replicate 2 true ++ ys),3⟩ : Cfg) = _
  have hs : List.replicate 4 true ++ (List.replicate 2 true ++ ys) =
      List.replicate 6 true ++ ys := by rfl
  rw [hs]
  exact dZeroClose44 m ys

private theorem oppairsFalse (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (fun xs : List Bool => false :: true :: xs) ih

private theorem inputShape (k q : Nat) (ys : List Bool) :
    packet (3*k+4) q 2 (guardTail ++ ys) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++
          (aFront 0 ++ (List.replicate 2 true ++ ys)))) := by
  have hn : List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hw : word q 2 (guardTail ++ ys) =
      false :: (pairs q ++
        (aFront 0 ++ (List.replicate 2 true ++ ys))) := by
    simp only [word]
    calc
      _ = (oppairs q ++ [false]) ++
           (List.replicate 2 true ++ (guardTail ++ ys)) := by
             simp [List.append_assoc]
      _ = _ := by
        rw [oppairsFalse]
        simp [aFront,guardTail,oppairs,List.replicate,List.append_assoc]
  simp only [packet,init]
  rw [hw,hn]
  rfl

/-- q>0 source return with tail 0011Y, which is 4 steps faster
    than tail 0100Y but has the same literal endpoint. -/
theorem e_two_0011_positive (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+64+4*q)
      (packet (3*k+4) (q+1) 2 (guardTail ++ ys)) =
    packet (8*k+5) 0 (2*(q+1)+2)
      (false :: List.replicate 8 true ++ ys) := by
  rw [inputShape]
  have ht : 12*k*k+49*k+64+4*q =
      (12*k*k+41*k+33) + ((4*q+28)+(2*(4*k)+3)) := by omega
  rw [ht,run_add,prefix_E]
  change run ((4*q+28)+(2*(4*k)+3))
    (eStart (4*k) (q+1)
      (aFront 0 ++ (List.replicate 2 true ++ ys))) = _
  rw [run_add,guardedFrontPositive,sweepD_run]
  rw [show 2*(4*k)+3=8*k+3 by omega]
  simpa using outputPositive k q 0 ys

/-- q=0 companion of the alternative 0011-guarded E-two frontier. -/
theorem e_two_0011_zero (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+96)
      (packet (3*k+4) 0 2 (guardTail ++ ys)) =
    packet (8*k+3) 0 4 (zeroTail ++ ys) := by
  rw [inputShape]
  have ht : 12*k*k+49*k+96 =
      (12*k*k+41*k+33) + (60+(2*(4*k)+3)) := by omega
  rw [ht,run_add,prefix_E]
  change run (60+(2*(4*k)+3))
    (eStart (4*k) 0
      (aFront 0 ++ (List.replicate 2 true ++ ys))) = _
  rw [run_add,guardedFrontZero,sweepB_run]
  rw [show 2*(4*k)+3=8*k+3 by omega]
  simpa using outputZero k 0 ys

#print axioms guardedFrontPositive
#print axioms guardedFrontZero
#print axioms e_two_0011_positive
#print axioms e_two_0011_zero

end BB6.Agent37E2ZeroGuard
