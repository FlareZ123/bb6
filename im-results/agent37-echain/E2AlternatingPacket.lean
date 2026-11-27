import Lean.Elab.Tactic.Omega
import E2AlternatingTurn
import E2ShortPositive
import E2ShortZero
import EGenericTurn
import PacketSource

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace BB6.Agent37E2AlternatingPacket

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2EGenericTurn
open BB6.Agent37E2AlternatingTurn
open BB6.Agent37ShortEPositive

/-- An arbitrary positive number of 01 pairs before the two-zero
    terminator. r=0 is precisely the previously certified 0100 frontier. -/
def longTail (r : Nat) (ys : List Bool) : List Bool :=
  oppairs (r+1) ++ ([false,false] ++ ys)

private theorem ones_split (r : Nat) (ys : List Bool) :
    List.replicate (2*(r+1)+4) true ++ ys =
    List.replicate 6 true ++ (List.replicate (2*r) true ++ ys) := by
  have hn : 2*(r+1)+4 = 6+2*r := by omega
  rw [hn, ← List.replicate_append_replicate]
  exact List.append_assoc _ _ _

/-- Complete local E-turn for positive q and an arbitrary alternating
    01 length r+1, using aTurnAll and the unbounded D-stack pump. -/
theorem eLongFrontPositive (m q r : Nat) (ys : List Bool) :
    run (4*q+4*r+32)
      (eStart m (q+1) (aFront (r+1) ++ ys)) =
    sweepD m (shortPacket (q+1)
      (List.replicate (2*r) true ++ ys)) := by
  have ht : 4*q+4*r+32 =
      (2*(q+1)+4) +
      ((4*(r+1)+12)+(2*(q+1)+8)) := by omega
  rw [ht,run_add,eStart_scan,run_add]
  change run (2*(q+1)+8)
    (run (4*(r+1)+12)
      (aStart (r+1) (oppairs (q+2) ++
        (pairs (m+3) ++ [true,true])) ys)) = _
  rw [aTurnAll]
  change run (2*(q+1)+8)
    (⟨oppairs (q+2) ++ (pairs (m+3) ++ [true,true]),true,
      List.replicate (2*(r+1)+4) true ++ ys,3⟩ : Cfg) = _
  rw [ones_split]
  exact dPositive q m (List.replicate (2*r) true ++ ys)

/-- q=0 is a different D-to-B 44-step corridor after the A turn. -/
def zeroOut : List Bool :=
  [false,true,true,true,true,false,true,false,true,false,true,false,true,true]

def zeroTail : List Bool :=
  [false,true,false,true,false,true,false,true,true]

theorem dZeroClose44 (m : Nat) (ys : List Bool) :
    run 44
      (⟨oppairs 1 ++ (pairs (m+3) ++ [true,true]),true,
         List.replicate 6 true ++ ys,3⟩ : Cfg) =
    sweepB m (zeroOut ++ ys) := by
  simp [run,step,goL,goR,oppairs,pairs,sweepB,zeroOut,
    List.append_assoc]

theorem eLongFrontZero (m r : Nat) (ys : List Bool) :
    run (64+4*r)
      (eStart m 0 (aFront (r+1) ++ ys)) =
      sweepB m (zeroOut ++ (List.replicate (2*r) true ++ ys)) := by
  have ht : 64+4*r = 4+((4*(r+1)+12)+44) := by omega
  rw [ht,run_add]
  have hscan : run 4 (eStart m 0 (aFront (r+1) ++ ys)) =
      ⟨oppairs 1 ++ (pairs (m+3) ++ [true,true]),false,
        aFront (r+1) ++ ys,0⟩ := by
    simpa using eStart_scan m 0 (aFront (r+1) ++ ys)
  rw [hscan,run_add]
  change run 44
    (run (4*(r+1)+12)
      (aStart (r+1) (oppairs 1 ++
        (pairs (m+3) ++ [true,true])) ys)) = _
  rw [aTurnAll]
  change run 44
    (⟨oppairs 1 ++ (pairs (m+3) ++ [true,true]),true,
      List.replicate (2*(r+1)+4) true ++ ys,3⟩ : Cfg) = _
  rw [ones_split]
  exact dZeroClose44 m (List.replicate (2*r) true ++ ys)

private theorem oppairsFalse (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simpa [oppairs,pairs,List.append_assoc] using
        congrArg (fun xs : List Bool => false :: true :: xs) ih

private theorem inputShape (k q r : Nat) (ys : List Bool) :
    packet (3*k+4) q 2 (longTail r ys) =
    init (List.replicate (3*k+2) true ++
      false :: (pairs q ++ (aFront (r+1) ++ ys))) := by
  have hn : List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hw : word q 2 (longTail r ys) =
      false :: (pairs q ++ (aFront (r+1) ++ ys)) := by
    simp only [word]
    calc
      _ = (oppairs q ++ [false]) ++
           (List.replicate 2 true ++ longTail r ys) := by
             simp [List.append_assoc]
      _ = _ := by
        rw [oppairsFalse]
        simp [aFront,longTail,List.replicate,List.append_assoc]
  simp only [packet,init]
  rw [hw,hn]
  rfl

theorem outputPositive (k q r : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*k+3) true ++
      (shortPacket (q+1) (List.replicate (2*r) true ++ ys)),5⟩ : Cfg) =
    packet (8*k+5) 0 (2*(q+1)+2)
      (false :: List.replicate (8+2*r) true ++ ys) := by
  have hp : List.replicate (8*k+5) true =
      List.replicate (8*k+3) true ++ [true,true] := by
    rw [show 8*k+5=(8*k+3)+2 by omega,
      ←List.replicate_append_replicate]
    rfl
  have hr : List.replicate 8 true ++
      (List.replicate (2*r) true ++ ys) =
      List.replicate (8+2*r) true ++ ys := by
    rw [←List.replicate_append_replicate]
    rfl
  simp [shortPacket,packet,word,oppairs,hp,List.append_assoc]
  simpa [List.replicate] using hr

theorem outputZero (k r : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*k+3) true ++
      (zeroOut ++ (List.replicate (2*r) true ++ ys)),5⟩ : Cfg) =
    packet (8*k+3) 0 4
      (zeroTail ++ (List.replicate (2*r) true ++ ys)) := by
  simp [packet,word,oppairs,zeroOut,zeroTail,List.append_assoc]

/-- Exact original-source E-two transition for *two* independent,
    unbounded alternating stacks: input q>0 (01)^q before 0 11, and
    r>0 (01)^r before the terminating 00. The binary tail is arbitrary. -/
theorem e_two_double_positive (k q r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+68+4*q+4*r)
      (packet (3*k+4) (q+1) 2 (longTail r ys)) =
    packet (8*k+5) 0 (2*(q+1)+2)
      (false :: List.replicate (8+2*r) true ++ ys) := by
  rw [inputShape]
  have ht : 12*k*k+49*k+68+4*q+4*r =
      (12*k*k+41*k+33) +
        ((4*q+4*r+32)+(2*(4*k)+3)) := by omega
  rw [ht,run_add,prefix_E]
  change run ((4*q+4*r+32)+(2*(4*k)+3))
    (eStart (4*k) (q+1) (aFront (r+1) ++ ys)) = _
  rw [run_add,eLongFrontPositive,sweepD_run]
  rw [show 2*(4*k)+3=8*k+3 by omega]
  exact outputPositive k q r ys

/-- Zero-pair companion of the same double-alternating E-two family. -/
theorem e_two_double_zero (k r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+100+4*r)
      (packet (3*k+4) 0 2 (longTail r ys)) =
    packet (8*k+3) 0 4
      (zeroTail ++ (List.replicate (2*r) true ++ ys)) := by
  rw [inputShape]
  have ht : 12*k*k+49*k+100+4*r =
      (12*k*k+41*k+33) +
        ((64+4*r)+(2*(4*k)+3)) := by omega
  rw [ht,run_add,prefix_E]
  change run ((64+4*r)+(2*(4*k)+3))
    (eStart (4*k) 0 (aFront (r+1) ++ ys)) = _
  rw [run_add,eLongFrontZero,sweepB_run]
  rw [show 2*(4*k)+3=8*k+3 by omega]
  exact outputZero k r ys

#print axioms eLongFrontPositive
#print axioms eLongFrontZero
#print axioms e_two_double_positive
#print axioms e_two_double_zero

end BB6.Agent37E2AlternatingPacket
