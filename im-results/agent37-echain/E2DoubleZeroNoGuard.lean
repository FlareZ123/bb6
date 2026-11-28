import Lean.Elab.Tactic.Omega
import E2ShortPositive
import E2AlternatingTurn
import EGenericTurn
import PacketSource

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace BB6.Agent37E2DoubleZeroNoGuard
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2EGenericTurn BB6.Agent37E2AlternatingTurn
open BB6.Agent37ShortEPositive

/-- q>0 after the D/1 sweep, with only four guaranteed ones at the
    original A/0 output. Unlike the earlier shortPacket, no additional
    11 guard is imposed on the arbitrary unknown right suffix. -/
def packetFour (q : Nat) (ys : List Bool) : List Bool :=
  [true,true,false] ++ (List.replicate (2*q+2) true ++
    (false :: List.replicate 6 true ++ ys))

private theorem d4BaseTen (m : Nat) (ys : List Bool) :
    run 10
      (⟨oppairs 2 ++ (pairs (m+3) ++ [true,true]),true,
        List.replicate 4 true ++ ys,3⟩ : Cfg) =
      sweepD m (packetFour 1 ys) := by
  simp [run,step,goL,goR,sweepD,packetFour,oppairs,pairs,
    List.append_assoc]

private theorem pairRotate (n : Nat) (zs : List Bool) :
    true :: (oppairs n ++ zs) = pairs n ++ (true :: zs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [oppairs,pairs,List.append_assoc] using
        congrArg (fun xs : List Bool => true :: false :: xs) ih

private theorem d4Five (u m : Nat) (ys : List Bool) :
    run 5
      (⟨oppairs (u+3) ++ (pairs (m+3) ++ [true,true]),true,
        List.replicate 4 true ++ ys,3⟩ : Cfg) =
      ⟨pairs u ++ (true :: (pairs (m+3) ++ [true,true])),false,
        [true,true,false] ++ (List.replicate 6 true ++ ys),3⟩ := by
  simp [run,step,goL,goR,oppairs,pairs,List.append_assoc]
  exact pairRotate u _

private theorem d4CloseSeven (m : Nat) (zs : List Bool) :
    run 7
      (⟨true :: (pairs (m+3) ++ [true,true]),false,zs,3⟩ : Cfg) =
      sweepD m ([true,true,false,true,true,true,true] ++ zs) := by
  simp [run,step,goL,goR,sweepD,pairs,List.append_assoc]

private theorem d4Many (u m : Nat) (ys : List Bool) :
    run (2*(u+2)+8)
      (⟨oppairs (u+3) ++ (pairs (m+3) ++ [true,true]),true,
        List.replicate 4 true ++ ys,3⟩ : Cfg) =
      sweepD m (packetFour (u+2) ys) := by
  have ht : 2*(u+2)+8=5+(2*u+7) := by omega
  rw [ht,run_add,d4Five]
  rw [show 2*u+7=2*u+7 by rfl,run_add]
  rw [dPairsRun,d4CloseSeven]
  congr 1
  have hr : List.replicate 4 true ++
      (List.replicate (2*u) true ++ List.replicate 2 true) =
      List.replicate (2*(u+2)+2) true := by
    calc
      _ = (List.replicate 4 true ++ List.replicate (2*u) true) ++
            List.replicate 2 true := by rw [List.append_assoc]
      _ = List.replicate (4+2*u) true ++ List.replicate 2 true := by
            rw [List.replicate_append_replicate]
      _ = List.replicate (4+2*u+2) true := by
            rw [List.replicate_append_replicate]
      _ = _ := by rw [show 4+2*u+2=2*(u+2)+2 by omega]
  calc
    _ = [true,true,false] ++
          ((List.replicate 4 true ++
            (List.replicate (2*u) true ++ List.replicate 2 true)) ++
              (false :: List.replicate 6 true ++ ys)) := by
                simp [List.replicate,List.append_assoc]
    _ = packetFour (u+2) ys := by rw [hr]; rfl

theorem d4Positive (q m : Nat) (ys : List Bool) :
    run (2*(q+1)+8)
      (⟨oppairs (q+2) ++ (pairs (m+3) ++ [true,true]),true,
        List.replicate 4 true ++ ys,3⟩ : Cfg) =
      sweepD m (packetFour (q+1) ys) := by
  cases q with
  | zero => simpa using d4BaseTen m ys
  | succ u =>
      simpa [Nat.succ_eq_add_one,Nat.add_assoc] using d4Many u m ys

theorem frontPositive (m q : Nat) (ys : List Bool) :
    run (4*q+28) (eStart m (q+1) (aFront 0 ++ ys)) =
      sweepD m (packetFour (q+1) ys) := by
  have ht : 4*q+28 =
      (2*(q+1)+4)+(12+(2*(q+1)+8)) := by omega
  rw [ht,run_add,eStart_scan,run_add]
  change run (2*(q+1)+8)
    (run 12
      (aStart 0 (oppairs (q+2) ++
        (pairs (m+3) ++ [true,true])) ys)) = _
  rw [show (12:Nat)=4*0+12 by omega,aTurnAllNat]
  change run (2*(q+1)+8)
    (⟨oppairs (q+2) ++ (pairs (m+3) ++ [true,true]),true,
      List.replicate 4 true ++ ys,3⟩ : Cfg) = _
  exact d4Positive q m ys

private theorem oppairsFalse (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (fun xs : List Bool => false :: true :: xs) ih

private theorem inputShape (k q : Nat) (ys : List Bool) :
    packet (3*k+4) (q+1) 2 ([false,false] ++ ys) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs (q+1) ++ (aFront 0 ++ ys))) := by
  have hn : List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hw : word (q+1) 2 ([false,false] ++ ys) =
      false :: (pairs (q+1) ++ (aFront 0 ++ ys)) := by
    simp only [word]
    calc
      _ = (oppairs (q+1) ++ [false]) ++
          (List.replicate 2 true ++ ([false,false] ++ ys)) := by
            simp [List.append_assoc]
      _ = _ := by
        rw [oppairsFalse]
        simp [aFront,List.replicate,oppairs,List.append_assoc]
  simp only [packet,init]
  rw [hw,hn]
  rfl

private theorem outputShape (k q : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*k+3) true ++
      packetFour (q+1) ys,5⟩ : Cfg) =
      packet (8*k+5) 0 (2*(q+1)+2)
        (false :: List.replicate 6 true ++ ys) := by
  have hn : List.replicate (8*k+5) true =
      List.replicate (8*k+3) true ++ [true,true] := by
    rw [show 8*k+5=(8*k+3)+2 by omega,
      ←List.replicate_append_replicate]
    rfl
  simp [packetFour,packet,word,oppairs,hn,List.append_assoc]

/-- No extra '11' lookahead requirement: for EVERY binary suffix after
    00, positive-q E-two returns with an exact original six-state clock.
    The old guarded theorem covered only tails 0011Y. -/
theorem e_two_00_positive (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+64+4*q)
      (packet (3*k+4) (q+1) 2 ([false,false] ++ ys)) =
      packet (8*k+5) 0 (2*(q+1)+2)
        (false :: List.replicate 6 true ++ ys) := by
  rw [inputShape]
  have ht : 12*k*k+49*k+64+4*q =
      (12*k*k+41*k+33) +
        ((4*q+28)+(2*(4*k)+3)) := by omega
  rw [ht,run_add,prefix_E]
  change run ((4*q+28)+(2*(4*k)+3))
    (eStart (4*k) (q+1) (aFront 0 ++ ys)) = _
  rw [run_add,frontPositive,sweepD_run]
  rw [show 2*(4*k)+3=8*k+3 by omega]
  exact outputShape k q ys

#print axioms d4BaseTen
#print axioms d4Many
#print axioms d4Positive
#print axioms frontPositive
#print axioms e_two_00_positive

end BB6.Agent37E2DoubleZeroNoGuard
