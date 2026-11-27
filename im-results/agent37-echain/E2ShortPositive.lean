import Lean.Elab.Tactic.Omega
import EGenericTurn
import PacketSource

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

namespace BB6.Agent37ShortEPositive

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2EGenericTurn

def shortFront : List Bool :=
  [true,true,false,true,false,false]

def shortPacket (q : Nat) (ys : List Bool) : List Bool :=
  [true,true,false] ++ (List.replicate (2*q+2) true ++
    (false :: List.replicate 8 true ++ ys))

/-- A sixteen-step local turn changes A/0 to D/1, rather than the
    A/0 to C/1 form handled by the earlier EGenericTurn compiler.
    The unknown left tape and subsequent binary suffix are preserved. -/
theorem aShort16 (L ys : List Bool) :
    run 16 (⟨L,false,shortFront ++ ys,0⟩ : Cfg) =
      ⟨L,true,List.replicate 6 true ++ ys,3⟩ := by
  simp [shortFront,run,step,goL,goR,List.append_assoc]

private theorem dTwo (n : Nat) (L ys : List Bool) :
    run 2 (⟨pairs (n+1) ++ L,false,ys,3⟩ : Cfg) =
      ⟨pairs n ++ L,false,[true,true] ++ ys,3⟩ := by
  simp [pairs,run,step,goL,goR,List.append_assoc]

/-- A D/0 sweep of an arbitrary pair stack, leaving the base L intact. -/
theorem dPairsRun (n : Nat) (L ys : List Bool) :
    run (2*n) (⟨pairs n ++ L,false,ys,3⟩ : Cfg) =
      ⟨L,false,List.replicate (2*n) true ++ ys,3⟩ := by
  induction n generalizing ys with
  | zero => simp [pairs,run]
  | succ n ih =>
    have ht : 2*(n+1)=2+2*n := by omega
    rw [ht,run_add,dTwo,ih]
    have hr : List.replicate (2*n) true ++ ([true,true] ++ ys) =
        List.replicate (2*(n+1)) true ++ ys := by
      calc
        _ = (List.replicate (2*n) true ++ List.replicate 2 true) ++ ys := by
          simp [List.append_assoc]
        _ = List.replicate (2*n+2) true ++ ys := by
          rw [List.replicate_append_replicate]
        _ = _ := by
          rw [show 2*n+2=2*(n+1) by omega]
    rw [show 2+2*n=2*(n+1) by omega]
    exact congrArg (fun z : List Bool => Cfg.mk L false z 3) hr

/-- One fixed left-turn step group after scanning the q-dependent stack. -/
private theorem dCloseSeven (m : Nat) (zs : List Bool) :
    run 7 (⟨true :: (pairs (m+3) ++ [true,true]),false,zs,3⟩ : Cfg) =
      sweepD m ([true,true,false,true,true,true,true] ++ zs) := by
  simp [run,step,goL,goR,sweepD,pairs,List.append_assoc]

/-- Base q=1 of the short E-two left-stack grammar. -/
private theorem dBaseTen (m : Nat) (ys : List Bool) :
    run 10
      (⟨oppairs 2 ++ (pairs (m+3) ++ [true,true]),true,
        List.replicate 6 true ++ ys,3⟩ : Cfg) =
      sweepD m (shortPacket 1 ys) := by
  simp [run,step,goL,goR,sweepD,shortPacket,oppairs,pairs,
    List.append_assoc]

private theorem pairRotate (n : Nat) (zs : List Bool) :
    true :: (oppairs n ++ zs) = pairs n ++ (true :: zs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [oppairs,pairs,List.append_assoc] using
        congrArg (fun xs : List Bool => true :: false :: xs) ih

/-- For q>=2, the first five transitions expose an arbitrary D-pair
    stack, which can be removed by dPairsRun before a seven-step close. -/
private theorem dFive (u m : Nat) (ys : List Bool) :
    run 5
      (⟨oppairs (u+3) ++ (pairs (m+3) ++ [true,true]),true,
        List.replicate 6 true ++ ys,3⟩ : Cfg) =
      ⟨pairs u ++ (true :: (pairs (m+3) ++ [true,true])),false,
        [true,true,false] ++ (List.replicate 8 true ++ ys),3⟩ := by
  simp [run,step,goL,goR,oppairs,pairs,List.append_assoc]
  exact pairRotate u _

private theorem dMany (u m : Nat) (ys : List Bool) :
    run (2*(u+2)+8)
      (⟨oppairs (u+3) ++ (pairs (m+3) ++ [true,true]),true,
        List.replicate 6 true ++ ys,3⟩ : Cfg) =
      sweepD m (shortPacket (u+2) ys) := by
  have ht : 2*(u+2)+8=5+(2*u+7) := by omega
  rw [ht,run_add,dFive]
  rw [show 2*u+7=2*u+7 by rfl,run_add]
  rw [dPairsRun,dCloseSeven]
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
              (false :: List.replicate 8 true ++ ys)) := by
                simp [List.replicate,List.append_assoc]
    _ = shortPacket (u+2) ys := by
          rw [hr]
          rfl

/-- All strictly positive q short E-two boundaries are uniformly covered:
    a 16-step A->D local turn, q-dependent D pair scanner, and D sweep. -/
theorem dPositive (q m : Nat) (ys : List Bool) :
    run (2*(q+1)+8)
      (⟨oppairs (q+2) ++ (pairs (m+3) ++ [true,true]),true,
        List.replicate 6 true ++ ys,3⟩ : Cfg) =
      sweepD m (shortPacket (q+1) ys) := by
  cases q with
  | zero => simpa using dBaseTen m ys
  | succ u =>
      simpa [Nat.succ_eq_add_one,Nat.add_assoc] using dMany u m ys

theorem shortEFrontPositive (m q : Nat) (ys : List Bool) :
    run (4*(q+1)+28) (eStart m (q+1) (shortFront ++ ys)) =
      sweepD m (shortPacket (q+1) ys) := by
  have ht : 4*(q+1)+28 =
      (2*(q+1)+4)+(16+(2*(q+1)+8)) := by omega
  rw [ht,run_add,eStart_scan,run_add,aShort16]
  exact dPositive q m ys

private theorem oppairsFalse (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simpa [oppairs,pairs,List.append_assoc] using
        congrArg (fun xs : List Bool => false :: true :: xs) ih

private theorem inputShape (k q : Nat) (ys : List Bool) :
    packet (3*k+4) (q+1) 2 (false :: true :: false :: false :: ys) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs (q+1) ++ (shortFront ++ ys))) := by
  have hn : List.replicate (3*k+4) true =
      true::true::List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hw : oppairs (q+1) ++
      (false :: List.replicate 2 true ++
        (false :: true :: false :: false :: ys)) =
      false :: (pairs (q+1) ++ (shortFront ++ ys)) := by
    calc
      _ = (oppairs (q+1) ++ [false]) ++
            (List.replicate 2 true ++
               (false :: true :: false :: false :: ys)) := by
                simp [List.append_assoc]
      _ = _ := by
            rw [oppairsFalse]
            simp [shortFront,List.replicate,List.append_assoc]
  simp only [packet,word,init,List.replicate_zero,
    List.nil_append,List.cons_append]
  rw [hn,hw]
  rfl

private theorem outputShape (k q : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*k+3) true ++
      (shortPacket (q+1) ys),5⟩ : Cfg) =
      packet (8*k+5) 0 (2*(q+1)+2)
        (false :: List.replicate 8 true ++ ys) := by
  have hn : List.replicate (8*k+5) true =
      List.replicate (8*k+3) true ++ [true,true] := by
    rw [show 8*k+5=(8*k+3)+2 by omega,
      ←List.replicate_append_replicate]
    rfl
  simp [shortPacket,packet,word,oppairs,hn,List.append_assoc]

/-- Complete exact original six-state E-two source return for every
    k>=0 and q>=1 with two explicit zero guard bits after 01, retaining
    all further binary bits. Positive q is essential: q=0 follows another
    branch. -/
theorem e_two_short_positive (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+64+4*(q+1))
      (packet (3*k+4) (q+1) 2
        (false :: true :: false :: false :: ys)) =
      packet (8*k+5) 0 (2*(q+1)+2)
        (false :: List.replicate 8 true ++ ys) := by
  rw [inputShape]
  have ht : 12*k*k+49*k+64+4*(q+1) =
      (12*k*k+41*k+33) +
        ((4*(q+1)+28)+(2*(4*k)+3)) := by omega
  rw [ht,run_add,prefix_E]
  change run ((4*(q+1)+28)+(2*(4*k)+3))
    (eStart (4*k) (q+1) (shortFront ++ ys)) = _
  rw [run_add,shortEFrontPositive,sweepD_run]
  rw [show 2*(4*k)+3=8*k+3 by omega]
  exact outputShape k q ys

#print axioms aShort16
#print axioms dPairsRun
#print axioms dPositive
#print axioms shortEFrontPositive
#print axioms e_two_short_positive

end BB6.Agent37ShortEPositive
