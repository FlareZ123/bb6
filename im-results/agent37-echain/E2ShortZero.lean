import Lean.Elab.Tactic.Omega
import EGenericTurn
import PacketSource

set_option maxRecDepth 8192
set_option maxHeartbeats 25000000
set_option linter.unusedSimpArgs false

namespace BB6.Agent37ShortEZero

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2EGenericTurn

private def shortFront : List Bool :=
  [true,true,false,true,false,false]

private def zeroOut : List Bool :=
  [false,true,true,true,true,false,true,false,true,false,true,false,true,true]

private def zeroTail : List Bool :=
  [false,true,false,true,false,true,false,true,true]

/-- At the zero-pair boundary the same six-bit guarded E-two frontier
    takes a *different* branch from the positive-pair family: B/0 rather
    than D/0, and 64 local steps rather than 4q+28. -/
theorem shortZeroFront64 (m : Nat) (ys : List Bool) :
    run 64 (eStart m 0 (shortFront ++ ys)) =
      sweepB m (zeroOut ++ ys) := by
  simp [eStart,shortFront,zeroOut,sweepB,
    run,step,goL,goR,pairs,List.append_assoc]

theorem shortZeroRun (m : Nat) (ys : List Bool) :
    run (2*m+67) (eStart m 0 (shortFront ++ ys)) =
      ⟨[],false,List.replicate (2*m+3) true ++ (zeroOut ++ ys),5⟩ := by
  rw [show 2*m+67=64+(2*m+3) by omega,
    run_add,shortZeroFront64,sweepB_run]

private theorem inputShape (k : Nat) (ys : List Bool) :
    packet (3*k+4) 0 2 (false :: true :: false :: false :: ys) =
      init (List.replicate (3*k+2) true ++
        false :: (shortFront ++ ys)) := by
  have hn : List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ←List.replicate_append_replicate]
    rfl
  simp [packet,word,shortFront,init,hn,oppairs,
    List.append_assoc]

private theorem outputShape (k : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*k+3) true ++ (zeroOut ++ ys),5⟩ : Cfg) =
      packet (8*k+3) 0 4 (zeroTail ++ ys) := by
  simp [packet,word,zeroOut,zeroTail,oppairs,List.append_assoc]

/-- Complete source return for the q=0 guarded E-two packet.
    The q=0 and q>0 cases thus exhaust every alternating-stack length,
    but not arbitrary unguarded binary tails. -/
theorem e_two_short_zero (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+100)
      (packet (3*k+4) 0 2
        (false :: true :: false :: false :: ys)) =
      packet (8*k+3) 0 4 (zeroTail ++ ys) := by
  rw [inputShape]
  have ht : 12*k*k+49*k+100 =
      (12*k*k+41*k+33)+(2*(4*k)+67) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k)+67) (eStart (4*k) 0 (shortFront ++ ys)) = _
  rw [shortZeroRun]
  rw [show 2*(4*k)+3=8*k+3 by omega]
  exact outputShape k ys

#print axioms shortZeroFront64
#print axioms shortZeroRun
#print axioms e_two_short_zero

end BB6.Agent37ShortEZero
