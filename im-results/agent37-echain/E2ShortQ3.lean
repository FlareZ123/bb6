import Lean.Elab.Tactic.Omega
import EGenericTurn
import PacketSource

set_option maxRecDepth 8192
set_option maxHeartbeats 15000000

namespace BB6.Agent37PacketBoundary

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2EGenericTurn

/-- The short E-two frontier used at the external A_step2 call 54.
    Two explicit trailing zeros guard the local six-bit A/C/D turn. -/
private def shortFront : List Bool :=
  [true,true,false,true,false,false]

private def shortOut : List Bool :=
  [true,true,false] ++ List.replicate 8 true ++
    (false :: List.replicate 8 true)

/-- The exact first forty primitive steps are local: the alternating
    left stack survives as a D-sweep with arbitrary length m. -/
theorem shortEFront40 (m : Nat) (ys : List Bool) :
    run 40 (eStart m 3 (shortFront ++ ys)) =
      sweepD m (shortOut ++ ys) := by
  simp [eStart, shortFront, shortOut, sweepD,
    run, step, goL, goR, pairs, List.append_assoc]

theorem shortERun (m : Nat) (ys : List Bool) :
    run (2*m+43) (eStart m 3 (shortFront ++ ys)) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (shortOut ++ ys),5⟩ := by
  rw [show 2*m+43=40+(2*m+3) by omega,
    run_add,shortEFront40,sweepD_run]

private theorem inputShape (k : Nat) (ys : List Bool) :
    packet (3*k+4) 3 2 (false :: true :: false :: false :: ys) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs 3 ++ (shortFront ++ ys))) := by
  have hn : List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ←List.replicate_append_replicate]
    rfl
  simp [packet,word,shortFront,init,hn,oppairs,pairs,
    List.append_assoc]

private theorem outputShape (k : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*k+3) true ++
      (shortOut ++ ys),5⟩ : Cfg) =
      packet (8*k+5) 0 8
        (false :: List.replicate 8 true ++ ys) := by
  have hn : List.replicate (8*k+5) true =
      List.replicate (8*k+3) true ++ [true,true] := by
    rw [show 8*k+5=(8*k+3)+2 by omega,
      ←List.replicate_append_replicate]
    rfl
  simp [packet,word,shortOut,hn,oppairs,List.append_assoc]

/-- Original six-state source return for the short q=3 E-two cylinder.
    Full binary tail ys is untouched *after two explicit zero guards*.
    This does not assert correctness for the unpadded shorter suffix. -/
theorem e_two_short_q3 (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+76)
      (packet (3*k+4) 3 2
        (false :: true :: false :: false :: ys)) =
      packet (8*k+5) 0 8
        (false :: List.replicate 8 true ++ ys) := by
  rw [inputShape]
  have ht : 12*k*k+49*k+76 =
      (12*k*k+41*k+33)+(2*(4*k)+43) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k)+43) (eStart (4*k) 3 (shortFront ++ ys)) = _
  rw [shortERun]
  rw [show 2*(4*k)+3=8*k+3 by omega]
  exact outputShape k ys

#print axioms shortEFront40
#print axioms shortERun
#print axioms e_two_short_q3

end BB6.Agent37PacketBoundary
