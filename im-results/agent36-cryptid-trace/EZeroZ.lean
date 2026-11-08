import Lean.Elab.Tactic.Omega
import MarkerZeroSource
import CryptidPairs

namespace BB6.Agent36EZeroZ
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2MarkerZero
open BB6.Agent2BoundaryBZero
open BB6.BoundaryPadding

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

/-- The first 01 in a nonempty zero-ended marker is absorbed as one
    additional 1 after the exact original E/p=0 return. -/
private theorem input_shape (k q m : Nat) :
    packet (3*k+4) q 0 (marker (m+1)) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ (false :: (true :: marker m)))) := by
  have hn : List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ← List.replicate_append_replicate]
    rfl
  have hw :
      oppairs q ++ (false :: marker (m+1)) =
        false :: (pairs q ++ (false :: (true :: marker m))) := by
    calc
      _ = (oppairs q ++ [false]) ++ marker (m+1) := by
        simp [List.append_assoc]
      _ = (false :: pairs q) ++ marker (m+1) := by
        rw [oppairs_false]
      _ = _ := by
        simp [marker,oppairs,List.append_assoc]
  simp only [packet,word,init,List.replicate_zero,
    List.nil_append,List.cons_append]
  rw [hn,hw]
  rfl

private theorem output_shape (k q m : Nat) :
    (⟨[],false,List.replicate (8*k+5) true ++
      (false :: (List.replicate (2*q+6) true ++
        (true :: marker m))),5⟩ : Cfg) =
      packet (8*k+5) 0 (2*q+7) (marker m) := by
  have hp : List.replicate (2*q+7) true =
      List.replicate (2*q+6) true ++ [true] := by
    rw [show 2*q+7=(2*q+6)+1 by omega,
      ← List.replicate_append_replicate]
    rfl
  simp [packet,word,oppairs,hp,List.append_assoc]

/-- All-parameter, exact original-machine step transformation:
    M(3k+4,q,0;Z_(m+1)) -> M(8k+5,0,2q+7;Z_m).
    This is a Z-marker analogue of the earlier Y-marker E-zero drop. -/
theorem e_zero_drop_Z (k q m : Nat) :
    run (12*k*k+49*k+50+4*q)
      (packet (3*k+4) q 0 (marker (m+1))) =
    packet (8*k+5) 0 (2*q+7) (marker m) := by
  rw [input_shape]
  exact (full_E_pairs k q (true :: marker m)).trans
    (output_shape k q m)

/-- Entire infinite p=0 terminal cylinder q divisible by three and
    positive zero-marker depth reenters the regular L section through
    an original-source physical-tape certificate. No blank-root entry
    is asserted. -/
theorem e_zero_q0_Z_regular (k u m : Nat) :
    ∃ T a r b,
      ObsEq
        (run T (packet (3*k+4) (3*u) 0 (marker (m+1))))
        (regularSection a r b) := by
  let c : BB6.Agent31PacketRank.Packet :=
    ⟨8*k+5,0,2*(3*u)+7⟩
  obtain ⟨T,a,r,b,h⟩ :=
    all_p1_regular m c (by dsimp [c]; omega)
      (by dsimp [c]; omega)
  refine ⟨(12*k*k+49*k+50+4*(3*u))+T,a,r,b,?_⟩
  rw [run_add,e_zero_drop_Z]
  exact h

#print axioms e_zero_drop_Z
#print axioms e_zero_q0_Z_regular

end BB6.Agent36EZeroZ
