import Lean.Elab.Tactic.Omega
import CryptidPairs
import PacketSource

set_option maxRecDepth 4096
set_option maxHeartbeats 10000000

namespace BB6.Agent37PacketBoundary

open CryptidBoundary BB6.Agent31PacketSource

private theorem oppairsFalse (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs, pairs, List.append_assoc] using
      congrArg (fun xs : List Bool => false :: true :: xs) ih

private theorem inputShape (k q : Nat) (ys : List Bool) :
    packet (3*k+4) q 0 (false :: true :: ys) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ (false :: true :: ys))) := by
  have hn : List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ← List.replicate_append_replicate]
    rfl
  have hw :
      oppairs q ++ (false :: false :: true :: ys) =
        false :: (pairs q ++ (false :: true :: ys)) := by
    calc
      _ = (oppairs q ++ [false]) ++ (false :: true :: ys) := by
        simp [List.append_assoc]
      _ = _ := by
        rw [oppairsFalse]
        simp [List.append_assoc]
  simp only [packet, word, init, List.replicate_zero,
    List.nil_append, List.cons_append]
  rw [hn, hw]
  rfl

private theorem outputShape (k q : Nat) (ys : List Bool) :
    (⟨[], false, List.replicate (8*k+5) true ++
      (false :: (List.replicate (2*q+6) true ++ (true :: ys))), 5⟩ : Cfg) =
        packet (8*k+5) 0 (2*q+7) ys := by
  have hp : List.replicate (2*q+7) true =
      List.replicate (2*q+6) true ++ [true] := by
    rw [show 2*q+7=(2*q+6)+1 by omega,
      ← List.replicate_append_replicate]
    rfl
  simp [packet, word, oppairs, hp, List.append_assoc]

/-- A literal original-source, arbitrary-binary-tail E/0 packet transition.
    It consumes the initial two-bit marker 01 of Y and converts q alternating
    pairs into 2q+7 ones. No restriction on q or the remaining tail. -/
theorem e_zero_drop_any (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+50+4*q)
      (packet (3*k+4) q 0 (false :: true :: ys)) =
    packet (8*k+5) 0 (2*q+7) ys := by
  rw [inputShape]
  exact (full_E_pairs k q (true :: ys)).trans (outputShape k q ys)

#print axioms e_zero_drop_any

end BB6.Agent37PacketBoundary
