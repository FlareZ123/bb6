import Lean.Elab.Tactic.Omega
import E1101010111ThenB
import CryptidTriplePairs

namespace BB6.Agent26EThenE

open CryptidBoundary
open BB6.Agent26E1101010111
open BB6.Agent26EThenB

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- The extra right packet after the first exceptional E return.
    All bits are preserved, including the final zero in `tail`. -/
def nextSuffix (q : Nat) (ys : List Bool) : List Bool :=
  List.replicate (2*q+3) true ++ tail ys

/-- If the first E parameter is 1 modulo 3, its successor is again
    an E boundary. Three of its forced leading ones start the universal
    E triple-packet theorem. -/
private theorem e_to_e_section (t q : Nat) (ys : List Bool) :
    (⟨[], false,
      List.replicate (8*(3*t+1)+5) true ++ bWord q ys, 5⟩ : Cfg) =
    init (List.replicate (3*(8*t+3)+2) true ++
      false :: (pairs 0 ++ ([true,true,true] ++ nextSuffix q ys))) := by
  rw [bWord_shape]
  have hp : List.replicate (8*(3*t+1)+5) true =
      true :: true :: List.replicate (3*(8*t+3)+2) true := by
    have hn : 8*(3*t+1)+5 = 2+(3*(8*t+3)+2) := by omega
    rw [hn]
    calc
      _ = List.replicate 2 true ++ List.replicate (3*(8*t+3)+2) true := by
        rw [List.replicate_append_replicate]
      _ = _ := by rfl
  have hq : List.replicate (2*q+6) true =
      [true,true,true] ++ List.replicate (2*q+3) true := by
    have hn : 2*q+6=3+(2*q+3) := by omega
    rw [hn]
    rw [←List.replicate_append_replicate]
    rfl
  rw [hp, hq]
  rfl

/-- Two consecutive exact physical F-section endpoints for the
    original D-start machine. The second is an E triple-packet return,
    uniform over k=3t+1, q, and every suffix. -/
theorem e_then_e (t q : Nat) (ys : List Bool) :
    run ((12*(3*t+1)*(3*t+1)+49*(3*t+1)+80+4*q) +
       (12*(8*t+3)*(8*t+3)+49*(8*t+3)+58))
      (init (List.replicate (3*(3*t+1)+2) true ++
        false :: (pairs q ++ wordE ys))) =
      ⟨[], false, List.replicate (8*(8*t+3)+9) true ++
        (oppairs (0+2) ++ false :: nextSuffix q ys),5⟩ := by
  rw [run_add, full_E_1101010111_pairs (3*t+1) q ys]
  rw [e_to_e_section]
  simpa only [Nat.zero_add] using
    (full_E_triple_pairs (8*t+3) 0 (nextSuffix q ys))

/-- Closed polynomial time and complete physical tape, retaining any
    arbitrary nonempty suffix without discarding its preceding zero. -/
theorem e_then_e_polynomial (t q : Nat) (ys : List Bool) :
    run (876*t*t+1187*t+454+4*q)
      (init (List.replicate (9*t+5) true ++
        false :: (pairs q ++ wordE ys))) =
      ⟨[],false,List.replicate (64*t+33) true ++
        (oppairs 2 ++ false :: nextSuffix q ys),5⟩ := by
  have ht :
      (12*(3*t+1)*(3*t+1)+49*(3*t+1)+80+4*q) +
      (12*(8*t+3)*(8*t+3)+49*(8*t+3)+58) =
      876*t*t+1187*t+454+4*q := by
    have h1 : t*(3*t)=3*(t*t) := by ac_rfl
    have h2 : t*(8*t)=8*(t*t) := by ac_rfl
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,h1,h2]
    omega
  have hs := e_then_e t q ys
  rw [←ht]
  simpa only [show 9*t+5=3*(3*t+1)+2 by omega,
    show 64*t+33=8*(8*t+3)+9 by omega,
    Nat.zero_add] using hs

#print axioms e_then_e
#print axioms e_then_e_polynomial

end BB6.Agent26EThenE
