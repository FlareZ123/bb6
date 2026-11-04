import Lean.Elab.Tactic.Omega
import E1101010111Pairs

namespace BB6.Agent26EThenB

open CryptidBoundary
open BB6.Agent26E1101010111

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def tail (ys : List Bool) : List Bool :=
  [false,true,false,true,false,true,false,true,false] ++ ys

/-- Normalize the exact encoded E return packet without discarding a
    terminal physical zero when an arbitrary right suffix remains. -/
theorem bWord_shape (q : Nat) (ys : List Bool) :
    bWord q ys =
      false :: (List.replicate (2*q+6) true ++ tail ys) := by
  have hp :
      (List.replicate 3 true ++ List.replicate (2*q) true) ++
      List.replicate 3 true =
      List.replicate (2*q+6) true := by
    rw [List.replicate_append_replicate, List.replicate_append_replicate]
    congr 1
    omega
  unfold bWord wordD tail
  rw [← hp]
  simp [List.append_assoc]

/-- For E index k=3t, its full first return is a B index r=8t+1;
    this exact equality permits the next B return theorem to compose. -/
private theorem e_to_b_section (t q : Nat) (ys : List Bool) :
    (⟨[], false,
      List.replicate (8*(3*t)+5) true ++ bWord q ys,5⟩ : Cfg) =
      init (List.replicate (3*(8*t+1)) true ++
        false :: (List.replicate (2*q+6) true ++ tail ys)) := by
  rw [bWord_shape]
  have hrep : List.replicate (8*(3*t)+5) true =
      true :: true :: List.replicate (3*(8*t+1)) true := by
    have hn : 8*(3*t)+5 = 2+3*(8*t+1) := by omega
    rw [hn]
    calc
      _ = List.replicate 2 true ++ List.replicate (3*(8*t+1)) true := by
            rw [List.replicate_append_replicate]
      _ = _ := by rfl
  rw [hrep]
  rfl

/-- Source-original two consecutive exact return endpoints, from the
    E k=3t exceptional terminal to a B follow-up for any q and suffix. -/
theorem e_then_b (t q : Nat) (ys : List Bool) :
    run ((12*(3*t)*(3*t)+49*(3*t)+80+4*q) +
       (12*(8*t+1)*(8*t+1)+49*(8*t+1)+40))
      (init (List.replicate (3*(3*t)+2) true ++
        false :: (pairs q ++ wordE ys))) =
      ⟨[],false,
        List.replicate (8*(8*t+1)+9) true ++
          (List.replicate (2*q+6) true ++ tail ys),5⟩ := by
  rw [run_add, full_E_1101010111_pairs (3*t) q ys]
  rw [e_to_b_section]
  exact full_B (8*t+1)
    (List.replicate (2*q+6) true ++ tail ys)

/-- Closed two-return equation with simplified polynomial raw time. -/
theorem e_then_b_simplified (t q : Nat) (ys : List Bool) :
    run (876*t*t+731*t+181+4*q)
      (init (List.replicate (9*t+2) true ++
        false :: (pairs q ++ wordE ys))) =
      ⟨[],false,
        List.replicate (64*t+17) true ++
          (List.replicate (2*q+6) true ++ tail ys),5⟩ := by
  have ht : 876*t*t+731*t+181+4*q =
    (12*(3*t)*(3*t)+49*(3*t)+80+4*q) +
    (12*(8*t+1)*(8*t+1)+49*(8*t+1)+40) := by
    have h1 : 12*(3*t)*(3*t) = 108*(t*t) := by
      calc
        _ = (12*3*3)*(t*t) := by ac_rfl
        _ = _ := by rfl
    have h2 : 12*(8*t+1)*(8*t+1) = 768*(t*t)+192*t+12 := by
      calc
        _ = 12*(8*t)*(8*t)+2*12*(8*t)+12 := by
              simp only [Nat.mul_add, Nat.add_mul]
              omega
        _ = (12*8*8)*(t*t)+(2*12*8)*t+12 := by ac_rfl
        _ = _ := by rfl
    rw [h1,h2]
    simp only [Nat.mul_add,Nat.mul_assoc]
    omega
  rw [ht]
  simpa only [show 9*t+2=3*(3*t)+2 by omega,
    show 64*t+17=8*(8*t+1)+9 by omega] using e_then_b t q ys

#print axioms bWord_shape
#print axioms e_then_b
#print axioms e_then_b_simplified

end BB6.Agent26EThenB
