import MixedCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 500000
namespace F197.MixedCarry
open JCarry

def leadP : Nat → Tape → Tape
  | 0,l => l
  | n+1,l => leadP n (p l)

theorem leadP_comm (n : Nat) (l : Tape) : leadP n (p l) = p (leadP n l) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => exact ih (p l)

theorem inputs_P (n : Nat) (ks : List Token) (l : Tape) :
    inputs (List.replicate n Token.p ++ ks) l = leadP n (inputs ks l) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change p (inputs (List.replicate n Token.p ++ ks) l) = leadP n (p (inputs ks l))
    rw [ih, leadP_comm]

theorem countFlags_P (n : Nat) (ks : List Token) :
    countFlags (List.replicate n Token.p ++ ks) = countFlags ks := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, countFlags, flag, bit, ih]

theorem out_P (n : Nat) (ks : List Token) (v : Bool) (l : Tape) :
    a (h (firstFlag (List.replicate n Token.p ++ ks) v) (outputs (List.replicate n Token.p ++ ks) v l)) =
    leadP n (a (h (firstFlag ks v) (outputs ks v l))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let ws := List.replicate n Token.p ++ ks
    change a (h false (emit Token.p (firstFlag ws v) (outputs ws v l))) = leadP n (p (a (h (firstFlag ks v) (outputs ks v l))))
    rw [leadP_comm, ← ih]
    change a (h false (emit Token.p (firstFlag ws v) (outputs ws v l))) = p (a (h (firstFlag ws v) (outputs ws v l)))
    cases firstFlag ws v <;> rfl

theorem familyP (n : Nat) (ks : List Token) (v : Bool) (l : Tape) (hl : l 0 = true) :
    run (68*n + (74 + 68*ks.length + 14*(countFlags ks+bit v)))
      (b (leadP n (inputs ks (src v [] l))) e) =
    some (b (leadP n (a (h (firstFlag ks v) (outputs ks v l)))) e) := by
  have h0 := family (List.replicate n Token.p ++ ks) v l hl
  rw [inputs_P, out_P, countFlags_P, List.length_append, List.length_replicate] at h0
  rw [show 68*n + (74 + 68*ks.length + 14*(countFlags ks+bit v)) =
      74 + 68*(n+ks.length) + 14*(countFlags ks+bit v) by omega]
  exact h0

#print axioms familyP
end F197.MixedCarry
