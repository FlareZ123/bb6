import ABridgeTwo
import Lean.Elab.Tactic.Omega

namespace BB6.Agent36
open CryptidA (wordCode wordInc wordCost)

theorem code_append (a b : List Bool) : wordCode (a ++ b) = wordCode a ++ wordCode b := by
  induction a with
  | nil => rfl
  | cons hd tail ih => cases hd <;> simp [wordCode, ih]

theorem code_false (q : Nat) : wordCode (List.replicate q false) = CryptidBoundary.pairs q := by
  induction q with
  | zero => rfl
  | succ q ih => simp [wordCode, CryptidBoundary.pairs, ih, List.replicate_succ]

theorem code_true (r : Nat) : wordCode (List.replicate r true) = List.replicate (3*r) true := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ, wordCode, ih]
    rw [show 3*(r+1) = 3+3*r by omega, ← List.replicate_append_replicate]
    rfl

theorem inc_append (a b : List Bool) : wordInc (a ++ b) = wordInc a + wordInc b := by
  induction a with
  | nil => simp [wordInc]
  | cons hd tail ih => cases hd <;> simp [wordInc, ih] <;> omega

theorem inc_false (q : Nat) : wordInc (List.replicate q false) = q := by
  induction q with
  | zero => rfl
  | succ q ih => simp [wordInc, ih, List.replicate_succ] <;> omega

theorem inc_true (r : Nat) : wordInc (List.replicate r true) = 4*r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [wordInc, ih, List.replicate_succ] <;> omega

theorem cost_append (m : Nat) (a b : List Bool) :
    wordCost m (a ++ b) = wordCost m a + wordCost (m+wordInc a) b := by
  induction a generalizing m with
  | nil => simp [wordCost, wordInc]
  | cons hd tail ih =>
    cases hd <;> simp [wordCost, wordInc, ih, Nat.add_assoc]

theorem cost_false (m q : Nat) : wordCost m (List.replicate q false) = 2*q := by
  induction q generalizing m with
  | zero => rfl
  | succ q ih =>
    simp only [List.replicate_succ, wordCost]
    rw [ih]
    omega

theorem cost_true (m r : Nat) :
    wordCost m (List.replicate r true) = 12*r*r + (6*m+29)*r := by
  induction r generalizing m with
  | zero => simp [wordCost]
  | succ r ih =>
    simp only [List.replicate_succ,wordCost]
    rw [ih]
    simp only [Nat.mul_add, Nat.add_mul]
    omega

def tokens (q r : Nat) : List Bool :=
  List.replicate q false ++ List.replicate r true

def extra (q r : Nat) : List Bool := tokens q r ++ [false]

theorem inc_tokens (q r : Nat) : wordInc (tokens q r) = q+4*r := by
  simp [tokens, inc_append, inc_false, inc_true]

theorem inc_extra (q r : Nat) : wordInc (extra q r) = q+4*r+1 := by
  simp [extra, inc_append, inc_tokens, wordInc]

theorem cost_tokens (k q r : Nat) :
  wordCost (4*k+3) (tokens q r) =
    2*q + 12*r*r + (24*k+6*q+47)*r := by
  simp only [tokens,cost_append, cost_false, inc_false, cost_true]
  have hm : 6*(4*k+3+q)+29 = 24*k+6*q+47 := by omega
  rw [hm]
  omega

theorem cost_extra (k q r : Nat) :
  wordCost (4*k+3) (extra q r) =
    2*q + 12*r*r + (24*k+6*q+47)*r+2 := by
  simp only [extra,cost_append,cost_tokens,inc_tokens]
  simp [wordCost]

theorem code_tokens (q r : Nat) :
  wordCode (tokens q r) = CryptidBoundary.pairs q ++ List.replicate (3*r) true := by
  simp [tokens,code_append,code_false,code_true]

theorem code_extra (q r : Nat) :
  wordCode (extra q r) ++ [false] =
  CryptidBoundary.pairs q ++ List.replicate (3*r+1) true ++ [false,false] := by
  have hp : List.replicate (3*r+1) true = List.replicate (3*r) true ++ [true] := by
    rw [← List.replicate_append_replicate]; rfl
  simp only [extra, code_append, code_tokens, wordCode, hp, List.append_assoc]
  rfl

theorem time_extra (k q r : Nat) :
  (12*k*k+41*k+32) +
    (wordCost (4*k+3) (extra q r) +
      (2*((4*k+3)+wordInc (extra q r))+6)) =
  12*k*k+49*k+48+4*q+12*r*r+(24*k+55+6*q)*r := by
  rw [cost_extra, inc_extra]
  simp only [Nat.add_mul]
  omega

theorem time_double (k q r : Nat) :
  (12*k*k+41*k+32) +
    (wordCost (4*k+3) (tokens q r) +
      (2*((4*k+3)+wordInc (tokens q r))+16)) =
  12*k*k+49*k+54+4*q+12*r*r+(24*k+55+6*q)*r := by
  rw [cost_tokens, inc_tokens]
  simp only [Nat.add_mul]
  omega

theorem count_extra (k q r : Nat) :
  2*((4*k+3)+wordInc (extra q r))+5 = 8*k+13+2*q+8*r := by
  rw [inc_extra]
  omega

theorem count_double (k q r : Nat) :
  2*((4*k+3)+wordInc (tokens q r))+1 = 8*k+7+2*q+8*r := by
  rw [inc_tokens]
  omega

theorem code_extra_suffix (q r : Nat) (ys : List Bool) :
  wordCode (extra q r) ++ (false::ys) =
    CryptidBoundary.pairs q ++ (List.replicate (3*r+1) true ++ (false::false::ys)) := by
  have h := congrArg (fun xs : List Bool => xs ++ ys) (code_extra q r)
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using h

theorem code_double_suffix (q r : Nat) (ys : List Bool) :
  wordCode (tokens q r) ++ ([true,true,false,false] ++ ys) =
    CryptidBoundary.pairs q ++ (List.replicate (3*r+2) true ++ (false::false::ys)) := by
  rw [code_tokens]
  have hp : List.replicate (3*r+2) true = List.replicate (3*r) true ++ [true,true] := by
    rw [← List.replicate_append_replicate]; rfl
  rw [hp]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Exact original-machine A extra-10 return for arbitrary binary suffixes.
    This is a special case of Agent 35's source-certified coded A return. -/
theorem full_A_extra10 (k q r : Nat) (ys : List Bool) :
    CryptidBoundary.run
      (12*k*k+49*k+48+4*q+12*r*r+(24*k+55+6*q)*r)
      (CryptidBoundary.init
        (List.replicate (3*k+1) true ++
          false :: (CryptidBoundary.pairs q ++
            (List.replicate (3*r+1) true ++ (false::false::ys))))) =
      ⟨[], false, List.replicate (8*k+13+2*q+8*r) true ++ ys, 5⟩ := by
  have h := BB6.Agent35.full_A_code k (extra q r) ys
  rw [time_extra, count_extra, code_extra_suffix] at h
  exact h

/-- Exact original-machine A/E gate for arbitrary binary suffixes.
    This is a special case of Agent 35's source-certified 1100 return. -/
theorem full_A_E_pairs (k q r : Nat) (ys : List Bool) :
    CryptidBoundary.run
      (12*k*k+49*k+54+4*q+12*r*r+(24*k+55+6*q)*r)
      (CryptidBoundary.init
        (List.replicate (3*k+1) true ++
          false :: (CryptidBoundary.pairs q ++
            (List.replicate (3*r+2) true ++ (false::false::ys))))) =
      ⟨[], false,
        List.replicate (8*k+7+2*q+8*r) true ++
          (false :: List.replicate 6 true ++ ys), 5⟩ := by
  have h := BB6.Agent35.full_A_code_double k (tokens q r) ys
  rw [time_double, count_double, code_double_suffix] at h
  exact h

#print axioms full_A_extra10
#print axioms full_A_E_pairs
end BB6.Agent36
