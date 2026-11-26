import Raw54DigitSection
set_option maxRecDepth 100000
namespace BB6.Agent8Raw54.BinaryShape
open BB6Coverage.Agent31Pump BB6.Agent8Raw54.DigitSection

theorem shape (xs : List Bool) : (∃ k ys, xs = rep [true] k ++ false::ys) ∨ (∃ k, xs = rep [true] k) := by
  induction xs with
  | nil => exact Or.inr ⟨0,rfl⟩
  | cons x xs ih =>
    cases x
    · exact Or.inl ⟨0,xs,rfl⟩
    · rcases ih with ⟨k,ys,h⟩ | ⟨k,h⟩
      · exact Or.inl ⟨k+1,ys,by simp only [rep,List.cons_append,List.nil_append,h]⟩
      · exact Or.inr ⟨k+1,by simp only [rep,List.cons_append,List.nil_append,h]⟩

theorem enc_append (z o : List Bool) (xs ys : List Bool) : enc z o (xs ++ ys) = enc z o xs ++ enc z o ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [List.cons_append,enc,ih,List.append_assoc]

theorem enc_ones (z o : List Bool) (k : Nat) : enc z o (rep [true] k) = rep o k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rep,List.cons_append,List.nil_append,enc,ih]

theorem enc_zeros (z o : List Bool) (k : Nat) : enc z o (rep [false] k) = rep z k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rep,List.cons_append,List.nil_append,enc,ih]

def ones : List Bool → Nat
  | [] => 0
  | false::xs => ones xs
  | true::xs => ones xs + 1

theorem ones_append (xs ys : List Bool) : ones (xs ++ ys) = ones xs + ones ys := by
  induction xs with
  | nil => simp [ones]
  | cons x xs ih => cases x <;> simp only [List.cons_append,ones,ih] <;> omega

theorem ones_ones (k : Nat) : ones (rep [true] k) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rep,List.cons_append,List.nil_append,ones,ih]

theorem ones_zeros (k : Nat) : ones (rep [false] k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rep,List.cons_append,List.nil_append,ones,ih]
end BB6.Agent8Raw54.BinaryShape
