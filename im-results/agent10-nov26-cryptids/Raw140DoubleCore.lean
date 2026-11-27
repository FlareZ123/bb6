import Raw140DoubleLocal
namespace Raw140Double
open BB6BlockFAR Raw140Orbit Raw140Extra
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def Reach (M : Table) (a b : Prim) : Prop := ∃ t, run M t a = some b
theorem Reach.refl (M : Table) (a : Prim) : Reach M a a := ⟨0,rfl⟩
theorem Reach.trans {M : Table} {a b c : Prim} (h : Reach M a b) (g : Reach M b c) : Reach M a c := by
  obtain ⟨m,hm⟩ := h
  obtain ⟨n,hn⟩ := g
  exact ⟨m+n,join hm hn⟩
theorem Reach.ext {M : Table} (hM : Extends M) {a b : Prim} (h : Reach base a b) : Reach M a b := by
  obtain ⟨n,hn⟩ := h
  exact ⟨n,run_ext M hM n a b hn⟩

inductive Tail where
  | s62 | s64 | s6221 | s6421 | s6405 | s62542
  deriving DecidableEq, Repr

def tailWord : Tail → List Sym
  | .s62 => [S 6,S 2]
  | .s64 => [S 6,S 4]
  | .s6221 => [S 6,S 2,S 2,S 1]
  | .s6421 => [S 6,S 4,S 2,S 1]
  | .s6405 => [S 6,S 4,S 0,S 5]
  | .s62542 => [S 6,S 2,S 5,S 4,S 2]

def rho : Tail → Tail
  | .s62 => .s64
  | .s64 => .s6221
  | .s6221 => .s6421
  | .s6421 => .s6405
  | .s6405 => .s62542
  | .s62542 => .s62

def carry : Tail → Nat
  | .s62542 => 1
  | _ => 0

def rank : Tail → Nat
  | .s62 => 0
  | .s64 => 1
  | .s6221 => 2
  | .s6421 => 3
  | .s6405 => 4
  | .s62542 => 5

def word : List Bool → List Sym
  | [] => []
  | b::W => (if b then S 6 else S 4)::word W

def triple : List Bool := [true,false,false]
def trips : Nat → List Bool
  | 0 => []
  | n+1 => triple ++ trips n

theorem word_append (W V : List Bool) : word (W ++ V) = word W ++ word V := by
  induction W with
  | nil => rfl
  | cons b W ih => simp only [List.cons_append,word,ih]
theorem word_four (k : Nat) : word (List.replicate k false) = U 4 k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [word,U,List.replicate_succ,ih]
theorem trips_add (m n : Nat) : trips (m+n) = trips m ++ trips n := by
  induction m with
  | zero => simp [trips]
  | succ m ih => simp [Nat.succ_add,trips,ih,List.append_assoc]

def turn : Nat → Tail → Nat × Tail
  | 0,s => (0,s)
  | k+1,s => (carry s + (turn k (rho s)).1,(turn k (rho s)).2)

theorem one_balance (s : Tail) : 6*carry s + rank (rho s) = rank s + 1 := by
  cases s <;> decide
theorem rank_lt (s : Tail) : rank s < 6 := by cases s <;> decide
theorem turn_balance (k : Nat) (s : Tail) :
    6*(turn k s).1 + rank (turn k s).2 = k + rank s := by
  induction k generalizing s with
  | zero => simp [turn]
  | succ k ih =>
    have h := ih (rho s)
    have h' := one_balance s
    simp only [turn]
    omega
theorem turn_ge_three (k : Nat) (s : Tail) (h : 18 ≤ k) : 3 ≤ (turn k s).1 := by
  have h₁ := turn_balance k s
  have h₂ := rank_lt (turn k s).2
  omega

def EvenStart (R : List Sym) : Prop := ∃ Y, R = S 4::Y ∨ R = S 6::Y
theorem word_tail_even (W : List Bool) (s : Tail) : EvenStart (word W ++ tailWord s) := by
  cases W with
  | nil => cases s <;> exact ⟨_,Or.inr rfl⟩
  | cons b W =>
    cases b
    · exact ⟨_,Or.inl rfl⟩
    · exact ⟨_,Or.inr rfl⟩

theorem forward4 (X R : List Sym) (h : EvenStart R) :
    Reach base (boundary 2 true (S 4::X) (S 4::R))
      (boundary 2 true (S 4::S 5::X) R) := by
  rcases h with ⟨Y,h|h⟩
  · subst R; exact ⟨_,forward4_4 X Y⟩
  · subst R; exact ⟨_,forward4_6 X Y⟩
theorem forward6 (X R : List Sym) (h : EvenStart R) :
    Reach base (boundary 2 true (S 4::X) (S 6::R))
      (boundary 2 true (S 4::S 4::X) R) := by
  rcases h with ⟨Y,h|h⟩
  · subst R; exact ⟨_,forward6_4 X Y⟩
  · subst R; exact ⟨_,forward6_6 X Y⟩
theorem liftDL (X R : List Sym) (h : EvenStart R) :
    Reach base (boundary 3 false (S 6::X) R) (boundary 2 true (S 4::X) R) := by
  rcases h with ⟨Y,h|h⟩
  · subst R; exact ⟨_,lift_4 X Y⟩
  · subst R; exact ⟨_,lift_6 X Y⟩

theorem bounce (W : List Bool) (s : Tail) (X : List Sym) :
    Reach base (boundary 2 true (S 4::X) (word W ++ tailWord s))
      (boundary 3 false (S 5::X) (word W ++ word (trips (carry s)) ++ tailWord (rho s))) := by
  induction W generalizing X with
  | nil =>
    cases s
    · exact ⟨_,tail62 X⟩
    · exact ⟨_,tail64 X⟩
    · exact ⟨_,tail6221 X⟩
    · exact ⟨_,tail6421 X⟩
    · exact ⟨_,tail6405 X⟩
    · exact ⟨_,tail62542 X⟩
  | cons b W ih =>
    cases b
    · have h₁ := forward4 X (word W ++ tailWord s) (word_tail_even W s)
      have h₂ := ih (S 5::X)
      have h₃ := reverse4 X (word W ++ word (trips (carry s)) ++ tailWord (rho s))
      exact Reach.trans (Reach.trans h₁ h₂) ⟨_,h₃⟩
    · have h₁ := forward6 X (word W ++ tailWord s) (word_tail_even W s)
      have h₂ := ih (S 4::X)
      have h₃ := reverse6 X (word W ++ word (trips (carry s)) ++ tailWord (rho s))
      exact Reach.trans (Reach.trans h₁ h₂) ⟨_,h₃⟩

theorem dstep (X : List Sym) (W : List Bool) (s : Tail) :
    Reach base (boundary 3 false (S 6::X) (word W ++ tailWord s))
      (boundary 3 false X (word (false::(W ++ trips (carry s))) ++ tailWord (rho s))) := by
  have h₁ := liftDL X (word W ++ tailWord s) (word_tail_even W s)
  have h₂ := bounce W s X
  have h₃ := stepL base 3 3 false (S 5) (S 4) 3 X
    (word W ++ word (trips (carry s)) ++ tailWord (rho s)) (by rfl)
  have h₄ := Reach.trans (Reach.trans h₁ h₂) ⟨_,h₃⟩
  simpa only [word,word_append,List.append_assoc,List.cons_append,Bool.false_eq_true,ite_false] using h₄

theorem iter_word (k : Nat) (W : List Bool) (c d : Nat) :
    List.replicate k false ++ (false::(W ++ trips c)) ++ trips d =
      List.replicate (k+1) false ++ W ++ trips (c+d) := by
  rw [List.replicate_succ']
  simp only [trips_add,List.append_assoc,List.cons_append,List.nil_append]

theorem dIter (k : Nat) (X : List Sym) (W : List Bool) (s : Tail) :
    Reach base (boundary 3 false (U 6 k ++ X) (word W ++ tailWord s))
      (boundary 3 false X (word (List.replicate k false ++ W ++ trips (turn k s).1) ++ tailWord (turn k s).2)) := by
  induction k generalizing W s with
  | zero => simpa [turn,trips,U] using Reach.refl base (boundary 3 false X (word W ++ tailWord s))
  | succ k ih =>
    have h₁ := dstep (U 6 k ++ X) W s
    have h₂ := ih (false::(W ++ trips (carry s))) (rho s)
    have h₃ := Reach.trans h₁ h₂
    rw [iter_word] at h₃
    simpa only [turn,U,List.replicate_succ,List.cons_append] using h₃

def E (a b : Nat) (Z : List Sym) : Prim :=
  boundary 3 false [] (U 4 a ++ S 6::(U 4 b ++ Z))

theorem dEndE (j : Nat) (Z : List Sym) :
    Reach base (boundary 3 false [S 4] (U 4 (j+1) ++ Z)) (E 1 j Z) := by
  exact ⟨_,dEnd (U 4 j ++ Z)⟩

theorem eStep (a b : Nat) (Z : List Sym) : Reach base (E a (b+2) Z) (E (a+4) b Z) := by
  have h₁ := convert2 a (S 4::S 4::(U 4 b ++ Z))
  have h₂ := eTwo (U 5 (a+2)) (U 4 b ++ Z)
  have h₃ := sweepL base 3 (S 5) (S 4) 3 (a+4) [] (S 6::(U 4 b ++ Z)) (by rfl)
  have h₄ : Reach base (E a (b+2) Z) (boundary 3 false (U 5 (a+4)) (S 6::(U 4 b ++ Z))) :=
    Reach.trans ⟨_,h₁⟩ ⟨_,h₂⟩
  exact Reach.trans h₄ ⟨_,by simpa only [U,E,List.append_nil] using h₃⟩

theorem eIter (j a b : Nat) (Z : List Sym) :
    Reach base (E a (2*j+b) Z) (E (a+4*j) b Z) := by
  induction j generalizing a with
  | zero => simpa using Reach.refl base (E a b Z)
  | succ j ih =>
    rw [show 2*(j+1)+b = 2*j+b+2 by omega, show a+4*(j+1) = a+4+4*j by omega]
    exact Reach.trans (eStep a (2*j+b) Z) (ih (a+4))

theorem eEven (j a : Nat) (Z : List Sym) :
    Reach base (E a (2*j) Z) (boundary 1 true (U 5 (a+4*j+3)) Z) := by
  have h₁ := eIter j a 0 Z
  have h₂ := convert2 (a+4*j) Z
  exact Reach.trans h₁ ⟨_,h₂⟩

theorem eOddLast (a : Nat) (W : List Bool) (s : Tail) :
    Reach base (E a 1 (S 6::S 4::(word W ++ tailWord s)))
      (boundary 3 false [] (U 4 (a+6) ++ word W ++ word (trips (carry s)) ++ tailWord (rho s))) := by
  have h₁ := convert2 a (S 4::S 6::S 4::(word W ++ tailWord s))
  have h₂ := eOne (U 5 (a+2)) (word W ++ tailWord s)
  have h₃ := bounce (false::W) s (U 5 (a+4))
  have h₄ : Reach base (E a 1 (S 6::S 4::(word W ++ tailWord s)))
      (boundary 3 false (U 5 (a+5)) (S 4::(word W ++ word (trips (carry s)) ++ tailWord (rho s)))) :=
    Reach.trans (Reach.trans ⟨_,h₁⟩ ⟨_,h₂⟩) h₃
  have h₅ := sweepL base 3 (S 5) (S 4) 3 (a+5) []
    (S 4::(word W ++ word (trips (carry s)) ++ tailWord (rho s))) (by rfl)
  have h₆ : Reach base (boundary 3 false (U 5 (a+5)) (S 4::(word W ++ word (trips (carry s)) ++ tailWord (rho s))))
      (boundary 3 false [] (U 4 (a+5) ++ S 4::(word W ++ word (trips (carry s)) ++ tailWord (rho s)))) :=
    ⟨_,by simpa only [U,List.append_nil] using h₅⟩
  have h₇ := Reach.trans h₄ h₆
  simpa only [U,List.replicate_succ,List.cons_append,List.append_nil,List.append_assoc,rep_cons] using h₇

#print axioms bounce
#print axioms dIter
#print axioms eEven
#print axioms eOddLast
end Raw140Double
