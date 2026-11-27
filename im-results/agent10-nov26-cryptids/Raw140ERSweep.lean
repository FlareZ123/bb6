import Raw140DoubleCore
namespace Raw140ERSweep
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

-- The entire argument uses only the common nine-row table.
theorem one (X Y : List Sym) :
    run base 19 (boundary 4 true (S 1::X) (S 1::Y)) =
      some (boundary 4 true (S 1::S 3::X) Y) := by
  have h₁ := stepR base 4 4 false (S 1) (S 5) 7 (S 1::X) Y (by rfl)
  have h₂ := stepL base 4 3 true (S 1) (S 7) 3 X (S 5::Y) (by rfl)
  have h₃ := stepR base 3 4 false (S 5) (S 5) 1 (S 7::X) Y (by rfl)
  have h₄ := stepL base 4 4 true (S 7) (S 3) 1 X (S 5::Y) (by rfl)
  have h₅ := stepR base 4 4 true (S 5) (S 1) 7 (S 3::X) Y (by rfl)
  exact join (join (join (join h₁ h₂) h₃) h₄) h₅

theorem many (n : Nat) (X Y : List Sym) :
    run base (19*n) (boundary 4 true (S 1::X) (U 1 n ++ Y)) =
      some (boundary 4 true (S 1::(U 3 n ++ X)) Y) := by
  induction n generalizing X with
  | zero => simp [U,run]
  | succ n ih =>
    rw [show 19*(n+1)=19+19*n by omega]
    have h := join (one X (U 1 n ++ Y)) (ih (S 3::X))
    simpa only [ite_true, List.replicate_zero, U,List.replicate_succ,List.cons_append,rep_cons] using h

theorem prepare (p : Nat) (X Y : List Sym) :
    run base (7+3*p) (boundary 4 true (U 3 p ++ X) (S 1::Y)) =
      some (boundary 4 false X (U 1 p ++ S 5::Y)) := by
  have h₁ := stepR base 4 4 false (S 1) (S 5) 7 (U 3 p ++ X) Y (by rfl)
  have h₂ := sweepL base 4 (S 3) (S 1) 3 p X (S 5::Y) (by rfl)
  have h := join h₁ h₂
  simpa only [ite_true, List.replicate_zero, Nat.mul_comm p 3] using h

theorem five (p : Nat) (X Y : List Sym) :
    run base (22*p+15) (boundary 4 true (U 3 p ++ S 5::X) (S 1::Y)) =
      some (boundary 4 true (S 1::S 1::(U 3 p ++ X)) Y) := by
  have h₁ := prepare p (S 5::X) Y
  have h₂ := stepL base 4 4 true (S 5) (S 1) 1 X (U 1 p ++ S 5::Y) (by rfl)
  have h₃ := many p X (S 5::Y)
  have h₄ := stepR base 4 4 true (S 5) (S 1) 7 (S 1::(U 3 p ++ X)) Y (by rfl)
  have h := join (join (join h₁ h₂) h₃) h₄
  simpa only [ite_true, List.replicate_zero, show (7+3*p+1)+19*p+7=22*p+15 by omega] using h

theorem carry (p : Nat) (X Y : List Sym) :
    run base (12+3*(p+1)) (boundary 4 true (U 3 (p+1) ++ S 1::X) (S 1::Y)) =
      some (boundary 4 true (S 3::X) (U 1 (p+1) ++ S 5::Y)) := by
  have h₁ := prepare (p+1) (S 1::X) Y
  have h₂ := stepL base 4 3 true (S 1) (S 7) 3 X (U 1 (p+1) ++ S 5::Y) (by rfl)
  have h₃ := stepR base 3 4 false (S 1) (S 1) 1 (S 7::X) (U 1 p ++ S 5::Y) (by rfl)
  have h₄ := stepL base 4 4 true (S 7) (S 3) 1 X (S 1::(U 1 p ++ S 5::Y)) (by rfl)
  have h := join (join (join h₁ h₂) h₃) h₄
  simpa only [ite_true, List.replicate_zero, U,List.replicate_succ,List.cons_append,show (7+3*(p+1)+3)+1+1=12+3*(p+1) by omega] using h

def oddword : List Bool → List Sym
  | [] => []
  | b::W => (if b then S 3 else S 1)::oddword W

-- Preserve an arbitrary intervening word of 1/3 blocks, rotating one 3
-- across it and converting its terminating 5 into two leading 1s.
theorem rotate (W : List Bool) (p : Nat) (X Y : List Sym) :
    run base (22*(p+1+W.length)+15)
      (boundary 4 true (U 3 (p+1) ++ oddword W ++ S 5::X) (S 1::Y)) =
      some (boundary 4 true (S 1::S 1::(U 3 p ++ oddword W ++ S 3::X)) Y) := by
  induction W generalizing p Y with
  | nil =>
    have h := five (p+1) X Y
    simpa only [ite_true, List.replicate_zero, oddword,List.append_nil,List.nil_append,List.length_nil,Nat.add_zero,U,List.replicate_succ,List.cons_append,rep_cons] using h
  | cons b W ih =>
    cases b
    · have h₁ := carry p (oddword W ++ S 5::X) Y
      have h₃ := many p (S 1::(oddword W ++ S 3::X)) (S 5::Y)
      have h₄ := stepR base 4 4 true (S 5) (S 1) 7
        (S 1::(U 3 p ++ S 1::(oddword W ++ S 3::X))) Y (by rfl)
      have h₅ : run base (22*(1+W.length)+15)
          (boundary 4 true (S 3::(oddword W ++ S 5::X)) (S 1::(U 1 p ++ S 5::Y))) =
          some (boundary 4 true (S 1::S 1::(oddword W ++ S 3::X)) (U 1 p ++ S 5::Y)) := by
        simpa only [ite_true, List.replicate_zero, U,List.replicate_succ,List.cons_append,List.nil_append,Nat.zero_add] using
          (ih 0 (U 1 p ++ S 5::Y))
      have h := join (join (join h₁ h₅) h₃) h₄
      simpa only [ite_true, List.replicate_zero, oddword,Bool.false_eq_true,ite_false,List.length_cons,List.append_assoc,List.cons_append,
        show (12+3*(p+1)+(22*(1+W.length)+15))+19*p+7=22*(p+1+(W.length+1))+15 by omega] using h
    · have h := ih (p+1) Y
      simpa only [ite_true, List.replicate_zero, oddword,ite_true,List.length_cons,List.append_assoc,List.cons_append,
        U,List.replicate_succ,rep_cons,
        show p+1+1+W.length=p+1+(W.length+1) by omega] using h

theorem rotate_one (W : List Bool) (X Y : List Sym) :
    run base (22*(1+W.length)+15)
      (boundary 4 true (S 3::(oddword W ++ S 5::X)) (S 1::Y)) =
      some (boundary 4 true (S 1::S 1::(oddword W ++ S 3::X)) Y) := by
  simpa only [ite_true, List.replicate_zero, U,List.replicate_succ,List.cons_append,List.nil_append,Nat.zero_add] using rotate W 0 X Y

#print axioms one
#print axioms many
#print axioms rotate_one
end Raw140ERSweep
