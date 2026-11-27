import Raw14042MixedLocal
namespace Raw14042Mixed
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw14042Counter Raw14042CounterLocal Raw14042MixedLocal
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

def mixedWord (W : List Bool) (s : Tail) := word W ++ tailWord s
def rotateWord (W : List Bool) (s : Tail) := word W ++ word (trips (carry s)) ++ tailWord (rho s)

theorem front (X R : List Sym) (h : EvenStart R) :
    Reach base (boundary 4 true (S 2::X) (S 3::S 4::S 6::R))
      (boundary 2 true (S 4::S 5::S 2::S 6::X) R) := by
  rcases h with ⟨Y,h|h⟩
  · subst R; exact ⟨_,front44 X Y⟩
  · subst R; exact ⟨_,front46 X Y⟩

theorem scanFour (m : Nat) (X : List Sym) (W : List Bool) (s : Tail) :
    Reach base (boundary 4 true (S 2::X) (S 3::(U 2 m ++ S 4::S 6::mixedWord W s)))
      (boundary 1 false X (U 2 m ++ S 2::S 5::S 4::S 4::rotateWord W s)) := by
  let Z := U 6 m ++ X
  have h0 := scanTwo m X (S 4::S 6::mixedWord W s)
  have h1 := front Z (mixedWord W s) (word_tail_even W s)
  have h2 := bounce W s (S 5::S 2::S 6::Z)
  have h3 : Reach base (boundary 3 false (S 5::S 5::S 2::S 6::Z) (rotateWord W s))
      (boundary 1 false Z (S 2::S 5::S 4::S 4::rotateWord W s)) := ⟨_,back4 Z (rotateWord W s)⟩
  have h4 := sweepL base 1 (S 6) (S 2) 3 m X (S 2::S 5::S 4::S 4::rotateWord W s) (by rfl)
  have h5 : Reach base (boundary 1 false Z (S 2::S 5::S 4::S 4::rotateWord W s))
      (boundary 1 false X (U 2 m ++ S 2::S 5::S 4::S 4::rotateWord W s)) := ⟨_,h4⟩
  exact Reach.trans (Reach.trans (Reach.trans (Reach.trans h0 h1) h2) h3) h5

theorem scanFive (m : Nat) (X Y : List Sym) :
    Reach base (boundary 4 true (S 2::X) (S 3::(U 2 m ++ S 5::S 4::Y)))
      (boundary 1 false X (U 2 m ++ S 2::S 2::S 4::S 6::Y)) := by
  have h0 := scanTwo m X (S 5::S 4::Y)
  have h1 : Reach base (boundary 4 true (S 2::(U 6 m ++ X)) (S 3::S 5::S 4::Y))
      (boundary 1 false (U 6 m ++ X) (S 2::S 2::S 4::S 6::Y)) := ⟨_,front5 (U 6 m ++ X) Y⟩
  have h2 := sweepL base 1 (S 6) (S 2) 3 m X (S 2::S 2::S 4::S 6::Y) (by rfl)
  exact Reach.trans (Reach.trans h0 h1) ⟨_,h2⟩

def P (m : Nat) (X : List Sym) (W : List Bool) (s : Tail) : Prim :=
  boundary 4 true (S 2::S 7::X) (S 3::(U 2 m ++ S 4::S 6::mixedWord W s))

theorem addRotate (W : List Bool) (s : Tail) :
    S 4::rotateWord W s = mixedWord (false::(W ++ trips (carry s))) (rho s) := by
  simp only [rotateWord,mixedWord,word,word_append,List.append_assoc,List.cons_append,Bool.false_eq_true,ite_false]

theorem pair (m : Nat) (X : List Sym) (W : List Bool) (s : Tail) :
    Reach base (P (m+1) (S 3::S 3::X) W s)
      (P (m+2) X (false::(W ++ trips (carry s))) (rho s)) := by
  let Z := rotateWord W s
  have h0 := scanFour (m+1) (S 7::S 3::S 3::X) W s
  have h1 := finishStep (S 3::X) (U 2 m ++ S 5::S 4::S 4::Z)
  have h2 := scanFive (m+1) (S 7::S 3::X) (S 4::Z)
  have h3 := finishStep X (U 2 (m+1) ++ S 4::S 6::S 4::Z)
  have e : U 2 (m+1) ++ S 2::S 5::S 4::S 4::Z = S 2::S 2::(U 2 m ++ S 5::S 4::S 4::Z) := by
    simp only [U,List.replicate_succ,List.cons_append,rep_cons]
  change Reach base (P (m+1) (S 3::S 3::X) W s) (boundary 1 false (S 7::S 3::S 3::X) (U 2 (m+1) ++ S 2::S 5::S 4::S 4::Z)) at h0
  rw [e] at h0
  have hh : Reach base (P (m+1) (S 3::S 3::X) W s)
      (boundary 4 true (S 2::S 7::S 3::X) (S 3::(U 2 (m+1) ++ S 5::S 4::S 4::Z))) := by
    exact Reach.trans h0 ⟨_,h1⟩
  rw [two_shift] at h2
  have hh' := Reach.trans hh h2
  have hfinal := Reach.trans hh' (⟨_,h3⟩ : Reach base _ _)
  simpa only [P,Z,U,List.replicate_succ,List.cons_append,addRotate] using hfinal

theorem pairs (k m : Nat) (X : List Sym) (W : List Bool) (s : Tail) :
    Reach base (P (m+1) (U 3 (2*k) ++ X) W s)
      (P (m+1+k) X (List.replicate k false ++ W ++ trips (Raw140Double.turn k s).1) (Raw140Double.turn k s).2) := by
  induction k generalizing m W s with
  | zero => simpa [U,Raw140Double.turn,trips] using Reach.refl base (P (m+1) X W s)
  | succ k ih =>
    have h0 := pair m (U 3 (2*k) ++ X) W s
    have h1 := ih (m+1) (false::(W ++ trips (carry s))) (rho s)
    have h := Reach.trans h0 h1
    rw [iter_word] at h
    simpa only [U, List.replicate_succ,List.cons_append,Raw140Double.turn,
      show 2*(k+1)=2*k+2 by omega, show m+1+1+k=m+1+(k+1) by omega] using h

theorem depleteEven (m : Nat) (W : List Bool) (s : Tail) :
    Reach base (P (m+1) [S 2] W s)
      (boundary 1 false [] (U 2 (m+4) ++ S 4::S 6::mixedWord (false::(W ++ trips (carry s))) (rho s))) := by
  let Z := rotateWord W s
  have h0 := scanFour (m+1) [S 7,S 2] W s
  have e : U 2 (m+1) ++ S 2::S 5::S 4::S 4::Z = S 2::S 2::(U 2 m ++ S 5::S 4::S 4::Z) := by
    simp only [U,List.replicate_succ,List.cons_append,rep_cons]
  change Reach base (P (m+1) [S 2] W s) (boundary 1 false [S 7,S 2] (U 2 (m+1) ++ S 2::S 5::S 4::S 4::Z)) at h0
  rw [e] at h0
  have h1 := finishZero (U 2 m ++ S 5::S 4::S 4::Z)
  have h2 := scanFive (m+1) [S 6] (S 4::Z)
  have h := Reach.trans (Reach.trans h0 (⟨_,h1⟩ : Reach base _ _)) h2
  have h3 := stepL base 1 1 false (S 6) (S 2) 3 [] (U 2 (m+1) ++ S 2::S 2::S 4::S 6::S 4::Z) (by rfl)
  have h4 := Reach.trans h (⟨_,h3⟩ : Reach base _ _)
  simpa only [P,Z,U,List.replicate_succ,List.cons_append,rep_cons,addRotate,Bool.false_eq_true,ite_false] using h4

#print axioms pair
#print axioms pairs
#print axioms depleteEven
end Raw14042Mixed
