import Raw14042Mixed
namespace Raw14042MixedOdd
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw14042Counter Raw14042CounterLocal Raw14042Mixed
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

theorem depleteOdd (m : Nat) (W : List Bool) (s : Tail) :
    Reach base (P (m+1) [S 3,S 2] W s)
      (boundary 1 false [] (U 2 (m+4) ++ S 5::S 4::S 4::rotateWord (false::(W ++ trips (carry s))) (rho s))) := by
  let Z := rotateWord W s
  have h0 := scanFour (m+1) [S 7,S 3,S 2] W s
  have e : U 2 (m+1) ++ S 2::S 5::S 4::S 4::Z = S 2::S 2::(U 2 m ++ S 5::S 4::S 4::Z) := by
    simp only [U,List.replicate_succ,List.cons_append,rep_cons]
  change Reach base (P (m+1) [S 3,S 2] W s) (boundary 1 false [S 7,S 3,S 2] (U 2 (m+1) ++ S 2::S 5::S 4::S 4::Z)) at h0
  rw [e] at h0
  have h1 := finishStep [S 2] (U 2 m ++ S 5::S 4::S 4::Z)
  have h2 := scanFive (m+1) [S 7,S 2] (S 4::Z)
  rw [two_shift] at h2
  have h3 := finishZero (U 2 (m+1) ++ S 4::S 6::S 4::Z)
  have h4 := scanFour (m+2) [S 6] (false::(W ++ trips (carry s))) (rho s)
  have h5 : Reach base _ _ := Reach.trans (Reach.trans (Reach.trans (Reach.trans h0 ⟨_,h1⟩) h2) ⟨_,h3⟩) (by simpa only [← addRotate,Z,U,List.replicate_succ,List.cons_append] using h4)
  have h6 := stepL base 1 1 false (S 6) (S 2) 3 [] (U 2 (m+2) ++ S 2::S 5::S 4::S 4::rotateWord (false::(W ++ trips (carry s))) (rho s)) (by rfl)
  have h7 := Reach.trans h5 (⟨_,h6⟩ : Reach base _ _)
  simpa only [P,U,List.replicate_succ,List.cons_append,rep_cons,ite_true,Bool.false_eq_true,ite_false] using h7
#print axioms depleteOdd
end Raw14042MixedOdd
