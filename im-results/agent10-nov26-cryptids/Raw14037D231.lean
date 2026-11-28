import Raw14037WordReturn
namespace Raw14037D231
open BB6BlockFAR Raw140Orbit Raw140Extra
open Raw140Double (Reach)
open Raw140ERSuffix Raw140ERExit
open Raw14037DOdd (turn)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] boundary run

theorem seed (X : List Sym) :
    run base 207 (boundary 4 true (S 0::S 5::X) [S 2,S 3,S 1]) =
      some (boundary 4 true (S 1::S 3::S 3::S 5::S 5::X) (tailWord .t542)) := by
  exact Raw140Framed.execute_sound base true false 65 207
    ⟨4,true,[S 0,S 5],[S 2,S 3,S 1]⟩ ⟨4,true,[S 1,S 3,S 3,S 5,S 5],[S 5,S 4,S 2]⟩ X [] (by decide +kernel)

theorem convert (a k : Nat) :
    Reach base (boundary 3 false (U 6 (k+2) ++ [S 4]) (U 4 (a+1) ++ [S 2,S 3,S 1]))
      (boundary 4 false (U 6 (k+1) ++ [S 4])
        (U 1 (a+5) ++ trip115 ((turn (a+3) .t542).1) ++ tailWord (turn (a+3) .t542).2)) := by
  let X := U 6 (k+1) ++ [S 4]
  have h0 := Raw14037DTerm.frontAny a X [S 2,S 3,S 1]
  have h1 := seed (U 5 a ++ X)
  have h2 := Raw14037WordReturn.bankMany (a+2) 0 2 .t542 X
  have h3 := Raw14037WordReturn.rotateSweep (turn (a+2) .t542).1 (a+4) (turn (a+2) .t542).2 X
  have h2' : Reach base (boundary 4 true (S 1::S 3::S 3::(U 5 (a+2) ++ X)) (tailWord .t542))
      (boundary 4 true (S 1::(trip133 (turn (a+2) .t542).1 ++ U 3 (a+4) ++ X)) (tailWord (turn (a+2) .t542).2)) := by
    simpa only [Nat.zero_add,trip133,List.nil_append,U,List.replicate_succ,List.replicate_zero,List.cons_append,
      show 2+(a+2)=a+4 by omega] using h2
  have h := Reach.trans (Reach.trans (Reach.trans h0 ⟨_,h1⟩) h2') h3
  have hturn : ∀ (j : Nat) (s : Tail), turn (j+1) s = ((turn j s).1+extra (turn j s).2,rho (turn j s).2) := by
    intro j s
    induction j generalizing s with
    | zero => simp [turn]
    | succ j ih =>
      change (extra s+(turn (j+1) (rho s)).1,(turn (j+1) (rho s)).2) =
        (extra s+(turn j (rho s)).1+extra (turn j (rho s)).2,rho (turn j (rho s)).2)
      rw [ih]
      simp only [Nat.add_assoc]
  rw [hturn]
  exact h

theorem exitOnes (k m : Nat) (Y : List Sym) :
    Reach base (boundary 4 false (U 6 (k+1) ++ [S 4]) (U 1 (m+1) ++ Y))
      (boundary 0 true (U 3 (k+1) ++ [S 2]) (S 0::S 5::(U 1 m ++ Y))) := by
  let Z := U 1 m ++ Y
  have h0 := Raw140Framed.execute_sound base true true 3 11
    ⟨4,false,[S 6],[S 1]⟩ ⟨1,false,[],[S 1,S 5]⟩ (U 6 k ++ [S 4]) Z (by decide +kernel)
  have h1 := sweepL base 1 (S 6) (S 2) 3 k [S 4] (S 1::S 5::Z) (by rfl)
  have h2 := stepL base 1 1 true (S 4) (S 5) 5 [] (U 2 k ++ S 1::S 5::Z) (by rfl)
  have h3 := sweepR base 1 (S 2) (S 5) 3 k [S 5] (S 1::S 5::Z) (by rfl)
  have h4 := stepR base 1 3 false (S 1) (S 0) 1 (U 5 k ++ [S 5]) (S 5::Z) (by rfl)
  have h5 := sweepL base 3 (S 5) (S 4) 3 (k+1) [] (S 0::S 5::Z) (by rfl)
  have h6 := stepL base 3 0 true (S 0) (S 2) 3 [] (U 4 (k+1) ++ S 0::S 5::Z) (by rfl)
  have h7 := sweepR base 0 (S 4) (S 3) 3 (k+1) [S 2] (S 0::S 5::Z) (by rfl)
  simp only [Raw140Framed.prim,List.cons_append,List.nil_append,ite_true] at h0
  have h4' : Reach base (boundary 1 true (U 5 k ++ [S 5]) (S 1::S 5::Z))
      (boundary 3 false (U 5 (k+1)) (S 0::S 5::Z)) := by
    simpa only [U,List.replicate_succ',List.append_assoc,Bool.false_eq_true,ite_false] using (show Reach base _ _ from ⟨_,h4⟩)
  have h6' : Reach base (boundary 3 false [] (U 4 (k+1) ++ S 0::S 5::Z))
      (boundary 0 true [S 2] (U 4 (k+1) ++ S 0::S 5::Z)) := by
    exact ⟨_,by simpa only [Szero,left_zero,ite_true] using h6⟩
  simp only [List.append_nil] at h5
  have h := Reach.trans (Reach.trans (Reach.trans (Reach.trans (Reach.trans (Reach.trans (Reach.trans ⟨_,h0⟩ ⟨_,h1⟩) ⟨_,h2⟩) ⟨_,h3⟩) h4') ⟨_,h5⟩) h6') ⟨_,h7⟩
  simpa only [Z,U,List.replicate_succ,List.cons_append,List.append_assoc] using h

theorem ar05 (X Y : List Sym) :
    run base 12 (boundary 0 true (S 3::X) (S 0::S 5::Y)) =
      some (boundary 4 true (S 1::S 3::S 3::X) Y) := by
  exact Raw140Framed.execute_sound base true true 4 12
    ⟨0,true,[S 3],[S 0,S 5]⟩ ⟨4,true,[S 1,S 3,S 3],[]⟩ X Y (by decide +kernel)

theorem collect (p m n : Nat) (s : Tail) :
    Reach base (boundary 0 true (U 3 (p+1) ++ [S 2]) (S 0::S 5::(U 1 m ++ trip115 n ++ tailWord s)))
      (boundary 4 true (S 1::(trip133 n ++ U 3 (m+p+2) ++ [S 2])) (tailWord s)) := by
  let X := U 3 p ++ [S 2]
  have h0 := ar05 X (U 1 m ++ trip115 n ++ tailWord s)
  have h1 := Raw140ERSweep.many m (S 3::S 3::X) (trip115 n ++ tailWord s)
  have h2 := Raw14037SixBank.erMany n (U 3 (m+p+2) ++ [S 2]) (tailWord s)
  have h1' : Reach base (boundary 4 true (S 1::S 3::S 3::X) (U 1 m ++ trip115 n ++ tailWord s))
      (boundary 4 true (S 1::(U 3 (m+p+2) ++ [S 2])) (trip115 n ++ tailWord s)) := by
    simpa only [X,U,List.replicate_succ,List.cons_append,List.append_assoc,rep_cons,merge] using (show Reach base _ _ from ⟨_,h1⟩)
  rw [←List.append_assoc] at h2
  exact Reach.trans (Reach.trans ⟨_,h0⟩ h1') ⟨_,h2⟩

#print axioms convert
#print axioms exitOnes
#print axioms collect
end Raw14037D231
