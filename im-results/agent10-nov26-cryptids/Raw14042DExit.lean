import Raw14042DExitLocal
namespace Raw14042DExit
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw14042AWord Raw14042DMixed Raw14042DExitLocal
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

theorem dropFirst (W : List Bool) (X : List Sym) (s : AT) :
    Reach base (boundary 4 true (S 1::S 1::S 1::S 5::X) (w15 W ++ aw s))
      (boundary 4 true (S 1::X) (w15 (false::true::true::W ++ tr15 (ac s)) ++ aw (an s))) := by
  have h0 := Raw14042AWord.bounce W (S 1::S 1::S 5::X) s
  have h1 := drop115 X (w15 W ++ TA (ac s) ++ aw (an s))
  simpa only [w15,w15_append,w15_tr,Bool.false_eq_true,ite_false,ite_true,List.cons_append,List.append_assoc] using Reach.trans h0 ⟨_,h1⟩

theorem dropOne (W : List Bool) (X : List Sym) (s : AT) :
    Reach base (boundary 4 true (S 1::S 5::X) (w15 W ++ aw s))
      (boundary 4 true (S 1::X) (w15 (false::W ++ tr15 (ac s)) ++ aw (an s))) := by
  have h0 := Raw14042AWord.bounce W (S 5::X) s
  have h1 := stepL base 4 4 true (S 5) (S 1) 1 X (S 1::(w15 W ++ TA (ac s) ++ aw (an s))) (by rfl)
  simpa only [w15,w15_append,w15_tr,Bool.false_eq_true,ite_false,List.cons_append,List.append_assoc,ite_true] using Reach.trans h0 ⟨_,h1⟩

theorem dropMany (k : Nat) (W : List Bool) (X : List Sym) (s : AT) :
    Reach base (boundary 4 true (S 1::(U 5 k ++ X)) (w15 W ++ aw s))
      (boundary 4 true (S 1::X) (w15 (List.replicate k false ++ W ++ tr15 (Raw14042DMixed.turn k s).1) ++ aw (Raw14042DMixed.turn k s).2)) := by
  induction k generalizing W s with
  | zero => simpa [U,Raw14042DMixed.turn,tr15] using Reach.refl base (boundary 4 true (S 1::X) (w15 W ++ aw s))
  | succ k ih =>
    have h0 := dropOne W (U 5 k ++ X) s
    have h1 := ih (false::W ++ tr15 (ac s)) (an s)
    have h := Reach.trans h0 h1
    have e : List.replicate (k+1) false = List.replicate k false ++ [false] := by rw [List.replicate_succ']
    rw [e]
    simpa only [U,List.replicate_succ,List.cons_append,Raw14042DMixed.turn,← tr15_add,List.append_assoc,List.singleton_append,List.nil_append] using h

#print axioms dropFirst
#print axioms dropMany
end Raw14042DExit
